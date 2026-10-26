import V185TrunkScan23Chunk0228

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1354298 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_1354298 : Nat := 118140960795 + 1354298 * 2 ^ 59
def prefixEnd_1354298 : Nat := 4983230072969 + 3 ^ 40 * 1354298 * 2
def baseEnd_1354298 : Nat := 77267313713649726282967

theorem tailTrace_1354298 : CollatzResearch.WordTrace tailWord_1354298 prefixEnd_1354298 77267313713649726282967 := by
  unfold tailWord_1354298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12348826511904279132279887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32930204031744744352746365 12348826511904279132279887)
  ·
    refine ⟨18523239767856418698419831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12348826511904279132279887 18523239767856418698419831)
    ·
      refine ⟨27784859651784628047629747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18523239767856418698419831 27784859651784628047629747)
      ·
        refine ⟨41677289477676942071444621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27784859651784628047629747 41677289477676942071444621)
        ·
          refine ⟨15628983554128853276791733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41677289477676942071444621 15628983554128853276791733)
          ·
            refine ⟨1465217208199579994699225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15628983554128853276791733 1465217208199579994699225)
            ·
              refine ⟨1098912906149684996024419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465217208199579994699225 1098912906149684996024419)
              ·
                refine ⟨1648369359224527494036629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098912906149684996024419 1648369359224527494036629)
                ·
                  refine ⟨77267313713649726282967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1648369359224527494036629 77267313713649726282967)
                  ·
                    rfl

theorem cell23_1354298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_1354298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354298 prefixEnd_1354298 := by exact prefixLift 1354298
  have htrace : WordTrace (prefixWord ++ tailWord_1354298) baseStart_1354298 baseEnd_1354298 := by
    simpa [prefixWord, tailWord_1354298, baseEnd_1354298] using wordTrace_append hprefix tailTrace_1354298
  have hstable : (prefixWord ++ tailWord_1354298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354298).length < 2 ^ (prefixWord ++ tailWord_1354298).sum := by decide
  have hdescent : baseEnd_1354298 < baseStart_1354298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354311 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1354311 : Nat := 118140960795 + 1354311 * 2 ^ 59
def prefixEnd_1354311 : Nat := 4983230072969 + 3 ^ 40 * 1354311 * 2
def baseEnd_1354311 : Nat := 231804166223785328561381

theorem tailTrace_1354311 : CollatzResearch.WordTrace tailWord_1354311 prefixEnd_1354311 231804166223785328561381 := by
  unfold tailWord_1354311
  simp only [CollatzResearch.WordTrace]
  refine ⟨49395780196570019749342787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32930520131046679832895191 49395780196570019749342787)
  ·
    refine ⟨74093670294855029624014181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49395780196570019749342787 74093670294855029624014181)
    ·
      refine ⟨13892563180285318054502659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74093670294855029624014181 13892563180285318054502659)
      ·
        refine ⟨20838844770427977081753989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892563180285318054502659 20838844770427977081753989)
        ·
          refine ⟨3907283394455245702828873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20838844770427977081753989 3907283394455245702828873)
          ·
            refine ⟨2930462545841434277121655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907283394455245702828873 2930462545841434277121655)
            ·
              refine ⟨4395693818762151415682483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930462545841434277121655 4395693818762151415682483)
              ·
                refine ⟨6593540728143227123523725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395693818762151415682483 6593540728143227123523725)
                ·
                  refine ⟨2472577773053710171321397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6593540728143227123523725 2472577773053710171321397)
                  ·
                    refine ⟨231804166223785328561381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2472577773053710171321397 231804166223785328561381)
                    ·
                      rfl

theorem cell23_1354311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1354311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354311 prefixEnd_1354311 := by exact prefixLift 1354311
  have htrace : WordTrace (prefixWord ++ tailWord_1354311) baseStart_1354311 baseEnd_1354311 := by
    simpa [prefixWord, tailWord_1354311, baseEnd_1354311] using wordTrace_append hprefix tailTrace_1354311
  have hstable : (prefixWord ++ tailWord_1354311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354311).length < 2 ^ (prefixWord ++ tailWord_1354311).sum := by decide
  have hdescent : baseEnd_1354311 < baseStart_1354311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354318 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_1354318 : Nat := 118140960795 + 1354318 * 2 ^ 59
def prefixEnd_1354318 : Nat := 4983230072969 + 3 ^ 40 * 1354318 * 2
def baseEnd_1354318 : Nat := 695416093035937458296611

theorem tailTrace_1354318 : CollatzResearch.WordTrace tailWord_1354318 prefixEnd_1354318 695416093035937458296611 := by
  unfold tailWord_1354318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174504438443082493105951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32930690338363106629898405 6174504438443082493105951)
  ·
    refine ⟨9261756657664623739658927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174504438443082493105951 9261756657664623739658927)
    ·
      refine ⟨13892634986496935609488391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9261756657664623739658927 13892634986496935609488391)
      ·
        refine ⟨20838952479745403414232587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892634986496935609488391 20838952479745403414232587)
        ·
          refine ⟨31258428719618105121348881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20838952479745403414232587 31258428719618105121348881)
          ·
            refine ⟨23443821539713578841011661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31258428719618105121348881 23443821539713578841011661)
            ·
              refine ⟨8791433077392592065379373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23443821539713578841011661 8791433077392592065379373)
              ·
                refine ⟨3296787404022222024517265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8791433077392592065379373 3296787404022222024517265)
                ·
                  refine ⟨2472590553016666518387949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296787404022222024517265 2472590553016666518387949)
                  ·
                    refine ⟨927221457381249944395481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472590553016666518387949 927221457381249944395481)
                    ·
                      refine ⟨695416093035937458296611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927221457381249944395481 695416093035937458296611)
                      ·
                        rfl

theorem cell23_1354318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_1354318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354318 prefixEnd_1354318 := by exact prefixLift 1354318
  have htrace : WordTrace (prefixWord ++ tailWord_1354318) baseStart_1354318 baseEnd_1354318 := by
    simpa [prefixWord, tailWord_1354318, baseEnd_1354318] using wordTrace_append hprefix tailTrace_1354318
  have hstable : (prefixWord ++ tailWord_1354318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354318).length < 2 ^ (prefixWord ++ tailWord_1354318).sum := by decide
  have hdescent : baseEnd_1354318 < baseStart_1354318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354351 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_1354351 : Nat := 118140960795 + 1354351 * 2 ^ 59
def prefixEnd_1354351 : Nat := 4983230072969 + 3 ^ 40 * 1354351 * 2
def baseEnd_1354351 : Nat := 695433037897535829183959

theorem tailTrace_1354351 : CollatzResearch.WordTrace tailWord_1354351 prefixEnd_1354351 695433037897535829183959 := by
  unfold tailWord_1354351
  simp only [CollatzResearch.WordTrace]
  refine ⟨49397239116425106580798907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32931492744283404387199271 49397239116425106580798907)
  ·
    refine ⟨74095858674637659871198361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49397239116425106580798907 74095858674637659871198361)
    ·
      refine ⟨55571894005978244903398771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74095858674637659871198361 55571894005978244903398771)
      ·
        refine ⟨83357841008967367355098157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55571894005978244903398771 83357841008967367355098157)
        ·
          refine ⟨31259190378362762758161809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83357841008967367355098157 31259190378362762758161809)
          ·
            refine ⟨23444392783772072068621357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31259190378362762758161809 23444392783772072068621357)
            ·
              refine ⟨8791647293914527025733009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23444392783772072068621357 8791647293914527025733009)
              ·
                refine ⟨6593735470435895269299757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791647293914527025733009 6593735470435895269299757)
                ·
                  refine ⟨2472650801413460725987409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6593735470435895269299757 2472650801413460725987409)
                  ·
                    refine ⟨1854488101060095544490557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2472650801413460725987409 1854488101060095544490557)
                    ·
                      refine ⟨695433037897535829183959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1854488101060095544490557 695433037897535829183959)
                      ·
                        rfl

theorem cell23_1354351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_1354351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354351 prefixEnd_1354351 := by exact prefixLift 1354351
  have htrace : WordTrace (prefixWord ++ tailWord_1354351) baseStart_1354351 baseEnd_1354351 := by
    simpa [prefixWord, tailWord_1354351, baseEnd_1354351] using wordTrace_append hprefix tailTrace_1354351
  have hstable : (prefixWord ++ tailWord_1354351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354351).length < 2 ^ (prefixWord ++ tailWord_1354351).sum := by decide
  have hdescent : baseEnd_1354351 < baseStart_1354351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354361 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1354361 : Nat := 118140960795 + 1354361 * 2 ^ 59
def prefixEnd_1354361 : Nat := 4983230072969 + 3 ^ 40 * 1354361 * 2
def baseEnd_1354361 : Nat := 695438172704080790058913

theorem tailTrace_1354361 : CollatzResearch.WordTrace tailWord_1354361 prefixEnd_1354361 695438172704080790058913 := by
  unfold tailWord_1354361
  simp only [CollatzResearch.WordTrace]
  refine ⟨49397603846388878288662937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32931735897592585525775291 49397603846388878288662937)
  ·
    refine ⟨37048202884791658716497203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49397603846388878288662937 37048202884791658716497203)
    ·
      refine ⟨55572304327187488074745805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37048202884791658716497203 55572304327187488074745805)
      ·
        refine ⟨20839614122695308028029677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55572304327187488074745805 20839614122695308028029677)
        ·
          refine ⟨7814855296010740510511129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20839614122695308028029677 7814855296010740510511129)
          ·
            refine ⟨5861141472008055382883347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7814855296010740510511129 5861141472008055382883347)
            ·
              refine ⟨8791712208012083074325021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861141472008055382883347 8791712208012083074325021)
              ·
                refine ⟨3296892078004531152871883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8791712208012083074325021 3296892078004531152871883)
                ·
                  refine ⟨4945338117006796729307825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296892078004531152871883 4945338117006796729307825)
                  ·
                    refine ⟨3709003587755097546980869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945338117006796729307825 3709003587755097546980869)
                    ·
                      refine ⟨695438172704080790058913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3709003587755097546980869 695438172704080790058913)
                      ·
                        rfl

theorem cell23_1354361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1354361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354361 prefixEnd_1354361 := by exact prefixLift 1354361
  have htrace : WordTrace (prefixWord ++ tailWord_1354361) baseStart_1354361 baseEnd_1354361 := by
    simpa [prefixWord, tailWord_1354361, baseEnd_1354361] using wordTrace_append hprefix tailTrace_1354361
  have hstable : (prefixWord ++ tailWord_1354361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354361).length < 2 ^ (prefixWord ++ tailWord_1354361).sum := by decide
  have hdescent : baseEnd_1354361 < baseStart_1354361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354422 : List Nat := [5, 1, 3, 1, 2, 2, 2, 7]
def baseStart_1354422 : Nat := 118140960795 + 1354422 * 2 ^ 59
def prefixEnd_1354422 : Nat := 4983230072969 + 3 ^ 40 * 1354422 * 2
def baseEnd_1354422 : Nat := 25758129445333520422079

theorem tailTrace_1354422 : CollatzResearch.WordTrace tailWord_1354422 prefixEnd_1354422 25758129445333520422079 := by
  unfold tailWord_1354422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087489293697992856664595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32933219132778590471089013 3087489293697992856664595)
  ·
    refine ⟨4631233940546989284996893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3087489293697992856664595 4631233940546989284996893)
    ·
      refine ⟨1736712727705120981873835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4631233940546989284996893 1736712727705120981873835)
      ·
        refine ⟨2605069091557681472810753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736712727705120981873835 2605069091557681472810753)
        ·
          refine ⟨1953801818668261104608065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605069091557681472810753 1953801818668261104608065)
          ·
            refine ⟨1465351364001195828456049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953801818668261104608065 1465351364001195828456049)
            ·
              refine ⟨1099013523000896871342037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465351364001195828456049 1099013523000896871342037)
              ·
                refine ⟨25758129445333520422079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1099013523000896871342037 25758129445333520422079)
                ·
                  rfl

theorem cell23_1354422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_1354422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354422 prefixEnd_1354422 := by exact prefixLift 1354422
  have htrace : WordTrace (prefixWord ++ tailWord_1354422) baseStart_1354422 baseEnd_1354422 := by
    simpa [prefixWord, tailWord_1354422, baseEnd_1354422] using wordTrace_append hprefix tailTrace_1354422
  have hstable : (prefixWord ++ tailWord_1354422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354422).length < 2 ^ (prefixWord ++ tailWord_1354422).sum := by decide
  have hdescent : baseEnd_1354422 < baseStart_1354422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354433 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1354433 : Nat := 118140960795 + 1354433 * 2 ^ 59
def prefixEnd_1354433 : Nat := 4983230072969 + 3 ^ 40 * 1354433 * 2
def baseEnd_1354433 : Nat := 695475143311204508358583

theorem tailTrace_1354433 : CollatzResearch.WordTrace tailWord_1354433 prefixEnd_1354433 695475143311204508358583 := by
  unfold tailWord_1354433
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400229902128034585283953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32933486601418689723522635 49400229902128034585283953)
  ·
    refine ⟨37050172426596025938962965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49400229902128034585283953 37050172426596025938962965)
    ·
      refine ⟨1736726832496688715888889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37050172426596025938962965 1736726832496688715888889)
      ·
        refine ⟨1302545124372516536916667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736726832496688715888889 1302545124372516536916667)
        ·
          refine ⟨1953817686558774805375001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302545124372516536916667 1953817686558774805375001)
          ·
            refine ⟨1465363264919081104031251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953817686558774805375001 1465363264919081104031251)
            ·
              refine ⟨2198044897378621656046877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465363264919081104031251 2198044897378621656046877)
              ·
                refine ⟨824266836516983121017579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198044897378621656046877 824266836516983121017579)
                ·
                  refine ⟨1236400254775474681526369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824266836516983121017579 1236400254775474681526369)
                  ·
                    refine ⟨927300191081606011144777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236400254775474681526369 927300191081606011144777)
                    ·
                      refine ⟨695475143311204508358583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927300191081606011144777 695475143311204508358583)
                      ·
                        rfl

theorem cell23_1354433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1354433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354433 prefixEnd_1354433 := by exact prefixLift 1354433
  have htrace : WordTrace (prefixWord ++ tailWord_1354433) baseStart_1354433 baseEnd_1354433 := by
    simpa [prefixWord, tailWord_1354433, baseEnd_1354433] using wordTrace_append hprefix tailTrace_1354433
  have hstable : (prefixWord ++ tailWord_1354433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354433).length < 2 ^ (prefixWord ++ tailWord_1354433).sum := by decide
  have hdescent : baseEnd_1354433 < baseStart_1354433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354455 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_1354455 : Nat := 118140960795 + 1354455 * 2 ^ 59
def prefixEnd_1354455 : Nat := 4983230072969 + 3 ^ 40 * 1354455 * 2
def baseEnd_1354455 : Nat := 695486439885603422283481

theorem tailTrace_1354455 : CollatzResearch.WordTrace tailWord_1354455 prefixEnd_1354455 695486439885603422283481 := by
  unfold tailWord_1354455
  simp only [CollatzResearch.WordTrace]
  refine ⟨49401032308048332342584819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32934021538698888228389879 49401032308048332342584819)
  ·
    refine ⟨74101548462072498513877229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49401032308048332342584819 74101548462072498513877229)
    ·
      refine ⟨27788080673277186942703961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74101548462072498513877229 27788080673277186942703961)
      ·
        refine ⟨20841060504957890207027971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27788080673277186942703961 20841060504957890207027971)
        ·
          refine ⟨31261590757436835310541957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20841060504957890207027971 31261590757436835310541957)
          ·
            refine ⟨5861548267019406620726617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31261590757436835310541957 5861548267019406620726617)
            ·
              refine ⟨4396161200264554965544963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861548267019406620726617 4396161200264554965544963)
              ·
                refine ⟨6594241800396832448317445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396161200264554965544963 6594241800396832448317445)
                ·
                  refine ⟨1236420337574406084059521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6594241800396832448317445 1236420337574406084059521)
                  ·
                    refine ⟨927315253180804563044641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236420337574406084059521 927315253180804563044641)
                    ·
                      refine ⟨695486439885603422283481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927315253180804563044641 695486439885603422283481)
                      ·
                        rfl

theorem cell23_1354455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_1354455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354455 prefixEnd_1354455 := by exact prefixLift 1354455
  have htrace : WordTrace (prefixWord ++ tailWord_1354455) baseStart_1354455 baseEnd_1354455 := by
    simpa [prefixWord, tailWord_1354455, baseEnd_1354455] using wordTrace_append hprefix tailTrace_1354455
  have hstable : (prefixWord ++ tailWord_1354455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354455).length < 2 ^ (prefixWord ++ tailWord_1354455).sum := by decide
  have hdescent : baseEnd_1354455 < baseStart_1354455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354542 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1354542 : Nat := 118140960795 + 1354542 * 2 ^ 59
def prefixEnd_1354542 : Nat := 4983230072969 + 3 ^ 40 * 1354542 * 2
def baseEnd_1354542 : Nat := 231843704234181527298527

theorem tailTrace_1354542 : CollatzResearch.WordTrace tailWord_1354542 prefixEnd_1354542 231843704234181527298527 := by
  unfold tailWord_1354542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175525682341643275125235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32936136972488764134001253 6175525682341643275125235)
  ·
    refine ⟨9263288523512464912687853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6175525682341643275125235 9263288523512464912687853)
    ·
      refine ⟨3473733196317174342257945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9263288523512464912687853 3473733196317174342257945)
      ·
        refine ⟨2605299897237880756693459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3473733196317174342257945 2605299897237880756693459)
        ·
          refine ⟨3907949845856821135040189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605299897237880756693459 3907949845856821135040189)
          ·
            refine ⟨1465481192196307925640071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3907949845856821135040189 1465481192196307925640071)
            ·
              refine ⟨2198221788294461888460107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465481192196307925640071 2198221788294461888460107)
              ·
                refine ⟨3297332682441692832690161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198221788294461888460107 3297332682441692832690161)
                ·
                  refine ⟨2472999511831269624517621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297332682441692832690161 2472999511831269624517621)
                  ·
                    refine ⟨231843704234181527298527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2472999511831269624517621 231843704234181527298527)
                    ·
                      rfl

theorem cell23_1354542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1354542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354542 prefixEnd_1354542 := by exact prefixLift 1354542
  have htrace : WordTrace (prefixWord ++ tailWord_1354542) baseStart_1354542 baseEnd_1354542 := by
    simpa [prefixWord, tailWord_1354542, baseEnd_1354542] using wordTrace_append hprefix tailTrace_1354542
  have hstable : (prefixWord ++ tailWord_1354542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354542).length < 2 ^ (prefixWord ++ tailWord_1354542).sum := by decide
  have hdescent : baseEnd_1354542 < baseStart_1354542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354551 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 8]
def baseStart_1354551 : Nat := 118140960795 + 1354551 * 2 ^ 59
def prefixEnd_1354551 : Nat := 4983230072969 + 3 ^ 40 * 1354551 * 2
def baseEnd_1354551 : Nat := 77281748225381671853671

theorem tailTrace_1354551 : CollatzResearch.WordTrace tailWord_1354551 prefixEnd_1354551 77281748225381671853671 := by
  unfold tailWord_1354551
  simp only [CollatzResearch.WordTrace]
  refine ⟨49404533715700540738079507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32936355810467027158719671 49404533715700540738079507)
  ·
    refine ⟨74106800573550811107119261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49404533715700540738079507 74106800573550811107119261)
    ·
      refine ⟨27790050215081554165169723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74106800573550811107119261 27790050215081554165169723)
      ·
        refine ⟨41685075322622331247754585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27790050215081554165169723 41685075322622331247754585)
        ·
          refine ⟨31263806491966748435815939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41685075322622331247754585 31263806491966748435815939)
          ·
            refine ⟨46895709737950122653723909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31263806491966748435815939 46895709737950122653723909)
            ·
              refine ⟨8792945575865647997573233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46895709737950122653723909 8792945575865647997573233)
              ·
                refine ⟨6594709181899235998179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792945575865647997573233 6594709181899235998179925)
                ·
                  refine ⟨77281748225381671853671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6594709181899235998179925 77281748225381671853671)
                  ·
                    rfl

theorem cell23_1354551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 8].length) (baseStart_1354551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354551 prefixEnd_1354551 := by exact prefixLift 1354551
  have htrace : WordTrace (prefixWord ++ tailWord_1354551) baseStart_1354551 baseEnd_1354551 := by
    simpa [prefixWord, tailWord_1354551, baseEnd_1354551] using wordTrace_append hprefix tailTrace_1354551
  have hstable : (prefixWord ++ tailWord_1354551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354551).length < 2 ^ (prefixWord ++ tailWord_1354551).sum := by decide
  have hdescent : baseEnd_1354551 < baseStart_1354551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354572 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_1354572 : Nat := 118140960795 + 1354572 * 2 ^ 59
def prefixEnd_1354572 : Nat := 4983230072969 + 3 ^ 40 * 1354572 * 2
def baseEnd_1354572 : Nat := 231848839040726488173481

theorem tailTrace_1354572 : CollatzResearch.WordTrace tailWord_1354572 prefixEnd_1354572 231848839040726488173481 := by
  unfold tailWord_1354572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24702649824312230662296985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32936866432416307549729313 24702649824312230662296985)
  ·
    refine ⟨18526987368234172996722739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24702649824312230662296985 18526987368234172996722739)
    ·
      refine ⟨27790481052351259495084109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18526987368234172996722739 27790481052351259495084109)
      ·
        refine ⟨10421430394631722310656541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27790481052351259495084109 10421430394631722310656541)
        ·
          refine ⟨3908036397986895866496203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10421430394631722310656541 3908036397986895866496203)
          ·
            refine ⟨5862054596980343799744305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908036397986895866496203 5862054596980343799744305)
            ·
              refine ⟨4396540947735257849808229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862054596980343799744305 4396540947735257849808229)
              ·
                refine ⟨824351427700360846839043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396540947735257849808229 824351427700360846839043)
                ·
                  refine ⟨1236527141550541270258565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824351427700360846839043 1236527141550541270258565)
                  ·
                    refine ⟨231848839040726488173481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236527141550541270258565 231848839040726488173481)
                    ·
                      rfl

theorem cell23_1354572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_1354572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354572 prefixEnd_1354572 := by exact prefixLift 1354572
  have htrace : WordTrace (prefixWord ++ tailWord_1354572) baseStart_1354572 baseEnd_1354572 := by
    simpa [prefixWord, tailWord_1354572, baseEnd_1354572] using wordTrace_append hprefix tailTrace_1354572
  have hstable : (prefixWord ++ tailWord_1354572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354572).length < 2 ^ (prefixWord ++ tailWord_1354572).sum := by decide
  have hdescent : baseEnd_1354572 < baseStart_1354572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354585 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 6]
def baseStart_1354585 : Nat := 118140960795 + 1354585 * 2 ^ 59
def prefixEnd_1354585 : Nat := 4983230072969 + 3 ^ 40 * 1354585 * 2
def baseEnd_1354585 : Nat := 77283688041187545961987

theorem tailTrace_1354585 : CollatzResearch.WordTrace tailWord_1354585 prefixEnd_1354585 77283688041187545961987 := by
  unfold tailWord_1354585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49405773797577364544817209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32937182531718243029878139 49405773797577364544817209)
  ·
    refine ⟨37054330348183023408612907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49405773797577364544817209 37054330348183023408612907)
    ·
      refine ⟨55581495522274535112919361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37054330348183023408612907 55581495522274535112919361)
      ·
        refine ⟨41686121641705901334689521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55581495522274535112919361 41686121641705901334689521)
        ·
          refine ⟨31264591231279426001017141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41686121641705901334689521 31264591231279426001017141)
          ·
            refine ⟨2931055427932446187595357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31264591231279426001017141 2931055427932446187595357)
            ·
              refine ⟨1099145785474667320348259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2931055427932446187595357 1099145785474667320348259)
              ·
                refine ⟨1648718678212000980522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099145785474667320348259 1648718678212000980522389)
                ·
                  refine ⟨77283688041187545961987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1648718678212000980522389 77283688041187545961987)
                  ·
                    rfl

theorem cell23_1354585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_1354585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354585 prefixEnd_1354585 := by exact prefixLift 1354585
  have htrace : WordTrace (prefixWord ++ tailWord_1354585) baseStart_1354585 baseEnd_1354585 := by
    simpa [prefixWord, tailWord_1354585, baseEnd_1354585] using wordTrace_append hprefix tailTrace_1354585
  have hstable : (prefixWord ++ tailWord_1354585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354585).length < 2 ^ (prefixWord ++ tailWord_1354585).sum := by decide
  have hdescent : baseEnd_1354585 < baseStart_1354585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354606 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1354606 : Nat := 118140960795 + 1354606 * 2 ^ 59
def prefixEnd_1354606 : Nat := 4983230072969 + 3 ^ 40 * 1354606 * 2
def baseEnd_1354606 : Nat := 231854658488144110498429

theorem tailTrace_1354606 : CollatzResearch.WordTrace tailWord_1354606 prefixEnd_1354606 231854658488144110498429 := by
  unfold tailWord_1354606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175817466312660641416459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32937693153667523420887781 6175817466312660641416459)
  ·
    refine ⟨9263726199468990962124689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6175817466312660641416459 9263726199468990962124689)
    ·
      refine ⟨6947794649601743221593517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9263726199468990962124689 6947794649601743221593517)
      ·
        refine ⟨2605422993600653708097569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6947794649601743221593517 2605422993600653708097569)
        ·
          refine ⟨1954067245200490281073177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605422993600653708097569 1954067245200490281073177)
          ·
            refine ⟨1465550433900367710804883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954067245200490281073177 1465550433900367710804883)
            ·
              refine ⟨2198325650850551566207325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465550433900367710804883 2198325650850551566207325)
              ·
                refine ⟨824372119068956837327747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198325650850551566207325 824372119068956837327747)
                ·
                  refine ⟨1236558178603435255991621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824372119068956837327747 1236558178603435255991621)
                  ·
                    refine ⟨231854658488144110498429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236558178603435255991621 231854658488144110498429)
                    ·
                      rfl

theorem cell23_1354606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1354606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354606 prefixEnd_1354606 := by exact prefixLift 1354606
  have htrace : WordTrace (prefixWord ++ tailWord_1354606) baseStart_1354606 baseEnd_1354606 := by
    simpa [prefixWord, tailWord_1354606, baseEnd_1354606] using wordTrace_append hprefix tailTrace_1354606
  have hstable : (prefixWord ++ tailWord_1354606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354606).length < 2 ^ (prefixWord ++ tailWord_1354606).sum := by decide
  have hdescent : baseEnd_1354606 < baseStart_1354606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354618 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1354618 : Nat := 118140960795 + 1354618 * 2 ^ 59
def prefixEnd_1354618 : Nat := 4983230072969 + 3 ^ 40 * 1354618 * 2
def baseEnd_1354618 : Nat := 695570137232286284545231

theorem tailTrace_1354618 : CollatzResearch.WordTrace tailWord_1354618 prefixEnd_1354618 695570137232286284545231 := by
  unfold tailWord_1354618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351744351614452795192127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32937984937638540787179005 12351744351614452795192127)
  ·
    refine ⟨18527616527421679192788191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12351744351614452795192127 18527616527421679192788191)
    ·
      refine ⟨27791424791132518789182287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18527616527421679192788191 27791424791132518789182287)
      ·
        refine ⟨41687137186698778183773431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27791424791132518789182287 41687137186698778183773431)
        ·
          refine ⟨62530705780048167275660147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41687137186698778183773431 62530705780048167275660147)
          ·
            refine ⟨93796058670072250913490221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62530705780048167275660147 93796058670072250913490221)
            ·
              refine ⟨35173522001277094092558833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93796058670072250913490221 35173522001277094092558833)
              ·
                refine ⟨26380141500957820569419125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35173522001277094092558833 26380141500957820569419125)
                ·
                  refine ⟨2473138265714795678383043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26380141500957820569419125 2473138265714795678383043)
                  ·
                    refine ⟨3709707398572193517574565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473138265714795678383043 3709707398572193517574565)
                    ·
                      refine ⟨695570137232286284545231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3709707398572193517574565 695570137232286284545231)
                      ·
                        rfl

theorem cell23_1354618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1354618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354618 prefixEnd_1354618 := by exact prefixLift 1354618
  have htrace : WordTrace (prefixWord ++ tailWord_1354618) baseStart_1354618 baseEnd_1354618 := by
    simpa [prefixWord, tailWord_1354618, baseEnd_1354618] using wordTrace_append hprefix tailTrace_1354618
  have hstable : (prefixWord ++ tailWord_1354618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354618).length < 2 ^ (prefixWord ++ tailWord_1354618).sum := by decide
  have hdescent : baseEnd_1354618 < baseStart_1354618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354652 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1354652 : Nat := 118140960795 + 1354652 * 2 ^ 59
def prefixEnd_1354652 : Nat := 4983230072969 + 3 ^ 40 * 1354652 * 2
def baseEnd_1354652 : Nat := 695587595574539151520075

theorem tailTrace_1354652 : CollatzResearch.WordTrace tailWord_1354652 prefixEnd_1354652 695587595574539151520075 := by
  unfold tailWord_1354652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24704108744167317493753105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32938811658889756658337473 24704108744167317493753105)
  ·
    refine ⟨18528081558125488120314829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24704108744167317493753105 18528081558125488120314829)
    ·
      refine ⟨6948030584297058045118061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18528081558125488120314829 6948030584297058045118061)
      ·
        refine ⟨2605511469111396766919273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6948030584297058045118061 2605511469111396766919273)
        ·
          refine ⟨1954133601833547575189455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605511469111396766919273 1954133601833547575189455)
          ·
            refine ⟨2931200402750321362784183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954133601833547575189455 2931200402750321362784183)
            ·
              refine ⟨4396800604125482044176275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931200402750321362784183 4396800604125482044176275)
              ·
                refine ⟨6595200906188223066264413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396800604125482044176275 6595200906188223066264413)
                ·
                  refine ⟨2473200339820583649849155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6595200906188223066264413 2473200339820583649849155)
                  ·
                    refine ⟨3709800509730875474773733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473200339820583649849155 3709800509730875474773733)
                    ·
                      refine ⟨695587595574539151520075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3709800509730875474773733 695587595574539151520075)
                      ·
                        rfl

theorem cell23_1354652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1354652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354652 prefixEnd_1354652 := by exact prefixLift 1354652
  have htrace : WordTrace (prefixWord ++ tailWord_1354652) baseStart_1354652 baseEnd_1354652 := by
    simpa [prefixWord, tailWord_1354652, baseEnd_1354652] using wordTrace_append hprefix tailTrace_1354652
  have hstable : (prefixWord ++ tailWord_1354652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354652).length < 2 ^ (prefixWord ++ tailWord_1354652).sum := by decide
  have hdescent : baseEnd_1354652 < baseStart_1354652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354686 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_1354686 : Nat := 118140960795 + 1354686 * 2 ^ 59
def prefixEnd_1354686 : Nat := 4983230072969 + 3 ^ 40 * 1354686 * 2
def baseEnd_1354686 : Nat := 695605053916792018494919

theorem tailTrace_1354686 : CollatzResearch.WordTrace tailWord_1354686 prefixEnd_1354686 695605053916792018494919 := by
  unfold tailWord_1354686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176182196276432349280489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32939638380140972529495941 6176182196276432349280489)
  ·
    refine ⟨4632136647207324261960367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6176182196276432349280489 4632136647207324261960367)
    ·
      refine ⟨6948204970810986392940551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4632136647207324261960367 6948204970810986392940551)
      ·
        refine ⟨10422307456216479589410827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948204970810986392940551 10422307456216479589410827)
        ·
          refine ⟨15633461184324719384116241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10422307456216479589410827 15633461184324719384116241)
          ·
            refine ⟨11725095888243539538087181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15633461184324719384116241 11725095888243539538087181)
            ·
              refine ⟨4396910958091327326782693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11725095888243539538087181 4396910958091327326782693)
              ·
                refine ⟨824420804642123873771755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396910958091327326782693 824420804642123873771755)
                ·
                  refine ⟨1236631206963185810657633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824420804642123873771755 1236631206963185810657633)
                  ·
                    refine ⟨927473405222389357993225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236631206963185810657633 927473405222389357993225)
                    ·
                      refine ⟨695605053916792018494919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927473405222389357993225 695605053916792018494919)
                      ·
                        rfl

theorem cell23_1354686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_1354686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354686 prefixEnd_1354686 := by exact prefixLift 1354686
  have htrace : WordTrace (prefixWord ++ tailWord_1354686) baseStart_1354686 baseEnd_1354686 := by
    simpa [prefixWord, tailWord_1354686, baseEnd_1354686] using wordTrace_append hprefix tailTrace_1354686
  have hstable : (prefixWord ++ tailWord_1354686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354686).length < 2 ^ (prefixWord ++ tailWord_1354686).sum := by decide
  have hdescent : baseEnd_1354686 < baseStart_1354686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354688 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_1354688 : Nat := 118140960795 + 1354688 * 2 ^ 59
def prefixEnd_1354688 : Nat := 4983230072969 + 3 ^ 40 * 1354688 * 2
def baseEnd_1354688 : Nat := 231868693626033670223303

theorem tailTrace_1354688 : CollatzResearch.WordTrace tailWord_1354688 prefixEnd_1354688 231868693626033670223303 := by
  unfold tailWord_1354688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24704765258102106567908359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32939687010802808757211145 24704765258102106567908359)
  ·
    refine ⟨37057147887153159851862539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24704765258102106567908359 37057147887153159851862539)
    ·
      refine ⟨55585721830729739777793809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37057147887153159851862539 55585721830729739777793809)
      ·
        refine ⟨41689291373047304833345357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55585721830729739777793809 41689291373047304833345357)
        ·
          refine ⟨15633484264892739312504509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41689291373047304833345357 15633484264892739312504509)
          ·
            refine ⟨5862556599334777242189191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15633484264892739312504509 5862556599334777242189191)
            ·
              refine ⟨8793834899002165863283787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862556599334777242189191 8793834899002165863283787)
              ·
                refine ⟨13190752348503248794925681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8793834899002165863283787 13190752348503248794925681)
                ·
                  refine ⟨9893064261377436596194261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13190752348503248794925681 9893064261377436596194261)
                  ·
                    refine ⟨231868693626033670223303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9893064261377436596194261 231868693626033670223303)
                    ·
                      rfl

theorem cell23_1354688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_1354688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354688 prefixEnd_1354688 := by exact prefixLift 1354688
  have htrace : WordTrace (prefixWord ++ tailWord_1354688) baseStart_1354688 baseEnd_1354688 := by
    simpa [prefixWord, tailWord_1354688, baseEnd_1354688] using wordTrace_append hprefix tailTrace_1354688
  have hstable : (prefixWord ++ tailWord_1354688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354688).length < 2 ^ (prefixWord ++ tailWord_1354688).sum := by decide
  have hdescent : baseEnd_1354688 < baseStart_1354688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354698 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1354698 : Nat := 118140960795 + 1354698 * 2 ^ 59
def prefixEnd_1354698 : Nat := 4983230072969 + 3 ^ 40 * 1354698 * 2
def baseEnd_1354698 : Nat := 695611215684645971544863

theorem tailTrace_1354698 : CollatzResearch.WordTrace tailWord_1354698 prefixEnd_1354698 695611215684645971544863 := by
  unfold tailWord_1354698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12352473811541996210920187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32939930164111989895787165 12352473811541996210920187)
  ·
    refine ⟨18528710717312994316380281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12352473811541996210920187 18528710717312994316380281)
    ·
      refine ⟨13896533037984745737285211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18528710717312994316380281 13896533037984745737285211)
      ·
        refine ⟨20844799556977118605927817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896533037984745737285211 20844799556977118605927817)
        ·
          refine ⟨15633599667732838954445863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20844799556977118605927817 15633599667732838954445863)
          ·
            refine ⟨23450399501599258431668795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15633599667732838954445863 23450399501599258431668795)
            ·
              refine ⟨35175599252398887647503193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23450399501599258431668795 35175599252398887647503193)
              ·
                refine ⟨26381699439299165735627395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35175599252398887647503193 26381699439299165735627395)
                ·
                  refine ⟨39572549158948748603441093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26381699439299165735627395 39572549158948748603441093)
                  ·
                    refine ⟨7419852967302890363145205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39572549158948748603441093 7419852967302890363145205)
                    ·
                      refine ⟨695611215684645971544863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7419852967302890363145205 695611215684645971544863)
                      ·
                        rfl

theorem cell23_1354698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1354698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354698 prefixEnd_1354698 := by exact prefixLift 1354698
  have htrace : WordTrace (prefixWord ++ tailWord_1354698) baseStart_1354698 baseEnd_1354698 := by
    simpa [prefixWord, tailWord_1354698, baseEnd_1354698] using wordTrace_append hprefix tailTrace_1354698
  have hstable : (prefixWord ++ tailWord_1354698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354698).length < 2 ^ (prefixWord ++ tailWord_1354698).sum := by decide
  have hdescent : baseEnd_1354698 < baseStart_1354698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354702 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1354702 : Nat := 118140960795 + 1354702 * 2 ^ 59
def prefixEnd_1354702 : Nat := 4983230072969 + 3 ^ 40 * 1354702 * 2
def baseEnd_1354702 : Nat := 695613269607263955894845

theorem tailTrace_1354702 : CollatzResearch.WordTrace tailWord_1354702 prefixEnd_1354702 695613269607263955894845 := by
  unfold tailWord_1354702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176255142269186690853295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32940027425435662351217573 6176255142269186690853295)
  ·
    refine ⟨9264382713403780036279943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6176255142269186690853295 9264382713403780036279943)
    ·
      refine ⟨13896574070105670054419915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264382713403780036279943 13896574070105670054419915)
      ·
        refine ⟨20844861105158505081629873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896574070105670054419915 20844861105158505081629873)
        ·
          refine ⟨15633645828868878811222405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20844861105158505081629873 15633645828868878811222405)
          ·
            refine ⟨2931308592912914777104201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15633645828868878811222405 2931308592912914777104201)
            ·
              refine ⟨2198481444684686082828151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931308592912914777104201 2198481444684686082828151)
              ·
                refine ⟨3297722167027029124242227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198481444684686082828151 3297722167027029124242227)
                ·
                  refine ⟨4946583250540543686363341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297722167027029124242227 4946583250540543686363341)
                  ·
                    refine ⟨1854968718952703882386253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4946583250540543686363341 1854968718952703882386253)
                    ·
                      refine ⟨695613269607263955894845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1854968718952703882386253 695613269607263955894845)
                      ·
                        rfl

theorem cell23_1354702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1354702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354702 prefixEnd_1354702 := by exact prefixLift 1354702
  have htrace : WordTrace (prefixWord ++ tailWord_1354702) baseStart_1354702 baseEnd_1354702 := by
    simpa [prefixWord, tailWord_1354702, baseEnd_1354702] using wordTrace_append hprefix tailTrace_1354702
  have hstable : (prefixWord ++ tailWord_1354702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354702).length < 2 ^ (prefixWord ++ tailWord_1354702).sum := by decide
  have hdescent : baseEnd_1354702 < baseStart_1354702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354712 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_1354712 : Nat := 118140960795 + 1354712 * 2 ^ 59
def prefixEnd_1354712 : Nat := 4983230072969 + 3 ^ 40 * 1354712 * 2
def baseEnd_1354712 : Nat := 695618404413808916769799

theorem tailTrace_1354712 : CollatzResearch.WordTrace tailWord_1354712 prefixEnd_1354712 695618404413808916769799 := by
  unfold tailWord_1354712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24705202934058632617345195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32940270578744843489793593 24705202934058632617345195)
  ·
    refine ⟨37057804401087948926017793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24705202934058632617345195 37057804401087948926017793)
    ·
      refine ⟨27793353300815961694513345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37057804401087948926017793 27793353300815961694513345)
      ·
        refine ⟨20845014975611971270885009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27793353300815961694513345 20845014975611971270885009)
        ·
          refine ⟨15633761231708978453163757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20845014975611971270885009 15633761231708978453163757)
          ·
            refine ⟨5862660461890866919936409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15633761231708978453163757 5862660461890866919936409)
            ·
              refine ⟨4396995346418150189952307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862660461890866919936409 4396995346418150189952307)
              ·
                refine ⟨6595493019627225284928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396995346418150189952307 6595493019627225284928461)
                ·
                  refine ⟨2473309882360209481848173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6595493019627225284928461 2473309882360209481848173)
                  ·
                    refine ⟨927491205885078555693065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473309882360209481848173 927491205885078555693065)
                    ·
                      refine ⟨695618404413808916769799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927491205885078555693065 695618404413808916769799)
                      ·
                        rfl

theorem cell23_1354712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_1354712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354712 prefixEnd_1354712 := by exact prefixLift 1354712
  have htrace : WordTrace (prefixWord ++ tailWord_1354712) baseStart_1354712 baseEnd_1354712 := by
    simpa [prefixWord, tailWord_1354712, baseEnd_1354712] using wordTrace_append hprefix tailTrace_1354712
  have hstable : (prefixWord ++ tailWord_1354712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354712).length < 2 ^ (prefixWord ++ tailWord_1354712).sum := by decide
  have hdescent : baseEnd_1354712 < baseStart_1354712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354795 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 2, 5]
def baseStart_1354795 : Nat := 118140960795 + 1354795 * 2 ^ 59
def prefixEnd_1354795 : Nat := 4983230072969 + 3 ^ 40 * 1354795 * 2
def baseEnd_1354795 : Nat := 231887007769377364010639

theorem tailTrace_1354795 : CollatzResearch.WordTrace tailWord_1354795 prefixEnd_1354795 231887007769377364010639 := by
  unfold tailWord_1354795
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413433126816570409961839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32942288751211046939974559 49413433126816570409961839)
  ·
    refine ⟨74120149690224855614942759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49413433126816570409961839 74120149690224855614942759)
    ·
      refine ⟨111180224535337283422414139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74120149690224855614942759 111180224535337283422414139)
      ·
        refine ⟨166770336803005925133621209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111180224535337283422414139 166770336803005925133621209)
        ·
          refine ⟨125077752602254443850215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166770336803005925133621209 125077752602254443850215907)
          ·
            refine ⟨187616628903381665775323861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125077752602254443850215907 187616628903381665775323861)
            ·
              refine ⟨4397264739923007791609153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 187616628903381665775323861 4397264739923007791609153)
              ·
                refine ⟨3297948554942255843706865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397264739923007791609153 3297948554942255843706865)
                ·
                  refine ⟨2473461416206691882780149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297948554942255843706865 2473461416206691882780149)
                  ·
                    refine ⟨231887007769377364010639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2473461416206691882780149 231887007769377364010639)
                    ·
                      rfl

theorem cell23_1354795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].length) (baseStart_1354795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354795 prefixEnd_1354795 := by exact prefixLift 1354795
  have htrace : WordTrace (prefixWord ++ tailWord_1354795) baseStart_1354795 baseEnd_1354795 := by
    simpa [prefixWord, tailWord_1354795, baseEnd_1354795] using wordTrace_append hprefix tailTrace_1354795
  have hstable : (prefixWord ++ tailWord_1354795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354795).length < 2 ^ (prefixWord ++ tailWord_1354795).sum := by decide
  have hdescent : baseEnd_1354795 < baseStart_1354795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354802 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_1354802 : Nat := 118140960795 + 1354802 * 2 ^ 59
def prefixEnd_1354802 : Nat := 4983230072969 + 3 ^ 40 * 1354802 * 2
def baseEnd_1354802 : Nat := 695664617672713564644385

theorem tailTrace_1354802 : CollatzResearch.WordTrace tailWord_1354802 prefixEnd_1354802 695664617672713564644385 := by
  unfold tailWord_1354802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353422109447802651366665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32942458958527473736977773 12353422109447802651366665)
  ·
    refine ⟨9265066582085851988524999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12353422109447802651366665 9265066582085851988524999)
    ·
      refine ⟨13897599873128777982787499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265066582085851988524999 13897599873128777982787499)
      ·
        refine ⟨20846399809693166974181249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13897599873128777982787499 20846399809693166974181249)
        ·
          refine ⟨15634799857269875230635937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20846399809693166974181249 15634799857269875230635937)
          ·
            refine ⟨11726099892952406422976953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15634799857269875230635937 11726099892952406422976953)
            ·
              refine ⟨8794574919714304817232715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11726099892952406422976953 8794574919714304817232715)
              ·
                refine ⟨13191862379571457225849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8794574919714304817232715 13191862379571457225849073)
                ·
                  refine ⟨9893896784678592919386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13191862379571457225849073 9893896784678592919386805)
                  ·
                    refine ⟨927552823563618086192513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9893896784678592919386805 927552823563618086192513)
                    ·
                      refine ⟨695664617672713564644385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927552823563618086192513 695664617672713564644385)
                      ·
                        rfl

theorem cell23_1354802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_1354802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354802 prefixEnd_1354802 := by exact prefixLift 1354802
  have htrace : WordTrace (prefixWord ++ tailWord_1354802) baseStart_1354802 baseEnd_1354802 := by
    simpa [prefixWord, tailWord_1354802, baseEnd_1354802] using wordTrace_append hprefix tailTrace_1354802
  have hstable : (prefixWord ++ tailWord_1354802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354802).length < 2 ^ (prefixWord ++ tailWord_1354802).sum := by decide
  have hdescent : baseEnd_1354802 < baseStart_1354802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354815 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_1354815 : Nat := 118140960795 + 1354815 * 2 ^ 59
def prefixEnd_1354815 : Nat := 4983230072969 + 3 ^ 40 * 1354815 * 2
def baseEnd_1354815 : Nat := 695671292921222013781825

theorem tailTrace_1354815 : CollatzResearch.WordTrace tailWord_1354815 prefixEnd_1354815 695671292921222013781825 := by
  unfold tailWord_1354815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49414162586744113825689899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32942775057829409217126599 49414162586744113825689899)
  ·
    refine ⟨74121243880116170738534849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49414162586744113825689899 74121243880116170738534849)
    ·
      refine ⟨55590932910087128053901137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74121243880116170738534849 55590932910087128053901137)
      ·
        refine ⟨41693199682565346040425853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55590932910087128053901137 41693199682565346040425853)
        ·
          refine ⟨15634949880962004765159695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41693199682565346040425853 15634949880962004765159695)
          ·
            refine ⟨23452424821443007147739543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15634949880962004765159695 23452424821443007147739543)
            ·
              refine ⟨35178637232164510721609315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23452424821443007147739543 35178637232164510721609315)
              ·
                refine ⟨52767955848246766082413973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35178637232164510721609315 52767955848246766082413973)
                ·
                  refine ⟨2473497930386567160113155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52767955848246766082413973 2473497930386567160113155)
                  ·
                    refine ⟨3710246895579850740169733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473497930386567160113155 3710246895579850740169733)
                    ·
                      refine ⟨695671292921222013781825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3710246895579850740169733 695671292921222013781825)
                      ·
                        rfl

theorem cell23_1354815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_1354815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354815 prefixEnd_1354815 := by exact prefixLift 1354815
  have htrace : WordTrace (prefixWord ++ tailWord_1354815) baseStart_1354815 baseEnd_1354815 := by
    simpa [prefixWord, tailWord_1354815, baseEnd_1354815] using wordTrace_append hprefix tailTrace_1354815
  have hstable : (prefixWord ++ tailWord_1354815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354815).length < 2 ^ (prefixWord ++ tailWord_1354815).sum := by decide
  have hdescent : baseEnd_1354815 < baseStart_1354815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354829 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1354829 : Nat := 118140960795 + 1354829 * 2 ^ 59
def prefixEnd_1354829 : Nat := 4983230072969 + 3 ^ 40 * 1354829 * 2
def baseEnd_1354829 : Nat := 231892827216794986335587

theorem tailTrace_1354829 : CollatzResearch.WordTrace tailWord_1354829 prefixEnd_1354829 231892827216794986335587 := by
  unfold tailWord_1354829
  simp only [CollatzResearch.WordTrace]
  refine ⟨49414673208693394216699541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32943115472462262811133027 49414673208693394216699541)
  ·
    refine ⟨2316312806657502853907791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49414673208693394216699541 2316312806657502853907791)
    ·
      refine ⟨3474469209986254280861687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2316312806657502853907791 3474469209986254280861687)
      ·
        refine ⟨5211703814979381421292531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474469209986254280861687 5211703814979381421292531)
        ·
          refine ⟨7817555722469072131938797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211703814979381421292531 7817555722469072131938797)
          ·
            refine ⟨2931583395925902049477049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7817555722469072131938797 2931583395925902049477049)
            ·
              refine ⟨2198687546944426537107787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931583395925902049477049 2198687546944426537107787)
              ·
                refine ⟨3298031320416639805661681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198687546944426537107787 3298031320416639805661681)
                ·
                  refine ⟨2473523490312479854246261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298031320416639805661681 2473523490312479854246261)
                  ·
                    refine ⟨231892827216794986335587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2473523490312479854246261 231892827216794986335587)
                    ·
                      rfl

theorem cell23_1354829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1354829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354829 prefixEnd_1354829 := by exact prefixLift 1354829
  have htrace : WordTrace (prefixWord ++ tailWord_1354829) baseStart_1354829 baseEnd_1354829 := by
    simpa [prefixWord, tailWord_1354829, baseEnd_1354829] using wordTrace_append hprefix tailTrace_1354829
  have hstable : (prefixWord ++ tailWord_1354829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354829).length < 2 ^ (prefixWord ++ tailWord_1354829).sum := by decide
  have hdescent : baseEnd_1354829 < baseStart_1354829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354846 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1354846 : Nat := 118140960795 + 1354846 * 2 ^ 59
def prefixEnd_1354846 : Nat := 4983230072969 + 3 ^ 40 * 1354846 * 2
def baseEnd_1354846 : Nat := 231895736940503797498061

theorem tailTrace_1354846 : CollatzResearch.WordTrace tailWord_1354846 prefixEnd_1354846 231895736940503797498061 := by
  unfold tailWord_1354846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176911656203975765008549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32943528833087870746712261 6176911656203975765008549)
  ·
    refine ⟨1158170935538245455939103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6176911656203975765008549 1158170935538245455939103)
    ·
      refine ⟨1737256403307368183908655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158170935538245455939103 1737256403307368183908655)
      ·
        refine ⟨2605884604961052275862983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737256403307368183908655 2605884604961052275862983)
        ·
          refine ⟨3908826907441578413794475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605884604961052275862983 3908826907441578413794475)
          ·
            refine ⟨5863240361162367620691713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908826907441578413794475 5863240361162367620691713)
            ·
              refine ⟨4397430270871775715518785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863240361162367620691713 4397430270871775715518785)
              ·
                refine ⟨3298072703153831786639089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397430270871775715518785 3298072703153831786639089)
                ·
                  refine ⟨2473554527365373839979317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298072703153831786639089 2473554527365373839979317)
                  ·
                    refine ⟨231895736940503797498061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2473554527365373839979317 231895736940503797498061)
                    ·
                      rfl

theorem cell23_1354846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1354846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354846 prefixEnd_1354846 := by exact prefixLift 1354846
  have htrace : WordTrace (prefixWord ++ tailWord_1354846) baseStart_1354846 baseEnd_1354846 := by
    simpa [prefixWord, tailWord_1354846, baseEnd_1354846] using wordTrace_append hprefix tailTrace_1354846
  have hstable : (prefixWord ++ tailWord_1354846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354846).length < 2 ^ (prefixWord ++ tailWord_1354846).sum := by decide
  have hdescent : baseEnd_1354846 < baseStart_1354846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354909 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_1354909 : Nat := 118140960795 + 1354909 * 2 ^ 59
def prefixEnd_1354909 : Nat := 4983230072969 + 3 ^ 40 * 1354909 * 2
def baseEnd_1354909 : Nat := 695719560102744646006393

theorem tailTrace_1354909 : CollatzResearch.WordTrace tailWord_1354909 prefixEnd_1354909 695719560102744646006393 := by
  unfold tailWord_1354909
  simp only [CollatzResearch.WordTrace]
  refine ⟨49417591048403567879611781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32945060698935711919741187 49417591048403567879611781)
  ·
    refine ⟨9265798321575668977427209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49417591048403567879611781 9265798321575668977427209)
    ·
      refine ⟨6949348741181751733070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9265798321575668977427209 6949348741181751733070407)
      ·
        refine ⟨10424023111772627599605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949348741181751733070407 10424023111772627599605611)
        ·
          refine ⟨15636034667658941399408417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424023111772627599605611 15636034667658941399408417)
          ·
            refine ⟨11727026000744206049556313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15636034667658941399408417 11727026000744206049556313)
            ·
              refine ⟨8795269500558154537167235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11727026000744206049556313 8795269500558154537167235)
              ·
                refine ⟨13192904250837231805750853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8795269500558154537167235 13192904250837231805750853)
                ·
                  refine ⟨2473669547031980963578285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13192904250837231805750853 2473669547031980963578285)
                  ·
                    refine ⟨927626080136992861341857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473669547031980963578285 927626080136992861341857)
                    ·
                      refine ⟨695719560102744646006393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927626080136992861341857 695719560102744646006393)
                      ·
                        rfl

theorem cell23_1354909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_1354909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354909 prefixEnd_1354909 := by exact prefixLift 1354909
  have htrace : WordTrace (prefixWord ++ tailWord_1354909) baseStart_1354909 baseEnd_1354909 := by
    simpa [prefixWord, tailWord_1354909, baseEnd_1354909] using wordTrace_append hprefix tailTrace_1354909
  have hstable : (prefixWord ++ tailWord_1354909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354909).length < 2 ^ (prefixWord ++ tailWord_1354909).sum := by decide
  have hdescent : baseEnd_1354909 < baseStart_1354909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354915 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 6]
def baseStart_1354915 : Nat := 118140960795 + 1354915 * 2 ^ 59
def prefixEnd_1354915 : Nat := 4983230072969 + 3 ^ 40 * 1354915 * 2
def baseEnd_1354915 : Nat := 231907546995557207510455

theorem tailTrace_1354915 : CollatzResearch.WordTrace tailWord_1354915 prefixEnd_1354915 231907546995557207510455 := by
  unfold tailWord_1354915
  simp only [CollatzResearch.WordTrace]
  refine ⟨49417809886381830904330199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32945206590921220602886799 49417809886381830904330199)
  ·
    refine ⟨74126714829572746356495299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49417809886381830904330199 74126714829572746356495299)
    ·
      refine ⟨111190072244359119534742949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74126714829572746356495299 111190072244359119534742949)
      ·
        refine ⟨20848138545817334912764303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111190072244359119534742949 20848138545817334912764303)
        ·
          refine ⟨31272207818726002369146455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20848138545817334912764303 31272207818726002369146455)
          ·
            refine ⟨46908311728089003553719683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31272207818726002369146455 46908311728089003553719683)
            ·
              refine ⟨70362467592133505330579525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46908311728089003553719683 70362467592133505330579525)
              ·
                refine ⟨13192962673525032249483661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70362467592133505330579525 13192962673525032249483661)
                ·
                  refine ⟨4947361002571887093556373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13192962673525032249483661 4947361002571887093556373)
                  ·
                    refine ⟨231907546995557207510455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4947361002571887093556373 231907546995557207510455)
                    ·
                      rfl

theorem cell23_1354915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_1354915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354915 prefixEnd_1354915 := by exact prefixLift 1354915
  have htrace : WordTrace (prefixWord ++ tailWord_1354915) baseStart_1354915 baseEnd_1354915 := by
    simpa [prefixWord, tailWord_1354915, baseEnd_1354915] using wordTrace_append hprefix tailTrace_1354915
  have hstable : (prefixWord ++ tailWord_1354915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354915).length < 2 ^ (prefixWord ++ tailWord_1354915).sum := by decide
  have hdescent : baseEnd_1354915 < baseStart_1354915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354916 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_1354916 : Nat := 118140960795 + 1354916 * 2 ^ 59
def prefixEnd_1354916 : Nat := 4983230072969 + 3 ^ 40 * 1354916 * 2
def baseEnd_1354916 : Nat := 695723154467326118618861

theorem tailTrace_1354916 : CollatzResearch.WordTrace tailWord_1354916 prefixEnd_1354916 695723154467326118618861 := by
  unfold tailWord_1354916
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708923179689104037558301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32945230906252138716744401 24708923179689104037558301)
  ·
    refine ⟨9265846192383414014084363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24708923179689104037558301 9265846192383414014084363)
    ·
      refine ⟨13898769288575121021126545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265846192383414014084363 13898769288575121021126545)
      ·
        refine ⟨10424076966431340765844909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13898769288575121021126545 10424076966431340765844909)
        ·
          refine ⟨3909028862411752787191841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10424076966431340765844909 3909028862411752787191841)
          ·
            refine ⟨2931771646808814590393881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909028862411752787191841 2931771646808814590393881)
            ·
              refine ⟨2198828735106610942795411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931771646808814590393881 2198828735106610942795411)
              ·
                refine ⟨3298243102659916414193117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198828735106610942795411 3298243102659916414193117)
                ·
                  refine ⟨1236841163497468655322419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3298243102659916414193117 1236841163497468655322419)
                  ·
                    refine ⟨1855261745246202982983629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1236841163497468655322419 1855261745246202982983629)
                    ·
                      refine ⟨695723154467326118618861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855261745246202982983629 695723154467326118618861)
                      ·
                        rfl

theorem cell23_1354916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_1354916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354916 prefixEnd_1354916 := by exact prefixLift 1354916
  have htrace : WordTrace (prefixWord ++ tailWord_1354916) baseStart_1354916 baseEnd_1354916 := by
    simpa [prefixWord, tailWord_1354916, baseEnd_1354916] using wordTrace_append hprefix tailTrace_1354916
  have hstable : (prefixWord ++ tailWord_1354916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354916).length < 2 ^ (prefixWord ++ tailWord_1354916).sum := by decide
  have hdescent : baseEnd_1354916 < baseStart_1354916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354939 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 5, 2, 2]
def baseStart_1354939 : Nat := 118140960795 + 1354939 * 2 ^ 59
def prefixEnd_1354939 : Nat := 4983230072969 + 3 ^ 40 * 1354939 * 2
def baseEnd_1354939 : Nat := 695734964522379528631255

theorem tailTrace_1354939 : CollatzResearch.WordTrace tailWord_1354939 prefixEnd_1354939 695734964522379528631255 := by
  unfold tailWord_1354939
  simp only [CollatzResearch.WordTrace]
  refine ⟨49418685238294883003203871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32945790158863255335469247 49418685238294883003203871)
  ·
    refine ⟨74128027857442324504805807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49418685238294883003203871 74128027857442324504805807)
    ·
      refine ⟨111192041786163486757208711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74128027857442324504805807 111192041786163486757208711)
      ·
        refine ⟨166788062679245230135813067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111192041786163486757208711 166788062679245230135813067)
        ·
          refine ⟨250182094018867845203719601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166788062679245230135813067 250182094018867845203719601)
          ·
            refine ⟨187636570514150883902789701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250182094018867845203719601 187636570514150883902789701)
            ·
              refine ⟨35181856971403290731773069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187636570514150883902789701 35181856971403290731773069)
              ·
                refine ⟨13193196364276234024414901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35181856971403290731773069 13193196364276234024414901)
                ·
                  refine ⟨1236862159150896939788897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13193196364276234024414901 1236862159150896939788897)
                  ·
                    refine ⟨927646619363172704841673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236862159150896939788897 927646619363172704841673)
                    ·
                      refine ⟨695734964522379528631255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927646619363172704841673 695734964522379528631255)
                      ·
                        rfl

theorem cell23_1354939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2, 2].length) (baseStart_1354939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354939 prefixEnd_1354939 := by exact prefixLift 1354939
  have htrace : WordTrace (prefixWord ++ tailWord_1354939) baseStart_1354939 baseEnd_1354939 := by
    simpa [prefixWord, tailWord_1354939, baseEnd_1354939] using wordTrace_append hprefix tailTrace_1354939
  have hstable : (prefixWord ++ tailWord_1354939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354939).length < 2 ^ (prefixWord ++ tailWord_1354939).sum := by decide
  have hdescent : baseEnd_1354939 < baseStart_1354939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354952 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1354952 : Nat := 118140960795 + 1354952 * 2 ^ 59
def prefixEnd_1354952 : Nat := 4983230072969 + 3 ^ 40 * 1354952 * 2
def baseEnd_1354952 : Nat := 695741639770887977768695

theorem tailTrace_1354952 : CollatzResearch.WordTrace tailWord_1354952 prefixEnd_1354952 695741639770887977768695 := by
  unfold tailWord_1354952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24709579693623893111713555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32946106258165190815618073 24709579693623893111713555)
  ·
    refine ⟨37064369540435839667570333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24709579693623893111713555 37064369540435839667570333)
    ·
      refine ⟨13899138577663439875338875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37064369540435839667570333 13899138577663439875338875)
      ·
        refine ⟨20848707866495159813008313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13899138577663439875338875 20848707866495159813008313)
        ·
          refine ⟨15636530899871369859756235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20848707866495159813008313 15636530899871369859756235)
          ·
            refine ⟨23454796349807054789634353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636530899871369859756235 23454796349807054789634353)
            ·
              refine ⟨17591097262355291092225765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23454796349807054789634353 17591097262355291092225765)
              ·
                refine ⟨3298330736691617079792331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17591097262355291092225765 3298330736691617079792331)
                ·
                  refine ⟨4947496105037425619688497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298330736691617079792331 4947496105037425619688497)
                  ·
                    refine ⟨3710622078778069214766373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947496105037425619688497 3710622078778069214766373)
                    ·
                      refine ⟨695741639770887977768695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3710622078778069214766373 695741639770887977768695)
                      ·
                        rfl

theorem cell23_1354952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1354952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354952 prefixEnd_1354952 := by exact prefixLift 1354952
  have htrace : WordTrace (prefixWord ++ tailWord_1354952) baseStart_1354952 baseEnd_1354952 := by
    simpa [prefixWord, tailWord_1354952, baseEnd_1354952] using wordTrace_append hprefix tailTrace_1354952
  have hstable : (prefixWord ++ tailWord_1354952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354952).length < 2 ^ (prefixWord ++ tailWord_1354952).sum := by decide
  have hdescent : baseEnd_1354952 < baseStart_1354952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_1354999 : Nat := 118140960795 + 1354999 * 2 ^ 59
def prefixEnd_1354999 : Nat := 4983230072969 + 3 ^ 40 * 1354999 * 2
def baseEnd_1354999 : Nat := 695765773361649293880979

theorem tailTrace_1354999 : CollatzResearch.WordTrace tailWord_1354999 prefixEnd_1354999 695765773361649293880979 := by
  unfold tailWord_1354999
  simp only [CollatzResearch.WordTrace]
  refine ⟨49420873618077513250388051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32947249078718342166925367 49420873618077513250388051)
  ·
    refine ⟨74131310427116269875582077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49420873618077513250388051 74131310427116269875582077)
    ·
      refine ⟨27799241410168601203343279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74131310427116269875582077 27799241410168601203343279)
      ·
        refine ⟨41698862115252901805014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27799241410168601203343279 41698862115252901805014919)
        ·
          refine ⟨62548293172879352707522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41698862115252901805014919 62548293172879352707522379)
          ·
            refine ⟨93822439759319029061283569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62548293172879352707522379 93822439759319029061283569)
            ·
              refine ⟨70366829819489271795962677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93822439759319029061283569 70366829819489271795962677)
              ·
                refine ⟨6596890295577119230871501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70366829819489271795962677 6596890295577119230871501)
                ·
                  refine ⟨2473833860841419711576813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6596890295577119230871501 2473833860841419711576813)
                  ·
                    refine ⟨927687697815532391841305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473833860841419711576813 927687697815532391841305)
                    ·
                      refine ⟨695765773361649293880979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927687697815532391841305 695765773361649293880979)
                      ·
                        rfl

theorem cell23_1354999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_1354999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354999 prefixEnd_1354999 := by exact prefixLift 1354999
  have htrace : WordTrace (prefixWord ++ tailWord_1354999) baseStart_1354999 baseEnd_1354999 := by
    simpa [prefixWord, tailWord_1354999, baseEnd_1354999] using wordTrace_append hprefix tailTrace_1354999
  have hstable : (prefixWord ++ tailWord_1354999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354999).length < 2 ^ (prefixWord ++ tailWord_1354999).sum := by decide
  have hdescent : baseEnd_1354999 < baseStart_1354999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355006 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1355006 : Nat := 118140960795 + 1355006 * 2 ^ 59
def prefixEnd_1355006 : Nat := 4983230072969 + 3 ^ 40 * 1355006 * 2
def baseEnd_1355006 : Nat := 695769367726230766493447

theorem tailTrace_1355006 : CollatzResearch.WordTrace tailWord_1355006 prefixEnd_1355006 695769367726230766493447 := by
  unfold tailWord_1355006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177641116131519180736609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32947419286034768963928581 6177641116131519180736609)
  ·
    refine ⟨4633230837098639385552457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6177641116131519180736609 4633230837098639385552457)
    ·
      refine ⟨3474923127823979539164343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4633230837098639385552457 3474923127823979539164343)
      ·
        refine ⟨5212384691735969308746515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474923127823979539164343 5212384691735969308746515)
        ·
          refine ⟨7818577037603953963119773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212384691735969308746515 7818577037603953963119773)
          ·
            refine ⟨2931966389101482736169915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7818577037603953963119773 2931966389101482736169915)
            ·
              refine ⟨4397949583652224104254873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931966389101482736169915 4397949583652224104254873)
              ·
                refine ⟨3298462187739168078191155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397949583652224104254873 3298462187739168078191155)
                ·
                  refine ⟨4947693281608752117286733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298462187739168078191155 4947693281608752117286733)
                  ·
                    refine ⟨1855384980603282043982525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4947693281608752117286733 1855384980603282043982525)
                    ·
                      refine ⟨695769367726230766493447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855384980603282043982525 695769367726230766493447)
                      ·
                        rfl

theorem cell23_1355006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1355006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355006 prefixEnd_1355006 := by exact prefixLift 1355006
  have htrace : WordTrace (prefixWord ++ tailWord_1355006) baseStart_1355006 baseEnd_1355006 := by
    simpa [prefixWord, tailWord_1355006, baseEnd_1355006] using wordTrace_append hprefix tailTrace_1355006
  have hstable : (prefixWord ++ tailWord_1355006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355006).length < 2 ^ (prefixWord ++ tailWord_1355006).sum := by decide
  have hdescent : baseEnd_1355006 < baseStart_1355006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355010 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1355010 : Nat := 118140960795 + 1355010 * 2 ^ 59
def prefixEnd_1355010 : Nat := 4983230072969 + 3 ^ 40 * 1355010 * 2
def baseEnd_1355010 : Nat := 695771421648848750843429

theorem tailTrace_1355010 : CollatzResearch.WordTrace tailWord_1355010 prefixEnd_1355010 695771421648848750843429 := by
  unfold tailWord_1355010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355318705259415532259621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32947516547358441419358989 12355318705259415532259621)
  ·
    refine ⟨2316622257236140412298679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12355318705259415532259621 2316622257236140412298679)
    ·
      refine ⟨3474933385854210618448019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2316622257236140412298679 3474933385854210618448019)
      ·
        refine ⟨5212400078781315927672029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474933385854210618448019 5212400078781315927672029)
        ·
          refine ⟨1954650029542993472877011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5212400078781315927672029 1954650029542993472877011)
          ·
            refine ⟨2931975044314490209315517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954650029542993472877011 2931975044314490209315517)
            ·
              refine ⟨1099490641617933828493319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2931975044314490209315517 1099490641617933828493319)
              ·
                refine ⟨1649235962426900742739979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099490641617933828493319 1649235962426900742739979)
                ·
                  refine ⟨2473853943640351114109969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649235962426900742739979 2473853943640351114109969)
                  ·
                    refine ⟨1855390457730263335582477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2473853943640351114109969 1855390457730263335582477)
                    ·
                      refine ⟨695771421648848750843429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855390457730263335582477 695771421648848750843429)
                      ·
                        rfl

theorem cell23_1355010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1355010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355010 prefixEnd_1355010 := by exact prefixLift 1355010
  have htrace : WordTrace (prefixWord ++ tailWord_1355010) baseStart_1355010 baseEnd_1355010 := by
    simpa [prefixWord, tailWord_1355010, baseEnd_1355010] using wordTrace_append hprefix tailTrace_1355010
  have hstable : (prefixWord ++ tailWord_1355010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355010).length < 2 ^ (prefixWord ++ tailWord_1355010).sum := by decide
  have hdescent : baseEnd_1355010 < baseStart_1355010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355029 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_1355029 : Nat := 118140960795 + 1355029 * 2 ^ 59
def prefixEnd_1355029 : Nat := 4983230072969 + 3 ^ 40 * 1355029 * 2
def baseEnd_1355029 : Nat := 695781177781284176505841

theorem tailTrace_1355029 : CollatzResearch.WordTrace tailWord_1355029 prefixEnd_1355029 695781177781284176505841 := by
  unfold tailWord_1355029
  simp only [CollatzResearch.WordTrace]
  refine ⟨49421967807968828373980141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32947978538645885582653427 49421967807968828373980141)
  ·
    refine ⟨18533237927988310640242553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49421967807968828373980141 18533237927988310640242553)
    ·
      refine ⟨13899928445991232980181915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18533237927988310640242553 13899928445991232980181915)
      ·
        refine ⟨20849892668986849470272873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13899928445991232980181915 20849892668986849470272873)
        ·
          refine ⟨15637419501740137102704655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20849892668986849470272873 15637419501740137102704655)
          ·
            refine ⟨23456129252610205654056983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15637419501740137102704655 23456129252610205654056983)
            ·
              refine ⟨35184193878915308481085475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23456129252610205654056983 35184193878915308481085475)
              ·
                refine ⟨52776290818372962721628213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35184193878915308481085475 52776290818372962721628213)
                ·
                  refine ⟨4947777264222465255152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52776290818372962721628213 4947777264222465255152645)
                  ·
                    refine ⟨927708237041712235341121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947777264222465255152645 927708237041712235341121)
                    ·
                      refine ⟨695781177781284176505841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927708237041712235341121 695781177781284176505841)
                      ·
                        rfl

theorem cell23_1355029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_1355029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355029 prefixEnd_1355029 := by exact prefixLift 1355029
  have htrace : WordTrace (prefixWord ++ tailWord_1355029) baseStart_1355029 baseEnd_1355029 := by
    simpa [prefixWord, tailWord_1355029, baseEnd_1355029] using wordTrace_append hprefix tailTrace_1355029
  have hstable : (prefixWord ++ tailWord_1355029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355029).length < 2 ^ (prefixWord ++ tailWord_1355029).sum := by decide
  have hdescent : baseEnd_1355029 < baseStart_1355029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355039 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 6]
def baseStart_1355039 : Nat := 118140960795 + 1355039 * 2 ^ 59
def prefixEnd_1355039 : Nat := 4983230072969 + 3 ^ 40 * 1355039 * 2
def baseEnd_1355039 : Nat := 231928770862609712460265

theorem tailTrace_1355039 : CollatzResearch.WordTrace tailWord_1355039 prefixEnd_1355039 231928770862609712460265 := by
  unfold tailWord_1355039
  simp only [CollatzResearch.WordTrace]
  refine ⟨49422332537932600081844171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32948221691955066721229447 49422332537932600081844171)
  ·
    refine ⟨74133498806898900122766257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49422332537932600081844171 74133498806898900122766257)
    ·
      refine ⟨55600124105174175092074693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74133498806898900122766257 55600124105174175092074693)
      ·
        refine ⟨10425023269720157829764005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55600124105174175092074693 10425023269720157829764005)
        ·
          refine ⟨1954691863072529593080751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10425023269720157829764005 1954691863072529593080751)
          ·
            refine ⟨2932037794608794389621127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954691863072529593080751 2932037794608794389621127)
            ·
              refine ⟨4398056691913191584431691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932037794608794389621127 4398056691913191584431691)
              ·
                refine ⟨6597085037869787376647537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398056691913191584431691 6597085037869787376647537)
                ·
                  refine ⟨4947813778402340532485653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597085037869787376647537 4947813778402340532485653)
                  ·
                    refine ⟨231928770862609712460265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4947813778402340532485653 231928770862609712460265)
                    ·
                      rfl

theorem cell23_1355039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_1355039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355039 prefixEnd_1355039 := by exact prefixLift 1355039
  have htrace : WordTrace (prefixWord ++ tailWord_1355039) baseStart_1355039 baseEnd_1355039 := by
    simpa [prefixWord, tailWord_1355039, baseEnd_1355039] using wordTrace_append hprefix tailTrace_1355039
  have hstable : (prefixWord ++ tailWord_1355039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355039).length < 2 ^ (prefixWord ++ tailWord_1355039).sum := by decide
  have hdescent : baseEnd_1355039 < baseStart_1355039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355076 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1355076 : Nat := 118140960795 + 1355076 * 2 ^ 59
def prefixEnd_1355076 : Nat := 4983230072969 + 3 ^ 40 * 1355076 * 2
def baseEnd_1355076 : Nat := 695805311372045492618125

theorem tailTrace_1355076 : CollatzResearch.WordTrace tailWord_1355076 prefixEnd_1355076 695805311372045492618125 := by
  unfold tailWord_1355076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711841019399277700470541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32949121359199036933960721 24711841019399277700470541)
  ·
    refine ⟨9266940382274729137676453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24711841019399277700470541 9266940382274729137676453)
    ·
      refine ⟨1737551321676511713314335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9266940382274729137676453 1737551321676511713314335)
      ·
        refine ⟨2606326982514767569971503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737551321676511713314335 2606326982514767569971503)
        ·
          refine ⟨3909490473772151354957255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606326982514767569971503 3909490473772151354957255)
          ·
            refine ⟨5864235710658227032435883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909490473772151354957255 5864235710658227032435883)
            ·
              refine ⟨8796353565987340548653825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864235710658227032435883 8796353565987340548653825)
              ·
                refine ⟨6597265174490505411490369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796353565987340548653825 6597265174490505411490369)
                ·
                  refine ⟨4947948880867879058617777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597265174490505411490369 4947948880867879058617777)
                  ·
                    refine ⟨3710961660650909293963333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947948880867879058617777 3710961660650909293963333)
                    ·
                      refine ⟨695805311372045492618125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3710961660650909293963333 695805311372045492618125)
                      ·
                        rfl

theorem cell23_1355076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1355076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355076 prefixEnd_1355076 := by exact prefixLift 1355076
  have htrace : WordTrace (prefixWord ++ tailWord_1355076) baseStart_1355076 baseEnd_1355076 := by
    simpa [prefixWord, tailWord_1355076, baseEnd_1355076] using wordTrace_append hprefix tailTrace_1355076
  have hstable : (prefixWord ++ tailWord_1355076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355076).length < 2 ^ (prefixWord ++ tailWord_1355076).sum := by decide
  have hdescent : baseEnd_1355076 < baseStart_1355076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355079 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1355079 : Nat := 118140960795 + 1355079 * 2 ^ 59
def prefixEnd_1355079 : Nat := 4983230072969 + 3 ^ 40 * 1355079 * 2
def baseEnd_1355079 : Nat := 695806851814008980880611

theorem tailTrace_1355079 : CollatzResearch.WordTrace tailWord_1355079 prefixEnd_1355079 695806851814008980880611 := by
  unfold tailWord_1355079
  simp only [CollatzResearch.WordTrace]
  refine ⟨49423791457787686913300291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32949194305191791275533527 49423791457787686913300291)
  ·
    refine ⟨74135687186681530369950437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49423791457787686913300291 74135687186681530369950437)
    ·
      refine ⟨13900441347502786944365707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74135687186681530369950437 13900441347502786944365707)
      ·
        refine ⟨20850662021254180416548561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900441347502786944365707 20850662021254180416548561)
        ·
          refine ⟨15637996515940635312411421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20850662021254180416548561 15637996515940635312411421)
          ·
            refine ⟨5864248693477738242154283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15637996515940635312411421 5864248693477738242154283)
            ·
              refine ⟨8796373040216607363231425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864248693477738242154283 8796373040216607363231425)
              ·
                refine ⟨6597279780162455522423569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796373040216607363231425 6597279780162455522423569)
                ·
                  refine ⟨4947959835121841641817677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597279780162455522423569 4947959835121841641817677)
                  ·
                    refine ⟨1855484938170690615681629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4947959835121841641817677 1855484938170690615681629)
                    ·
                      refine ⟨695806851814008980880611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855484938170690615681629 695806851814008980880611)
                      ·
                        rfl

theorem cell23_1355079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1355079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355079 prefixEnd_1355079 := by exact prefixLift 1355079
  have htrace : WordTrace (prefixWord ++ tailWord_1355079) baseStart_1355079 baseEnd_1355079 := by
    simpa [prefixWord, tailWord_1355079, baseEnd_1355079] using wordTrace_append hprefix tailTrace_1355079
  have hstable : (prefixWord ++ tailWord_1355079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355079).length < 2 ^ (prefixWord ++ tailWord_1355079).sum := by decide
  have hdescent : baseEnd_1355079 < baseStart_1355079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355119 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_1355119 : Nat := 118140960795 + 1355119 * 2 ^ 59
def prefixEnd_1355119 : Nat := 4983230072969 + 3 ^ 40 * 1355119 * 2
def baseEnd_1355119 : Nat := 695827391040188824380427

theorem tailTrace_1355119 : CollatzResearch.WordTrace tailWord_1355119 prefixEnd_1355119 695827391040188824380427 := by
  unfold tailWord_1355119
  simp only [CollatzResearch.WordTrace]
  refine ⟨49425250377642773744756411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32950166918428515829837607 49425250377642773744756411)
  ·
    refine ⟨74137875566464160617134617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49425250377642773744756411 74137875566464160617134617)
    ·
      refine ⟨55603406674848120462850963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74137875566464160617134617 55603406674848120462850963)
      ·
        refine ⟨83405110012272180694276445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55603406674848120462850963 83405110012272180694276445)
        ·
          refine ⟨31276916254602067760353667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83405110012272180694276445 31276916254602067760353667)
          ·
            refine ⟨46915374381903101640530501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31276916254602067760353667 46915374381903101640530501)
            ·
              refine ⟨8796632696606831557599469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46915374381903101640530501 8796632696606831557599469)
              ·
                refine ⟨3298737261227561834099801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8796632696606831557599469 3298737261227561834099801)
                ·
                  refine ⟨2474052945920671375574851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298737261227561834099801 2474052945920671375574851)
                  ·
                    refine ⟨3711079418881007063362277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474052945920671375574851 3711079418881007063362277)
                    ·
                      refine ⟨695827391040188824380427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3711079418881007063362277 695827391040188824380427)
                      ·
                        rfl

theorem cell23_1355119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_1355119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355119 prefixEnd_1355119 := by exact prefixLift 1355119
  have htrace : WordTrace (prefixWord ++ tailWord_1355119) baseStart_1355119 baseEnd_1355119 := by
    simpa [prefixWord, tailWord_1355119, baseEnd_1355119] using wordTrace_append hprefix tailTrace_1355119
  have hstable : (prefixWord ++ tailWord_1355119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355119).length < 2 ^ (prefixWord ++ tailWord_1355119).sum := by decide
  have hdescent : baseEnd_1355119 < baseStart_1355119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355129 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_1355129 : Nat := 118140960795 + 1355129 * 2 ^ 59
def prefixEnd_1355129 : Nat := 4983230072969 + 3 ^ 40 * 1355129 * 2
def baseEnd_1355129 : Nat := 231944175282244595085127

theorem tailTrace_1355129 : CollatzResearch.WordTrace tailWord_1355129 prefixEnd_1355129 231944175282244595085127 := by
  unfold tailWord_1355129
  simp only [CollatzResearch.WordTrace]
  refine ⟨49425615107606545452620441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32950410071737696968413627 49425615107606545452620441)
  ·
    refine ⟨37069211330704909089465331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49425615107606545452620441 37069211330704909089465331)
    ·
      refine ⟨55603816996057363634197997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37069211330704909089465331 55603816996057363634197997)
      ·
        refine ⟨20851431373521511362824249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55603816996057363634197997 20851431373521511362824249)
        ·
          refine ⟨15638573530141133522118187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20851431373521511362824249 15638573530141133522118187)
          ·
            refine ⟨23457860295211700283177281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15638573530141133522118187 23457860295211700283177281)
            ·
              refine ⟨17593395221408775212382961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23457860295211700283177281 17593395221408775212382961)
              ·
                refine ⟨13195046416056581409287221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17593395221408775212382961 13195046416056581409287221)
                ·
                  refine ⟨1237035601505304507120677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13195046416056581409287221 1237035601505304507120677)
                  ·
                    refine ⟨231944175282244595085127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237035601505304507120677 231944175282244595085127)
                    ·
                      rfl

theorem cell23_1355129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_1355129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355129 prefixEnd_1355129 := by exact prefixLift 1355129
  have htrace : WordTrace (prefixWord ++ tailWord_1355129) baseStart_1355129 baseEnd_1355129 := by
    simpa [prefixWord, tailWord_1355129, baseEnd_1355129] using wordTrace_append hprefix tailTrace_1355129
  have hstable : (prefixWord ++ tailWord_1355129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355129).length < 2 ^ (prefixWord ++ tailWord_1355129).sum := by decide
  have hdescent : baseEnd_1355129 < baseStart_1355129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355186 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1355186 : Nat := 118140960795 + 1355186 * 2 ^ 59
def prefixEnd_1355186 : Nat := 4983230072969 + 3 ^ 40 * 1355186 * 2
def baseEnd_1355186 : Nat := 695861794244040062242619

theorem tailTrace_1355186 : CollatzResearch.WordTrace tailWord_1355186 prefixEnd_1355186 695861794244040062242619 := by
  unfold tailWord_1355186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356923517100011046861353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32951796045600029458296941 12356923517100011046861353)
  ·
    refine ⟨9267692637825008285146015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12356923517100011046861353 9267692637825008285146015)
    ·
      refine ⟨13901538956737512427719023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9267692637825008285146015 13901538956737512427719023)
      ·
        refine ⟨20852308435106268641578535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13901538956737512427719023 20852308435106268641578535)
        ·
          refine ⟨31278462652659402962367803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20852308435106268641578535 31278462652659402962367803)
          ·
            refine ⟨46917693978989104443551705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31278462652659402962367803 46917693978989104443551705)
            ·
              refine ⟨35188270484241828332663779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46917693978989104443551705 35188270484241828332663779)
              ·
                refine ⟨52782405726362742498995669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35188270484241828332663779 52782405726362742498995669)
                ·
                  refine ⟨1237087634211626777320211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52782405726362742498995669 1237087634211626777320211)
                  ·
                    refine ⟨1855631451317440165980317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237087634211626777320211 1855631451317440165980317)
                    ·
                      refine ⟨695861794244040062242619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855631451317440165980317 695861794244040062242619)
                      ·
                        rfl

theorem cell23_1355186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1355186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355186 prefixEnd_1355186 := by exact prefixLift 1355186
  have htrace : WordTrace (prefixWord ++ tailWord_1355186) baseStart_1355186 baseEnd_1355186 := by
    simpa [prefixWord, tailWord_1355186, baseEnd_1355186] using wordTrace_append hprefix tailTrace_1355186
  have hstable : (prefixWord ++ tailWord_1355186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355186).length < 2 ^ (prefixWord ++ tailWord_1355186).sum := by decide
  have hdescent : baseEnd_1355186 < baseStart_1355186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355220 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1355220 : Nat := 118140960795 + 1355220 * 2 ^ 59
def prefixEnd_1355220 : Nat := 4983230072969 + 3 ^ 40 * 1355220 * 2
def baseEnd_1355220 : Nat := 695879252586292929217463

theorem tailTrace_1355220 : CollatzResearch.WordTrace tailWord_1355220 prefixEnd_1355220 695879252586292929217463 := by
  unfold tailWord_1355220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714467075138433997091557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32952622766851245329455409 24714467075138433997091557)
  ·
    refine ⟨4633962576588456374454667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24714467075138433997091557 4633962576588456374454667)
    ·
      refine ⟨6950943864882684561682001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633962576588456374454667 6950943864882684561682001)
      ·
        refine ⟨5213207898662013421261501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950943864882684561682001 5213207898662013421261501)
        ·
          refine ⟨1954952961998255032973063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5213207898662013421261501 1954952961998255032973063)
          ·
            refine ⟨2932429442997382549459595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954952961998255032973063 2932429442997382549459595)
            ·
              refine ⟨4398644164496073824189393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932429442997382549459595 4398644164496073824189393)
              ·
                refine ⟨3298983123372055368142045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398644164496073824189393 3298983123372055368142045)
                ·
                  refine ⟨1237118671264520763053267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3298983123372055368142045 1237118671264520763053267)
                  ·
                    refine ⟨1855678006896781144579901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237118671264520763053267 1855678006896781144579901)
                    ·
                      refine ⟨695879252586292929217463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855678006896781144579901 695879252586292929217463)
                      ·
                        rfl

theorem cell23_1355220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1355220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355220 prefixEnd_1355220 := by exact prefixLift 1355220
  have htrace : WordTrace (prefixWord ++ tailWord_1355220) baseStart_1355220 baseEnd_1355220 := by
    simpa [prefixWord, tailWord_1355220, baseEnd_1355220] using wordTrace_append hprefix tailTrace_1355220
  have hstable : (prefixWord ++ tailWord_1355220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355220).length < 2 ^ (prefixWord ++ tailWord_1355220).sum := by decide
  have hdescent : baseEnd_1355220 < baseStart_1355220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355226 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1355226 : Nat := 118140960795 + 1355226 * 2 ^ 59
def prefixEnd_1355226 : Nat := 4983230072969 + 3 ^ 40 * 1355226 * 2
def baseEnd_1355226 : Nat := 695882333470219905742435

theorem tailTrace_1355226 : CollatzResearch.WordTrace tailWord_1355226 prefixEnd_1355226 695882333470219905742435 := by
  unfold tailWord_1355226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357288247063782754725383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32952768658836754012601021 12357288247063782754725383)
  ·
    refine ⟨18535932370595674132088075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12357288247063782754725383 18535932370595674132088075)
    ·
      refine ⟨27803898555893511198132113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535932370595674132088075 27803898555893511198132113)
      ·
        refine ⟨20852923916920133398599085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27803898555893511198132113 20852923916920133398599085)
        ·
          refine ⟨7819846468845050024474657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20852923916920133398599085 7819846468845050024474657)
          ·
            refine ⟨5864884851633787518355993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7819846468845050024474657 5864884851633787518355993)
            ·
              refine ⟨4398663638725340638766995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864884851633787518355993 4398663638725340638766995)
              ·
                refine ⟨6597995458088010958150493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398663638725340638766995 6597995458088010958150493)
                ·
                  refine ⟨2474248296783004109306435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6597995458088010958150493 2474248296783004109306435)
                  ·
                    refine ⟨3711372445174506163959653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474248296783004109306435 3711372445174506163959653)
                    ·
                      refine ⟨695882333470219905742435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3711372445174506163959653 695882333470219905742435)
                      ·
                        rfl

theorem cell23_1355226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1355226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355226 prefixEnd_1355226 := by exact prefixLift 1355226
  have htrace : WordTrace (prefixWord ++ tailWord_1355226) baseStart_1355226 baseEnd_1355226 := by
    simpa [prefixWord, tailWord_1355226, baseEnd_1355226] using wordTrace_append hprefix tailTrace_1355226
  have hstable : (prefixWord ++ tailWord_1355226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355226).length < 2 ^ (prefixWord ++ tailWord_1355226).sum := by decide
  have hdescent : baseEnd_1355226 < baseStart_1355226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355237 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1355237 : Nat := 118140960795 + 1355237 * 2 ^ 59
def prefixEnd_1355237 : Nat := 4983230072969 + 3 ^ 40 * 1355237 * 2
def baseEnd_1355237 : Nat := 695887981757419362704885

theorem tailTrace_1355237 : CollatzResearch.WordTrace tailWord_1355237 prefixEnd_1355237 695887981757419362704885 := by
  unfold tailWord_1355237
  simp only [CollatzResearch.WordTrace]
  refine ⟨49429554191215279897551965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32953036127476853265034643 49429554191215279897551965)
  ·
    refine ⟨18536082821705729961581987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49429554191215279897551965 18536082821705729961581987)
    ·
      refine ⟨27804124232558594942372981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18536082821705729961581987 27804124232558594942372981)
      ·
        refine ⟨2606636646802368275847467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27804124232558594942372981 2606636646802368275847467)
        ·
          refine ⟨3909954970203552413771201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606636646802368275847467 3909954970203552413771201)
          ·
            refine ⟨2932466227652664310328401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909954970203552413771201 2932466227652664310328401)
            ·
              refine ⟨2199349670739498232746301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932466227652664310328401 2199349670739498232746301)
              ·
                refine ⟨824756126527311837279863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199349670739498232746301 824756126527311837279863)
                ·
                  refine ⟨1237134189790967755919795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824756126527311837279863 1237134189790967755919795)
                  ·
                    refine ⟨1855701284686451633879693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237134189790967755919795 1855701284686451633879693)
                    ·
                      refine ⟨695887981757419362704885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855701284686451633879693 695887981757419362704885)
                      ·
                        rfl

theorem cell23_1355237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1355237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355237 prefixEnd_1355237 := by exact prefixLift 1355237
  have htrace : WordTrace (prefixWord ++ tailWord_1355237) baseStart_1355237 baseEnd_1355237 := by
    simpa [prefixWord, tailWord_1355237, baseEnd_1355237] using wordTrace_append hprefix tailTrace_1355237
  have hstable : (prefixWord ++ tailWord_1355237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355237).length < 2 ^ (prefixWord ++ tailWord_1355237).sum := by decide
  have hdescent : baseEnd_1355237 < baseStart_1355237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355246 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1355246 : Nat := 118140960795 + 1355246 * 2 ^ 59
def prefixEnd_1355246 : Nat := 4983230072969 + 3 ^ 40 * 1355246 * 2
def baseEnd_1355246 : Nat := 695892603083309827492343

theorem tailTrace_1355246 : CollatzResearch.WordTrace tailWord_1355246 prefixEnd_1355246 695892603083309827492343 := by
  unfold tailWord_1355246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178735306022834304328699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32953254965455116289753061 6178735306022834304328699)
  ·
    refine ⟨9268102959034251456493049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178735306022834304328699 9268102959034251456493049)
    ·
      refine ⟨6951077219275688592369787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9268102959034251456493049 6951077219275688592369787)
      ·
        refine ⟨10426615828913532888554681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6951077219275688592369787 10426615828913532888554681)
        ·
          refine ⟨7819961871685149666416011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10426615828913532888554681 7819961871685149666416011)
          ·
            refine ⟨11729942807527724499624017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819961871685149666416011 11729942807527724499624017)
            ·
              refine ⟨8797457105645793374718013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11729942807527724499624017 8797457105645793374718013)
              ·
                refine ⟨3299046414617172515519255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8797457105645793374718013 3299046414617172515519255)
                ·
                  refine ⟨4948569621925758773278883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299046414617172515519255 4948569621925758773278883)
                  ·
                    refine ⟨7422854432888638159918325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4948569621925758773278883 7422854432888638159918325)
                    ·
                      refine ⟨695892603083309827492343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7422854432888638159918325 695892603083309827492343)
                      ·
                        rfl

theorem cell23_1355246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1355246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355246 prefixEnd_1355246 := by exact prefixLift 1355246
  have htrace : WordTrace (prefixWord ++ tailWord_1355246) baseStart_1355246 baseEnd_1355246 := by
    simpa [prefixWord, tailWord_1355246, baseEnd_1355246] using wordTrace_append hprefix tailTrace_1355246
  have hstable : (prefixWord ++ tailWord_1355246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355246).length < 2 ^ (prefixWord ++ tailWord_1355246).sum := by decide
  have hdescent : baseEnd_1355246 < baseStart_1355246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355249 : List Nat := [1, 2, 2, 2, 3, 3, 10]
def baseStart_1355249 : Nat := 118140960795 + 1355249 * 2 ^ 59
def prefixEnd_1355249 : Nat := 4983230072969 + 3 ^ 40 * 1355249 * 2
def baseEnd_1355249 : Nat := 8591285722534238466109

theorem tailTrace_1355249 : CollatzResearch.WordTrace tailWord_1355249 prefixEnd_1355249 8591285722534238466109 := by
  unfold tailWord_1355249
  simp only [CollatzResearch.WordTrace]
  refine ⟨49429991867171805946988801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32953327911447870631325867 49429991867171805946988801)
  ·
    refine ⟨37072493900378854460241601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49429991867171805946988801 37072493900378854460241601)
    ·
      refine ⟨27804370425284140845181201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37072493900378854460241601 27804370425284140845181201)
      ·
        refine ⟨20853277818963105633885901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27804370425284140845181201 20853277818963105633885901)
        ·
          refine ⟨7819979182111164612707213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20853277818963105633885901 7819979182111164612707213)
          ·
            refine ⟨2932492193291686729765205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7819979182111164612707213 2932492193291686729765205)
            ·
              refine ⟨8591285722534238466109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2932492193291686729765205 8591285722534238466109)
              ·
                rfl

theorem cell23_1355249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 10].length) (baseStart_1355249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355249 prefixEnd_1355249 := by exact prefixLift 1355249
  have htrace : WordTrace (prefixWord ++ tailWord_1355249) baseStart_1355249 baseEnd_1355249 := by
    simpa [prefixWord, tailWord_1355249, baseEnd_1355249] using wordTrace_append hprefix tailTrace_1355249
  have hstable : (prefixWord ++ tailWord_1355249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355249).length < 2 ^ (prefixWord ++ tailWord_1355249).sum := by decide
  have hdescent : baseEnd_1355249 < baseStart_1355249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355293 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1355293 : Nat := 118140960795 + 1355293 * 2 ^ 59
def prefixEnd_1355293 : Nat := 4983230072969 + 3 ^ 40 * 1355293 * 2
def baseEnd_1355293 : Nat := 695916736674071143604627

theorem tailTrace_1355293 : CollatzResearch.WordTrace tailWord_1355293 prefixEnd_1355293 695916736674071143604627 := by
  unfold tailWord_1355293
  simp only [CollatzResearch.WordTrace]
  refine ⟨49431596679012401461590533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32954397786008267641060355 49431596679012401461590533)
  ·
    refine ⟨9268424377314825274048225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49431596679012401461590533 9268424377314825274048225)
    ·
      refine ⟨6951318282986118955536169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9268424377314825274048225 6951318282986118955536169)
      ·
        refine ⟨5213488712239589216652127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6951318282986118955536169 5213488712239589216652127)
        ·
          refine ⟨7820233068359383824978191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213488712239589216652127 7820233068359383824978191)
          ·
            refine ⟨11730349602539075737467287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820233068359383824978191 11730349602539075737467287)
            ·
              refine ⟨17595524403808613606200931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11730349602539075737467287 17595524403808613606200931)
              ·
                refine ⟨26393286605712920409301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17595524403808613606200931 26393286605712920409301397)
                ·
                  refine ⟨1237185309642793144186003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26393286605712920409301397 1237185309642793144186003)
                  ·
                    refine ⟨1855777964464189716279005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237185309642793144186003 1855777964464189716279005)
                    ·
                      refine ⟨695916736674071143604627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855777964464189716279005 695916736674071143604627)
                      ·
                        rfl

theorem cell23_1355293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1355293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355293 prefixEnd_1355293 := by exact prefixLift 1355293
  have htrace : WordTrace (prefixWord ++ tailWord_1355293) baseStart_1355293 baseEnd_1355293 := by
    simpa [prefixWord, tailWord_1355293, baseEnd_1355293] using wordTrace_append hprefix tailTrace_1355293
  have hstable : (prefixWord ++ tailWord_1355293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355293).length < 2 ^ (prefixWord ++ tailWord_1355293).sum := by decide
  have hdescent : baseEnd_1355293 < baseStart_1355293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355306 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1355306 : Nat := 118140960795 + 1355306 * 2 ^ 59
def prefixEnd_1355306 : Nat := 4983230072969 + 3 ^ 40 * 1355306 * 2
def baseEnd_1355306 : Nat := 695923411922579592742067

theorem tailTrace_1355306 : CollatzResearch.WordTrace tailWord_1355306 prefixEnd_1355306 695923411922579592742067 := by
  unfold tailWord_1355306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12358017706991326170453443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32954713885310203121209181 12358017706991326170453443)
  ·
    refine ⟨18537026560486989255680165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12358017706991326170453443 18537026560486989255680165)
    ·
      refine ⟨3475692480091310485440031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18537026560486989255680165 3475692480091310485440031)
      ·
        refine ⟨5213538720136965728160047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475692480091310485440031 5213538720136965728160047)
        ·
          refine ⟨7820308080205448592240071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213538720136965728160047 7820308080205448592240071)
          ·
            refine ⟨11730462120308172888360107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820308080205448592240071 11730462120308172888360107)
            ·
              refine ⟨17595693180462259332540161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11730462120308172888360107 17595693180462259332540161)
              ·
                refine ⟨13196769885346694499405121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17595693180462259332540161 13196769885346694499405121)
                ·
                  refine ⟨9897577414010020874553841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196769885346694499405121 9897577414010020874553841)
                  ·
                    refine ⟨7423183060507515655915381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9897577414010020874553841 7423183060507515655915381)
                    ·
                      refine ⟨695923411922579592742067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7423183060507515655915381 695923411922579592742067)
                      ·
                        rfl

theorem cell23_1355306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1355306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355306 prefixEnd_1355306 := by exact prefixLift 1355306
  have htrace : WordTrace (prefixWord ++ tailWord_1355306) baseStart_1355306 baseEnd_1355306 := by
    simpa [prefixWord, tailWord_1355306, baseEnd_1355306] using wordTrace_append hprefix tailTrace_1355306
  have hstable : (prefixWord ++ tailWord_1355306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355306).length < 2 ^ (prefixWord ++ tailWord_1355306).sum := by decide
  have hdescent : baseEnd_1355306 < baseStart_1355306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355310 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1355310 : Nat := 118140960795 + 1355310 * 2 ^ 59
def prefixEnd_1355310 : Nat := 4983230072969 + 3 ^ 40 * 1355310 * 2
def baseEnd_1355310 : Nat := 695925465845197577092049

theorem tailTrace_1355310 : CollatzResearch.WordTrace tailWord_1355310 prefixEnd_1355310 695925465845197577092049 := by
  unfold tailWord_1355310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179027089993851670619923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32954811146633875576639589 6179027089993851670619923)
  ·
    refine ⟨9268540634990777505929885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179027089993851670619923 9268540634990777505929885)
    ·
      refine ⟨3475702738121541564723707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9268540634990777505929885 3475702738121541564723707)
      ·
        refine ⟨5213554107182312347085561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475702738121541564723707 5213554107182312347085561)
        ·
          refine ⟨3910165580386734260314171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213554107182312347085561 3910165580386734260314171)
          ·
            refine ⟨5865248370580101390471257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910165580386734260314171 5865248370580101390471257)
            ·
              refine ⟨4398936277935076042853443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865248370580101390471257 4398936277935076042853443)
              ·
                refine ⟨6598404416902614064280165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398936277935076042853443 6598404416902614064280165)
                ·
                  refine ⟨1237200828169240137052531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6598404416902614064280165 1237200828169240137052531)
                  ·
                    refine ⟨1855801242253860205578797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237200828169240137052531 1855801242253860205578797)
                    ·
                      refine ⟨695925465845197577092049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855801242253860205578797 695925465845197577092049)
                      ·
                        rfl

theorem cell23_1355310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1355310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355310 prefixEnd_1355310 := by exact prefixLift 1355310
  have htrace : WordTrace (prefixWord ++ tailWord_1355310) baseStart_1355310 baseEnd_1355310 := by
    simpa [prefixWord, tailWord_1355310, baseEnd_1355310] using wordTrace_append hprefix tailTrace_1355310
  have hstable : (prefixWord ++ tailWord_1355310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355310).length < 2 ^ (prefixWord ++ tailWord_1355310).sum := by decide
  have hdescent : baseEnd_1355310 < baseStart_1355310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355327 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 2, 1, 3]
def baseStart_1355327 : Nat := 118140960795 + 1355327 * 2 ^ 59
def prefixEnd_1355327 : Nat := 4983230072969 + 3 ^ 40 * 1355327 * 2
def baseEnd_1355327 : Nat := 695934195016324010579471

theorem tailTrace_1355327 : CollatzResearch.WordTrace tailWord_1355327 prefixEnd_1355327 695934195016324010579471 := by
  unfold tailWord_1355327
  simp only [CollatzResearch.WordTrace]
  refine ⟨49432836760889225268328235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32955224507259483512218823 49432836760889225268328235)
  ·
    refine ⟨74149255141333837902492353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49432836760889225268328235 74149255141333837902492353)
    ·
      refine ⟨55611941356000378426869265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74149255141333837902492353 55611941356000378426869265)
      ·
        refine ⟨41708956017000283820151949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55611941356000378426869265 41708956017000283820151949)
        ·
          refine ⟨15640858506375106432556981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41708956017000283820151949 15640858506375106432556981)
          ·
            refine ⟨1466330484972666228052217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15640858506375106432556981 1466330484972666228052217)
            ·
              refine ⟨1099747863729499671039163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466330484972666228052217 1099747863729499671039163)
              ·
                refine ⟨1649621795594249506558745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099747863729499671039163 1649621795594249506558745)
                ·
                  refine ⟨1237216346695687129919059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649621795594249506558745 1237216346695687129919059)
                  ·
                    refine ⟨1855824520043530694878589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237216346695687129919059 1855824520043530694878589)
                    ·
                      refine ⟨695934195016324010579471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1855824520043530694878589 695934195016324010579471)
                      ·
                        rfl

theorem cell23_1355327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_1355327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355327 prefixEnd_1355327 := by exact prefixLift 1355327
  have htrace : WordTrace (prefixWord ++ tailWord_1355327) baseStart_1355327 baseEnd_1355327 := by
    simpa [prefixWord, tailWord_1355327, baseEnd_1355327] using wordTrace_append hprefix tailTrace_1355327
  have hstable : (prefixWord ++ tailWord_1355327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355327).length < 2 ^ (prefixWord ++ tailWord_1355327).sum := by decide
  have hdescent : baseEnd_1355327 < baseStart_1355327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355333 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_1355333 : Nat := 118140960795 + 1355333 * 2 ^ 59
def prefixEnd_1355333 : Nat := 4983230072969 + 3 ^ 40 * 1355333 * 2
def baseEnd_1355333 : Nat := 695937275900250987104443

theorem tailTrace_1355333 : CollatzResearch.WordTrace tailWord_1355333 prefixEnd_1355333 695937275900250987104443 := by
  unfold tailWord_1355333
  simp only [CollatzResearch.WordTrace]
  refine ⟨49433055598867488293046653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32955370399244992195364435 49433055598867488293046653)
  ·
    refine ⟨18537395849575308109892495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49433055598867488293046653 18537395849575308109892495)
    ·
      refine ⟨27806093774362962164838743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18537395849575308109892495 27806093774362962164838743)
      ·
        refine ⟨41709140661544443247258115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27806093774362962164838743 41709140661544443247258115)
        ·
          refine ⟨62563710992316664870887173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41709140661544443247258115 62563710992316664870887173)
          ·
            refine ⟨11730695811059374663291345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62563710992316664870887173 11730695811059374663291345)
            ·
              refine ⟨8798021858294530997468509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11730695811059374663291345 8798021858294530997468509)
              ·
                refine ⟨3299258196860449124050691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8798021858294530997468509 3299258196860449124050691)
                ·
                  refine ⟨4948887295290673686076037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299258196860449124050691 4948887295290673686076037)
                  ·
                    refine ⟨927916367867001316139257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4948887295290673686076037 927916367867001316139257)
                    ·
                      refine ⟨695937275900250987104443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927916367867001316139257 695937275900250987104443)
                      ·
                        rfl

theorem cell23_1355333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_1355333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355333 prefixEnd_1355333 := by exact prefixLift 1355333
  have htrace : WordTrace (prefixWord ++ tailWord_1355333) baseStart_1355333 baseEnd_1355333 := by
    simpa [prefixWord, tailWord_1355333, baseEnd_1355333] using wordTrace_append hprefix tailTrace_1355333
  have hstable : (prefixWord ++ tailWord_1355333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355333).length < 2 ^ (prefixWord ++ tailWord_1355333).sum := by decide
  have hdescent : baseEnd_1355333 < baseStart_1355333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355339 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 9]
def baseStart_1355339 : Nat := 118140960795 + 1355339 * 2 ^ 59
def prefixEnd_1355339 : Nat := 4983230072969 + 3 ^ 40 * 1355339 * 2
def baseEnd_1355339 : Nat := 77326706309353107069935

theorem tailTrace_1355339 : CollatzResearch.WordTrace tailWord_1355339 prefixEnd_1355339 77326706309353107069935 := by
  unfold tailWord_1355339
  simp only [CollatzResearch.WordTrace]
  refine ⟨49433274436845751317765071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32955516291230500878510047 49433274436845751317765071)
  ·
    refine ⟨74149911655268626976647607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49433274436845751317765071 74149911655268626976647607)
    ·
      refine ⟨111224867482902940464971411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74149911655268626976647607 111224867482902940464971411)
      ·
        refine ⟨166837301224354410697457117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111224867482902940464971411 166837301224354410697457117)
        ·
          refine ⟨62563987959132904011546419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166837301224354410697457117 62563987959132904011546419)
          ·
            refine ⟨93845981938699356017319629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62563987959132904011546419 93845981938699356017319629)
            ·
              refine ⟨35192243227012258506494861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93845981938699356017319629 35192243227012258506494861)
              ·
                refine ⟨13197091210129596939935573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35192243227012258506494861 13197091210129596939935573)
                ·
                  refine ⟨77326706309353107069935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13197091210129596939935573 77326706309353107069935)
                  ·
                    rfl

theorem cell23_1355339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_1355339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355339 prefixEnd_1355339 := by exact prefixLift 1355339
  have htrace : WordTrace (prefixWord ++ tailWord_1355339) baseStart_1355339 baseEnd_1355339 := by
    simpa [prefixWord, tailWord_1355339, baseEnd_1355339] using wordTrace_append hprefix tailTrace_1355339
  have hstable : (prefixWord ++ tailWord_1355339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355339).length < 2 ^ (prefixWord ++ tailWord_1355339).sum := by decide
  have hdescent : baseEnd_1355339 < baseStart_1355339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355458 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1355458 : Nat := 118140960795 + 1355458 * 2 ^ 59
def prefixEnd_1355458 : Nat := 4983230072969 + 3 ^ 40 * 1355458 * 2
def baseEnd_1355458 : Nat := 77333495664673666449041

theorem tailTrace_1355458 : CollatzResearch.WordTrace tailWord_1355458 prefixEnd_1355458 77333495664673666449041 := by
  unfold tailWord_1355458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12359403680853658660336757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32958409815609756427564685 12359403680853658660336757)
  ·
    refine ⟨1158694095080030499406571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12359403680853658660336757 1158694095080030499406571)
    ·
      refine ⟨1738041142620045749109857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158694095080030499406571 1738041142620045749109857)
      ·
        refine ⟨1303530856965034311832393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738041142620045749109857 1303530856965034311832393)
        ·
          refine ⟨977648142723775733874295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303530856965034311832393 977648142723775733874295)
          ·
            refine ⟨1466472214085663600811443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977648142723775733874295 1466472214085663600811443)
            ·
              refine ⟨2199708321128495401217165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466472214085663600811443 2199708321128495401217165)
              ·
                refine ⟨824890620423185775456437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199708321128495401217165 824890620423185775456437)
                ·
                  refine ⟨77333495664673666449041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 824890620423185775456437 77333495664673666449041)
                  ·
                    rfl

theorem cell23_1355458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1355458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355458 prefixEnd_1355458 := by exact prefixLift 1355458
  have htrace : WordTrace (prefixWord ++ tailWord_1355458) baseStart_1355458 baseEnd_1355458 := by
    simpa [prefixWord, tailWord_1355458, baseEnd_1355458] using wordTrace_append hprefix tailTrace_1355458
  have hstable : (prefixWord ++ tailWord_1355458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355458).length < 2 ^ (prefixWord ++ tailWord_1355458).sum := by decide
  have hdescent : baseEnd_1355458 < baseStart_1355458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355460 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1355460 : Nat := 118140960795 + 1355460 * 2 ^ 59
def prefixEnd_1355460 : Nat := 4983230072969 + 3 ^ 40 * 1355460 * 2
def baseEnd_1355460 : Nat := 696002487943371990216359

theorem tailTrace_1355460 : CollatzResearch.WordTrace tailWord_1355460 prefixEnd_1355460 696002487943371990216359 := by
  unfold tailWord_1355460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718843834703694491459917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32958458446271592655279889 24718843834703694491459917)
  ·
    refine ⟨9269566438013885434297469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24718843834703694491459917 9269566438013885434297469)
    ·
      refine ⟨3476087414255207037861551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9269566438013885434297469 3476087414255207037861551)
      ·
        refine ⟨5214131121382810556792327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476087414255207037861551 5214131121382810556792327)
        ·
          refine ⟨7821196682074215835188491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214131121382810556792327 7821196682074215835188491)
          ·
            refine ⟨11731795023111323752782737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821196682074215835188491 11731795023111323752782737)
            ·
              refine ⟨8798846267333492814587053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11731795023111323752782737 8798846267333492814587053)
              ·
                refine ⟨3299567350250059805470145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8798846267333492814587053 3299567350250059805470145)
                ·
                  refine ⟨2474675512687544854102609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299567350250059805470145 2474675512687544854102609)
                  ·
                    refine ⟨1856006634515658640576957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474675512687544854102609 1856006634515658640576957)
                    ·
                      refine ⟨696002487943371990216359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856006634515658640576957 696002487943371990216359)
                      ·
                        rfl

theorem cell23_1355460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1355460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355460 prefixEnd_1355460 := by exact prefixLift 1355460
  have htrace : WordTrace (prefixWord ++ tailWord_1355460) baseStart_1355460 baseEnd_1355460 := by
    simpa [prefixWord, tailWord_1355460, baseEnd_1355460] using wordTrace_append hprefix tailTrace_1355460
  have hstable : (prefixWord ++ tailWord_1355460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355460).length < 2 ^ (prefixWord ++ tailWord_1355460).sum := by decide
  have hdescent : baseEnd_1355460 < baseStart_1355460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355484 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1355484 : Nat := 118140960795 + 1355484 * 2 ^ 59
def prefixEnd_1355484 : Nat := 4983230072969 + 3 ^ 40 * 1355484 * 2
def baseEnd_1355484 : Nat := 232004937159693298772083

theorem tailTrace_1355484 : CollatzResearch.WordTrace tailWord_1355484 prefixEnd_1355484 232004937159693298772083 := by
  unfold tailWord_1355484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719281510660220540896753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32959042014213627387862337 24719281510660220540896753)
  ·
    refine ⟨18539461132995165405672565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24719281510660220540896753 18539461132995165405672565)
    ·
      refine ⟨1738074481218296756781803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18539461132995165405672565 1738074481218296756781803)
      ·
        refine ⟨2607111721827445135172705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738074481218296756781803 2607111721827445135172705)
        ·
          refine ⟨1955333791370583851379529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607111721827445135172705 1955333791370583851379529)
          ·
            refine ⟨1466500343527937888534647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955333791370583851379529 1466500343527937888534647)
            ·
              refine ⟨2199750515291906832801971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466500343527937888534647 2199750515291906832801971)
              ·
                refine ⟨3299625772937860249202957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199750515291906832801971 3299625772937860249202957)
                ·
                  refine ⟨1237359664851697593451109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3299625772937860249202957 1237359664851697593451109)
                  ·
                    refine ⟨232004937159693298772083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237359664851697593451109 232004937159693298772083)
                    ·
                      rfl

theorem cell23_1355484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1355484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355484 prefixEnd_1355484 := by exact prefixLift 1355484
  have htrace : WordTrace (prefixWord ++ tailWord_1355484) baseStart_1355484 baseEnd_1355484 := by
    simpa [prefixWord, tailWord_1355484, baseEnd_1355484] using wordTrace_append hprefix tailTrace_1355484
  have hstable : (prefixWord ++ tailWord_1355484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355484).length < 2 ^ (prefixWord ++ tailWord_1355484).sum := by decide
  have hdescent : baseEnd_1355484 < baseStart_1355484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355493 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1355493 : Nat := 118140960795 + 1355493 * 2 ^ 59
def prefixEnd_1355493 : Nat := 4983230072969 + 3 ^ 40 * 1355493 * 2
def baseEnd_1355493 : Nat := 232006477601656787034569

theorem tailTrace_1355493 : CollatzResearch.WordTrace tailWord_1355493 prefixEnd_1355493 232006477601656787034569 := by
  unfold tailWord_1355493
  simp only [CollatzResearch.WordTrace]
  refine ⟨49438891278287835618871133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32959260852191890412580755 49438891278287835618871133)
  ·
    refine ⟨18539584229357938357076675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49438891278287835618871133 18539584229357938357076675)
    ·
      refine ⟨27809376344036907535615013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18539584229357938357076675 27809376344036907535615013)
      ·
        refine ⟨5214258064506920162927815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27809376344036907535615013 5214258064506920162927815)
        ·
          refine ⟨7821387096760380244391723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214258064506920162927815 7821387096760380244391723)
          ·
            refine ⟨11732080645140570366587585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821387096760380244391723 11732080645140570366587585)
            ·
              refine ⟨8799060483855427774940689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732080645140570366587585 8799060483855427774940689)
              ·
                refine ⟨6599295362891570831205517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8799060483855427774940689 6599295362891570831205517)
                ·
                  refine ⟨2474735761084339061702069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6599295362891570831205517 2474735761084339061702069)
                  ·
                    refine ⟨232006477601656787034569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2474735761084339061702069 232006477601656787034569)
                    ·
                      rfl

theorem cell23_1355493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1355493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355493 prefixEnd_1355493 := by exact prefixLift 1355493
  have htrace : WordTrace (prefixWord ++ tailWord_1355493) baseStart_1355493 baseEnd_1355493 := by
    simpa [prefixWord, tailWord_1355493, baseEnd_1355493] using wordTrace_append hprefix tailTrace_1355493
  have hstable : (prefixWord ++ tailWord_1355493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355493).length < 2 ^ (prefixWord ++ tailWord_1355493).sum := by decide
  have hdescent : baseEnd_1355493 < baseStart_1355493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355510 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1355510 : Nat := 118140960795 + 1355510 * 2 ^ 59
def prefixEnd_1355510 : Nat := 4983230072969 + 3 ^ 40 * 1355510 * 2
def baseEnd_1355510 : Nat := 232009387325365598197043

theorem tailTrace_1355510 : CollatzResearch.WordTrace tailWord_1355510 prefixEnd_1355510 232009387325365598197043 := by
  unfold tailWord_1355510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089969457451640470139999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32959674212817498348159989 3089969457451640470139999)
  ·
    refine ⟨4634954186177460705209999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089969457451640470139999 4634954186177460705209999)
    ·
      refine ⟨6952431279266191057814999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4634954186177460705209999 6952431279266191057814999)
      ·
        refine ⟨10428646918899286586722499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952431279266191057814999 10428646918899286586722499)
        ·
          refine ⟨15642970378348929880083749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428646918899286586722499 15642970378348929880083749)
          ·
            refine ⟨2933056945940424352515703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15642970378348929880083749 2933056945940424352515703)
            ·
              refine ⟨4399585418910636528773555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933056945940424352515703 4399585418910636528773555)
              ·
                refine ⟨6599378128365954793160333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399585418910636528773555 6599378128365954793160333)
                ·
                  refine ⟨2474766798137233047435125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6599378128365954793160333 2474766798137233047435125)
                  ·
                    refine ⟨232009387325365598197043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2474766798137233047435125 232009387325365598197043)
                    ·
                      rfl

theorem cell23_1355510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1355510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355510 prefixEnd_1355510 := by exact prefixLift 1355510
  have htrace : WordTrace (prefixWord ++ tailWord_1355510) baseStart_1355510 baseEnd_1355510 := by
    simpa [prefixWord, tailWord_1355510, baseEnd_1355510] using wordTrace_append hprefix tailTrace_1355510
  have hstable : (prefixWord ++ tailWord_1355510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355510).length < 2 ^ (prefixWord ++ tailWord_1355510).sum := by decide
  have hdescent : baseEnd_1355510 < baseStart_1355510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355523 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 6, 4]
def baseStart_1355523 : Nat := 118140960795 + 1355523 * 2 ^ 59
def prefixEnd_1355523 : Nat := 4983230072969 + 3 ^ 40 * 1355523 * 2
def baseEnd_1355523 : Nat := 232011612408201747909523

theorem tailTrace_1355523 : CollatzResearch.WordTrace tailWord_1355523 prefixEnd_1355523 232011612408201747909523 := by
  unfold tailWord_1355523
  simp only [CollatzResearch.WordTrace]
  refine ⟨49439985468179150742463223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32959990312119433828308815 49439985468179150742463223)
  ·
    refine ⟨74159978202268726113694835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49439985468179150742463223 74159978202268726113694835)
    ·
      refine ⟨111239967303403089170542253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74159978202268726113694835 111239967303403089170542253)
      ·
        refine ⟨41714987738776158438953345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111239967303403089170542253 41714987738776158438953345)
        ·
          refine ⟨31286240804082118829215009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41714987738776158438953345 31286240804082118829215009)
          ·
            refine ⟨23464680603061589121911257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31286240804082118829215009 23464680603061589121911257)
            ·
              refine ⟨17598510452296191841433443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23464680603061589121911257 17598510452296191841433443)
              ·
                refine ⟨26397765678444287762150165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598510452296191841433443 26397765678444287762150165)
                ·
                  refine ⟨1237395266177075988850789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26397765678444287762150165 1237395266177075988850789)
                  ·
                    refine ⟨232011612408201747909523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237395266177075988850789 232011612408201747909523)
                    ·
                      rfl

theorem cell23_1355523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 4].length) (baseStart_1355523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355523 prefixEnd_1355523 := by exact prefixLift 1355523
  have htrace : WordTrace (prefixWord ++ tailWord_1355523) baseStart_1355523 baseEnd_1355523 := by
    simpa [prefixWord, tailWord_1355523, baseEnd_1355523] using wordTrace_append hprefix tailTrace_1355523
  have hstable : (prefixWord ++ tailWord_1355523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355523).length < 2 ^ (prefixWord ++ tailWord_1355523).sum := by decide
  have hdescent : baseEnd_1355523 < baseStart_1355523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355541 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_1355541 : Nat := 118140960795 + 1355541 * 2 ^ 59
def prefixEnd_1355541 : Nat := 4983230072969 + 3 ^ 40 * 1355541 * 2
def baseEnd_1355541 : Nat := 696044079876386173303487

theorem tailTrace_1355541 : CollatzResearch.WordTrace tailWord_1355541 prefixEnd_1355541 696044079876386173303487 := by
  unfold tailWord_1355541
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440641982113939816618477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32960427988075959877745651 49440641982113939816618477)
  ·
    refine ⟨18540240743292727431231929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49440641982113939816618477 18540240743292727431231929)
    ·
      refine ⟨13905180557469545573423947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18540240743292727431231929 13905180557469545573423947)
      ·
        refine ⟨20857770836204318360135921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905180557469545573423947 20857770836204318360135921)
        ·
          refine ⟨15643328127153238770101941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20857770836204318360135921 15643328127153238770101941)
          ·
            refine ⟨1466562011920616134697057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15643328127153238770101941 1466562011920616134697057)
            ·
              refine ⟨1099921508940462101022793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466562011920616134697057 1099921508940462101022793)
              ·
                refine ⟨824941131705346575767095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099921508940462101022793 824941131705346575767095)
                ·
                  refine ⟨1237411697558019863650643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824941131705346575767095 1237411697558019863650643)
                  ·
                    refine ⟨1856117546337029795475965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237411697558019863650643 1856117546337029795475965)
                    ·
                      refine ⟨696044079876386173303487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856117546337029795475965 696044079876386173303487)
                      ·
                        rfl

theorem cell23_1355541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_1355541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355541 prefixEnd_1355541 := by exact prefixLift 1355541
  have htrace : WordTrace (prefixWord ++ tailWord_1355541) baseStart_1355541 baseEnd_1355541 := by
    simpa [prefixWord, tailWord_1355541, baseEnd_1355541] using wordTrace_append hprefix tailTrace_1355541
  have hstable : (prefixWord ++ tailWord_1355541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355541).length < 2 ^ (prefixWord ++ tailWord_1355541).sum := by decide
  have hdescent : baseEnd_1355541 < baseStart_1355541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355553 : List Nat := [1, 2, 3, 2, 1, 3, 3, 8]
def baseStart_1355553 : Nat := 118140960795 + 1355553 * 2 ^ 59
def prefixEnd_1355553 : Nat := 4983230072969 + 3 ^ 40 * 1355553 * 2
def baseEnd_1355553 : Nat := 25779638579416300976053

theorem tailTrace_1355553 : CollatzResearch.WordTrace tailWord_1355553 prefixEnd_1355553 25779638579416300976053 := by
  unfold tailWord_1355553
  simp only [CollatzResearch.WordTrace]
  refine ⟨49441079658070465866055313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32960719772046977244036875 49441079658070465866055313)
  ·
    refine ⟨37080809743552849399541485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49441079658070465866055313 37080809743552849399541485)
    ·
      refine ⟨13905303653832318524828057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37080809743552849399541485 13905303653832318524828057)
      ·
        refine ⟨10428977740374238893621043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13905303653832318524828057 10428977740374238893621043)
        ·
          refine ⟨15643466610561358340431565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428977740374238893621043 15643466610561358340431565)
          ·
            refine ⟨5866299978960509377661837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15643466610561358340431565 5866299978960509377661837)
            ·
              refine ⟨2199862492110191016623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5866299978960509377661837 2199862492110191016623189)
              ·
                refine ⟨25779638579416300976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2199862492110191016623189 25779638579416300976053)
                ·
                  rfl

theorem cell23_1355553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 8].length) (baseStart_1355553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355553 prefixEnd_1355553 := by exact prefixLift 1355553
  have htrace : WordTrace (prefixWord ++ tailWord_1355553) baseStart_1355553 baseEnd_1355553 := by
    simpa [prefixWord, tailWord_1355553, baseEnd_1355553] using wordTrace_append hprefix tailTrace_1355553
  have hstable : (prefixWord ++ tailWord_1355553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355553).length < 2 ^ (prefixWord ++ tailWord_1355553).sum := by decide
  have hdescent : baseEnd_1355553 < baseStart_1355553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355560 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1355560 : Nat := 118140960795 + 1355560 * 2 ^ 59
def prefixEnd_1355560 : Nat := 4983230072969 + 3 ^ 40 * 1355560 * 2
def baseEnd_1355560 : Nat := 696053836008821598965899

theorem tailTrace_1355560 : CollatzResearch.WordTrace tailWord_1355560 prefixEnd_1355560 696053836008821598965899 := by
  unfold tailWord_1355560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720667484522553030780067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32960889979363404041040089 24720667484522553030780067)
  ·
    refine ⟨37081001226783829546170101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24720667484522553030780067 37081001226783829546170101)
    ·
      refine ⟨3476343865010984019953447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37081001226783829546170101 3476343865010984019953447)
      ·
        refine ⟨5214515797516476029930171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476343865010984019953447 5214515797516476029930171)
        ·
          refine ⟨7821773696274714044895257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214515797516476029930171 7821773696274714044895257)
          ·
            refine ⟨5866330272206035533671443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7821773696274714044895257 5866330272206035533671443)
            ·
              refine ⟨8799495408309053300507165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866330272206035533671443 8799495408309053300507165)
              ·
                refine ⟨3299810778115894987690187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8799495408309053300507165 3299810778115894987690187)
                ·
                  refine ⟨4949716167173842481535281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299810778115894987690187 4949716167173842481535281)
                  ·
                    refine ⟨3712287125380381861151461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4949716167173842481535281 3712287125380381861151461)
                    ·
                      refine ⟨696053836008821598965899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3712287125380381861151461 696053836008821598965899)
                      ·
                        rfl

theorem cell23_1355560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1355560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355560 prefixEnd_1355560 := by exact prefixLift 1355560
  have htrace : WordTrace (prefixWord ++ tailWord_1355560) baseStart_1355560 baseEnd_1355560 := by
    simpa [prefixWord, tailWord_1355560, baseEnd_1355560] using wordTrace_append hprefix tailTrace_1355560
  have hstable : (prefixWord ++ tailWord_1355560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355560).length < 2 ^ (prefixWord ++ tailWord_1355560).sum := by decide
  have hdescent : baseEnd_1355560 < baseStart_1355560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355570 : List Nat := [3, 2, 1, 1, 3, 3, 3, 7]
def baseStart_1355570 : Nat := 118140960795 + 1355570 * 2 ^ 59
def prefixEnd_1355570 : Nat := 4983230072969 + 3 ^ 40 * 1355570 * 2
def baseEnd_1355570 : Nat := 25779961882050613327439

theorem tailTrace_1355570 : CollatzResearch.WordTrace tailWord_1355570 prefixEnd_1355570 25779961882050613327439 := by
  unfold tailWord_1355570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360424924752219442356041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32961133132672585179616109 12360424924752219442356041)
  ·
    refine ⟨9270318693564164581767031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12360424924752219442356041 9270318693564164581767031)
    ·
      refine ⟨13905478040346246872650547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270318693564164581767031 13905478040346246872650547)
      ·
        refine ⟨20858217060519370308975821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905478040346246872650547 20858217060519370308975821)
        ·
          refine ⟨7821831397694763865865933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20858217060519370308975821 7821831397694763865865933)
          ·
            refine ⟨2933186774135536449699725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7821831397694763865865933 2933186774135536449699725)
            ·
              refine ⟨1099945040300826168637397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2933186774135536449699725 1099945040300826168637397)
              ·
                refine ⟨25779961882050613327439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1099945040300826168637397 25779961882050613327439)
                ·
                  rfl

theorem cell23_1355570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_1355570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355570 prefixEnd_1355570 := by exact prefixLift 1355570
  have htrace : WordTrace (prefixWord ++ tailWord_1355570) baseStart_1355570 baseEnd_1355570 := by
    simpa [prefixWord, tailWord_1355570, baseEnd_1355570] using wordTrace_append hprefix tailTrace_1355570
  have hstable : (prefixWord ++ tailWord_1355570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355570).length < 2 ^ (prefixWord ++ tailWord_1355570).sum := by decide
  have hdescent : baseEnd_1355570 < baseStart_1355570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355580 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1355580 : Nat := 118140960795 + 1355580 * 2 ^ 59
def prefixEnd_1355580 : Nat := 4983230072969 + 3 ^ 40 * 1355580 * 2
def baseEnd_1355580 : Nat := 696064105621911520715807

theorem tailTrace_1355580 : CollatzResearch.WordTrace tailWord_1355580 prefixEnd_1355580 696064105621911520715807 := by
  unfold tailWord_1355580
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721032214486324738644097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32961376285981766318192129 24721032214486324738644097)
  ·
    refine ⟨18540774160864743553983073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24721032214486324738644097 18540774160864743553983073)
    ·
      refine ⟨13905580620648557665487305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18540774160864743553983073 13905580620648557665487305)
      ·
        refine ⟨10429185465486418249115479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13905580620648557665487305 10429185465486418249115479)
        ·
          refine ⟨15643778198229627373673219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10429185465486418249115479 15643778198229627373673219)
          ·
            refine ⟨23465667297344441060509829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643778198229627373673219 23465667297344441060509829)
            ·
              refine ⟨4399812618252082698845593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23465667297344441060509829 4399812618252082698845593)
              ·
                refine ⟨3299859463689062024134195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399812618252082698845593 3299859463689062024134195)
                ·
                  refine ⟨4949789195533593036201293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299859463689062024134195 4949789195533593036201293)
                  ·
                    refine ⟨1856170948325097388575485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4949789195533593036201293 1856170948325097388575485)
                    ·
                      refine ⟨696064105621911520715807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856170948325097388575485 696064105621911520715807)
                      ·
                        rfl

theorem cell23_1355580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1355580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355580 prefixEnd_1355580 := by exact prefixLift 1355580
  have htrace : WordTrace (prefixWord ++ tailWord_1355580) baseStart_1355580 baseEnd_1355580 := by
    simpa [prefixWord, tailWord_1355580, baseEnd_1355580] using wordTrace_append hprefix tailTrace_1355580
  have hstable : (prefixWord ++ tailWord_1355580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355580).length < 2 ^ (prefixWord ++ tailWord_1355580).sum := by decide
  have hdescent : baseEnd_1355580 < baseStart_1355580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355581 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1355581 : Nat := 118140960795 + 1355581 * 2 ^ 59
def prefixEnd_1355581 : Nat := 4983230072969 + 3 ^ 40 * 1355581 * 2
def baseEnd_1355581 : Nat := 696064619102566016803303

theorem tailTrace_1355581 : CollatzResearch.WordTrace tailWord_1355581 prefixEnd_1355581 696064619102566016803303 := by
  unfold tailWord_1355581
  simp only [CollatzResearch.WordTrace]
  refine ⟨49442100901969026648074597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32961400601312684432049731 49442100901969026648074597)
  ·
    refine ⟨9270393919119192496513987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49442100901969026648074597 9270393919119192496513987)
    ·
      refine ⟨13905590878678788744770981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270393919119192496513987 13905590878678788744770981)
      ·
        refine ⟨2607298289752272889644559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13905590878678788744770981 2607298289752272889644559)
        ·
          refine ⟨3910947434628409334466839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607298289752272889644559 3910947434628409334466839)
          ·
            refine ⟨5866421151942614001700259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910947434628409334466839 5866421151942614001700259)
            ·
              refine ⟨8799631727913921002550389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866421151942614001700259 8799631727913921002550389)
              ·
                refine ⟨824965474491930093989099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8799631727913921002550389 824965474491930093989099)
                ·
                  refine ⟨1237448211737895140983649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824965474491930093989099 1237448211737895140983649)
                  ·
                    refine ⟨928086158803421355737737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1237448211737895140983649 928086158803421355737737)
                    ·
                      refine ⟨696064619102566016803303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928086158803421355737737 696064619102566016803303)
                      ·
                        rfl

theorem cell23_1355581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1355581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355581 prefixEnd_1355581 := by exact prefixLift 1355581
  have htrace : WordTrace (prefixWord ++ tailWord_1355581) baseStart_1355581 baseEnd_1355581 := by
    simpa [prefixWord, tailWord_1355581, baseEnd_1355581] using wordTrace_append hprefix tailTrace_1355581
  have hstable : (prefixWord ++ tailWord_1355581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355581).length < 2 ^ (prefixWord ++ tailWord_1355581).sum := by decide
  have hdescent : baseEnd_1355581 < baseStart_1355581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355624 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1355624 : Nat := 118140960795 + 1355624 * 2 ^ 59
def prefixEnd_1355624 : Nat := 4983230072969 + 3 ^ 40 * 1355624 * 2
def baseEnd_1355624 : Nat := 696086698770709348565605

theorem tailTrace_1355624 : CollatzResearch.WordTrace tailWord_1355624 prefixEnd_1355624 696086698770709348565605 := by
  unfold tailWord_1355624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721834620406622495944963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32962446160542163327926617 24721834620406622495944963)
  ·
    refine ⟨37082751930609933743917445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24721834620406622495944963 37082751930609933743917445)
    ·
      refine ⟨6953015986989362576984521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37082751930609933743917445 6953015986989362576984521)
      ·
        refine ⟨5214761990242021932738391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6953015986989362576984521 5214761990242021932738391)
        ·
          refine ⟨7822142985363032899107587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214761990242021932738391 7822142985363032899107587)
          ·
            refine ⟨11733214478044549348661381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822142985363032899107587 11733214478044549348661381)
            ·
              refine ⟨2199977714633353002874009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11733214478044549348661381 2199977714633353002874009)
              ·
                refine ⟨1649983285975014752155507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199977714633353002874009 1649983285975014752155507)
                ·
                  refine ⟨2474974928962522128233261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649983285975014752155507 2474974928962522128233261)
                  ·
                    refine ⟨928115598360945798087473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474974928962522128233261 928115598360945798087473)
                    ·
                      refine ⟨696086698770709348565605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928115598360945798087473 696086698770709348565605)
                      ·
                        rfl

theorem cell23_1355624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1355624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355624 prefixEnd_1355624 := by exact prefixLift 1355624
  have htrace : WordTrace (prefixWord ++ tailWord_1355624) baseStart_1355624 baseEnd_1355624 := by
    simpa [prefixWord, tailWord_1355624, baseEnd_1355624] using wordTrace_append hprefix tailTrace_1355624
  have hstable : (prefixWord ++ tailWord_1355624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355624).length < 2 ^ (prefixWord ++ tailWord_1355624).sum := by decide
  have hdescent : baseEnd_1355624 < baseStart_1355624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355637 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1355637 : Nat := 118140960795 + 1355637 * 2 ^ 59
def prefixEnd_1355637 : Nat := 4983230072969 + 3 ^ 40 * 1355637 * 2
def baseEnd_1355637 : Nat := 696093374019217797703045

theorem tailTrace_1355637 : CollatzResearch.WordTrace tailWord_1355637 prefixEnd_1355637 696093374019217797703045 := by
  unfold tailWord_1355637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49444143389766148212113165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32962762259844098808075443 49444143389766148212113165)
  ·
    refine ⟨18541553771162305579542437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49444143389766148212113165 18541553771162305579542437)
    ·
      refine ⟨3476541332092932296164207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18541553771162305579542437 3476541332092932296164207)
      ·
        refine ⟨5214811998139398444246311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476541332092932296164207 5214811998139398444246311)
        ·
          refine ⟨7822217997209097666369467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214811998139398444246311 7822217997209097666369467)
          ·
            refine ⟨11733326995813646499554201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822217997209097666369467 11733326995813646499554201)
            ·
              refine ⟨8799995246860234874665651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11733326995813646499554201 8799995246860234874665651)
              ·
                refine ⟨13199992870290352311998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799995246860234874665651 13199992870290352311998477)
                ·
                  refine ⟨4949997326358882116999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13199992870290352311998477 4949997326358882116999429)
                  ·
                    refine ⟨928124498692290396937393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949997326358882116999429 928124498692290396937393)
                    ·
                      refine ⟨696093374019217797703045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928124498692290396937393 696093374019217797703045)
                      ·
                        rfl

theorem cell23_1355637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1355637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355637 prefixEnd_1355637 := by exact prefixLift 1355637
  have htrace : WordTrace (prefixWord ++ tailWord_1355637) baseStart_1355637 baseEnd_1355637 := by
    simpa [prefixWord, tailWord_1355637, baseEnd_1355637] using wordTrace_append hprefix tailTrace_1355637
  have hstable : (prefixWord ++ tailWord_1355637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355637).length < 2 ^ (prefixWord ++ tailWord_1355637).sum := by decide
  have hdescent : baseEnd_1355637 < baseStart_1355637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355653 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1355653 : Nat := 118140960795 + 1355653 * 2 ^ 59
def prefixEnd_1355653 : Nat := 4983230072969 + 3 ^ 40 * 1355653 * 2
def baseEnd_1355653 : Nat := 696101589709689735102971

theorem tailTrace_1355653 : CollatzResearch.WordTrace tailWord_1355653 prefixEnd_1355653 696101589709689735102971 := by
  unfold tailWord_1355653
  simp only [CollatzResearch.WordTrace]
  refine ⟨49444726957708182944695613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32963151305138788629797075 49444726957708182944695613)
  ·
    refine ⟨18541772609140568604260855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49444726957708182944695613 18541772609140568604260855)
    ·
      refine ⟨27812658913710852906391283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541772609140568604260855 27812658913710852906391283)
      ·
        refine ⟨41718988370566279359586925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27812658913710852906391283 41718988370566279359586925)
        ·
          refine ⟨15644620638962354759845097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41718988370566279359586925 15644620638962354759845097)
          ·
            refine ⟨11733465479221766069883823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15644620638962354759845097 11733465479221766069883823)
            ·
              refine ⟨17600198218832649104825735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11733465479221766069883823 17600198218832649104825735)
              ·
                refine ⟨26400297328248973657238603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17600198218832649104825735 26400297328248973657238603)
                ·
                  refine ⟨39600445992373460485857905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26400297328248973657238603 39600445992373460485857905)
                  ·
                    refine ⟨29700334494280095364393429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39600445992373460485857905 29700334494280095364393429)
                    ·
                      refine ⟨696101589709689735102971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29700334494280095364393429 696101589709689735102971)
                      ·
                        rfl

theorem cell23_1355653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1355653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355653 prefixEnd_1355653 := by exact prefixLift 1355653
  have htrace : WordTrace (prefixWord ++ tailWord_1355653) baseStart_1355653 baseEnd_1355653 := by
    simpa [prefixWord, tailWord_1355653, baseEnd_1355653] using wordTrace_append hprefix tailTrace_1355653
  have hstable : (prefixWord ++ tailWord_1355653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355653).length < 2 ^ (prefixWord ++ tailWord_1355653).sum := by decide
  have hdescent : baseEnd_1355653 < baseStart_1355653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355671 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_1355671 : Nat := 118140960795 + 1355671 * 2 ^ 59
def prefixEnd_1355671 : Nat := 4983230072969 + 3 ^ 40 * 1355671 * 2
def baseEnd_1355671 : Nat := 696110832361470664677889

theorem tailTrace_1355671 : CollatzResearch.WordTrace tailWord_1355671 prefixEnd_1355671 696110832361470664677889 := by
  unfold tailWord_1355671
  simp only [CollatzResearch.WordTrace]
  refine ⟨49445383471642972018850867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32963588981095314679233911 49445383471642972018850867)
  ·
    refine ⟨74168075207464458028276301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49445383471642972018850867 74168075207464458028276301)
    ·
      refine ⟨27813028202799171760603613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74168075207464458028276301 27813028202799171760603613)
      ·
        refine ⟨10429885576049689410226355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27813028202799171760603613 10429885576049689410226355)
        ·
          refine ⟨15644828364074534115339533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10429885576049689410226355 15644828364074534115339533)
          ·
            refine ⟨5866810636527950293252325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15644828364074534115339533 5866810636527950293252325)
            ·
              refine ⟨1100026994348990679984811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5866810636527950293252325 1100026994348990679984811)
              ·
                refine ⟨1650040491523486019977217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100026994348990679984811 1650040491523486019977217)
                ·
                  refine ⟨1237530368642614514982913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650040491523486019977217 1237530368642614514982913)
                  ·
                    refine ⟨928147776481960886237185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1237530368642614514982913 928147776481960886237185)
                    ·
                      refine ⟨696110832361470664677889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928147776481960886237185 696110832361470664677889)
                      ·
                        rfl

theorem cell23_1355671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_1355671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355671 prefixEnd_1355671 := by exact prefixLift 1355671
  have htrace : WordTrace (prefixWord ++ tailWord_1355671) baseStart_1355671 baseEnd_1355671 := by
    simpa [prefixWord, tailWord_1355671, baseEnd_1355671] using wordTrace_append hprefix tailTrace_1355671
  have hstable : (prefixWord ++ tailWord_1355671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355671).length < 2 ^ (prefixWord ++ tailWord_1355671).sum := by decide
  have hdescent : baseEnd_1355671 < baseStart_1355671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355673 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_1355673 : Nat := 118140960795 + 1355673 * 2 ^ 59
def prefixEnd_1355673 : Nat := 4983230072969 + 3 ^ 40 * 1355673 * 2
def baseEnd_1355673 : Nat := 232037286440926552284293

theorem tailTrace_1355673 : CollatzResearch.WordTrace tailWord_1355673 prefixEnd_1355673 232037286440926552284293 := by
  unfold tailWord_1355673
  simp only [CollatzResearch.WordTrace]
  refine ⟨49445456417635726360423673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32963637611757150906949115 49445456417635726360423673)
  ·
    refine ⟨37084092313226794770317755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49445456417635726360423673 37084092313226794770317755)
    ·
      refine ⟨55626138469840192155476633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37084092313226794770317755 55626138469840192155476633)
      ·
        refine ⟨41719603852380144116607475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55626138469840192155476633 41719603852380144116607475)
        ·
          refine ⟨62579405778570216174911213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41719603852380144116607475 62579405778570216174911213)
          ·
            refine ⟨23467277166963831065591705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62579405778570216174911213 23467277166963831065591705)
            ·
              refine ⟨17600457875222873299193779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23467277166963831065591705 17600457875222873299193779)
              ·
                refine ⟨26400686812834309948790669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17600457875222873299193779 26400686812834309948790669)
                ·
                  refine ⟨9900257554812866230796501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26400686812834309948790669 9900257554812866230796501)
                  ·
                    refine ⟨232037286440926552284293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9900257554812866230796501 232037286440926552284293)
                    ·
                      rfl

theorem cell23_1355673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_1355673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355673 prefixEnd_1355673 := by exact prefixLift 1355673
  have htrace : WordTrace (prefixWord ++ tailWord_1355673) baseStart_1355673 baseEnd_1355673 := by
    simpa [prefixWord, tailWord_1355673, baseEnd_1355673] using wordTrace_append hprefix tailTrace_1355673
  have hstable : (prefixWord ++ tailWord_1355673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355673).length < 2 ^ (prefixWord ++ tailWord_1355673).sum := by decide
  have hdescent : baseEnd_1355673 < baseStart_1355673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355683 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1355683 : Nat := 118140960795 + 1355683 * 2 ^ 59
def prefixEnd_1355683 : Nat := 4983230072969 + 3 ^ 40 * 1355683 * 2
def baseEnd_1355683 : Nat := 696116994129324617727833

theorem tailTrace_1355683 : CollatzResearch.WordTrace tailWord_1355683 prefixEnd_1355683 696116994129324617727833 := by
  unfold tailWord_1355683
  simp only [CollatzResearch.WordTrace]
  refine ⟨49445821147599498068287703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32963880765066332045525135 49445821147599498068287703)
  ·
    refine ⟨74168731721399247102431555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49445821147599498068287703 74168731721399247102431555)
    ·
      refine ⟨111253097582098870653647333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74168731721399247102431555 111253097582098870653647333)
      ·
        refine ⟨20859955796643538247558875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111253097582098870653647333 20859955796643538247558875)
        ·
          refine ⟨31289933694965307371338313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20859955796643538247558875 31289933694965307371338313)
          ·
            refine ⟨23467450271223980528503735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31289933694965307371338313 23467450271223980528503735)
            ·
              refine ⟨35201175406835970792755603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23467450271223980528503735 35201175406835970792755603)
              ·
                refine ⟨52801763110253956189133405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35201175406835970792755603 52801763110253956189133405)
                ·
                  refine ⟨19800661166345233570925027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52801763110253956189133405 19800661166345233570925027)
                  ·
                    refine ⟨29700991749517850356387541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19800661166345233570925027 29700991749517850356387541)
                    ·
                      refine ⟨696116994129324617727833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29700991749517850356387541 696116994129324617727833)
                      ·
                        rfl

theorem cell23_1355683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1355683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355683 prefixEnd_1355683 := by exact prefixLift 1355683
  have htrace : WordTrace (prefixWord ++ tailWord_1355683) baseStart_1355683 baseEnd_1355683 := by
    simpa [prefixWord, tailWord_1355683, baseEnd_1355683] using wordTrace_append hprefix tailTrace_1355683
  have hstable : (prefixWord ++ tailWord_1355683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355683).length < 2 ^ (prefixWord ++ tailWord_1355683).sum := by decide
  have hdescent : baseEnd_1355683 < baseStart_1355683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355727 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 4, 2]
def baseStart_1355727 : Nat := 118140960795 + 1355727 * 2 ^ 59
def prefixEnd_1355727 : Nat := 4983230072969 + 3 ^ 40 * 1355727 * 2
def baseEnd_1355727 : Nat := 696139587278122445577631

theorem tailTrace_1355727 : CollatzResearch.WordTrace tailWord_1355727 prefixEnd_1355727 696139587278122445577631 := by
  unfold tailWord_1355727
  simp only [CollatzResearch.WordTrace]
  refine ⟨49447425959440093582889435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32964950639626729055259623 49447425959440093582889435)
  ·
    refine ⟨74171138939160140374334153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49447425959440093582889435 74171138939160140374334153)
    ·
      refine ⟨55628354204370105280750615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74171138939160140374334153 55628354204370105280750615)
      ·
        refine ⟨83442531306555157921125923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55628354204370105280750615 83442531306555157921125923)
        ·
          refine ⟨125163796959832736881688885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83442531306555157921125923 125163796959832736881688885)
          ·
            refine ⟨11734105964984319082658333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125163796959832736881688885 11734105964984319082658333)
            ·
              refine ⟨4400289736869119655996875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11734105964984319082658333 4400289736869119655996875)
              ·
                refine ⟨6600434605303679483995313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400289736869119655996875 6600434605303679483995313)
                ·
                  refine ⟨4950325953977759612996485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600434605303679483995313 4950325953977759612996485)
                  ·
                    refine ⟨928186116370829927436841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4950325953977759612996485 928186116370829927436841)
                    ·
                      refine ⟨696139587278122445577631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928186116370829927436841 696139587278122445577631)
                      ·
                        rfl

theorem cell23_1355727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4, 2].length) (baseStart_1355727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355727 prefixEnd_1355727 := by exact prefixLift 1355727
  have htrace : WordTrace (prefixWord ++ tailWord_1355727) baseStart_1355727 baseEnd_1355727 := by
    simpa [prefixWord, tailWord_1355727, baseEnd_1355727] using wordTrace_append hprefix tailTrace_1355727
  have hstable : (prefixWord ++ tailWord_1355727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355727).length < 2 ^ (prefixWord ++ tailWord_1355727).sum := by decide
  have hdescent : baseEnd_1355727 < baseStart_1355727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355741 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1355741 : Nat := 118140960795 + 1355741 * 2 ^ 59
def prefixEnd_1355741 : Nat := 4983230072969 + 3 ^ 40 * 1355741 * 2
def baseEnd_1355741 : Nat := 232048925335761796934189

theorem tailTrace_1355741 : CollatzResearch.WordTrace tailWord_1355741 prefixEnd_1355741 232048925335761796934189 := by
  unfold tailWord_1355741
  simp only [CollatzResearch.WordTrace]
  refine ⟨49447936581389373973899077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32965291054259582649266051 49447936581389373973899077)
  ·
    refine ⟨9271488109010507620106077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49447936581389373973899077 9271488109010507620106077)
    ·
      refine ⟨3476808040878940357539779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9271488109010507620106077 3476808040878940357539779)
      ·
        refine ⟨5215212061318410536309669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476808040878940357539779 5215212061318410536309669)
        ·
          refine ⟨977852261497201975558063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5215212061318410536309669 977852261497201975558063)
          ·
            refine ⟨1466778392245802963337095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977852261497201975558063 1466778392245802963337095)
            ·
              refine ⟨2200167588368704445005643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466778392245802963337095 2200167588368704445005643)
              ·
                refine ⟨3300251382553056667508465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200167588368704445005643 3300251382553056667508465)
                ·
                  refine ⟨2475188536914792500631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300251382553056667508465 2475188536914792500631349)
                  ·
                    refine ⟨232048925335761796934189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2475188536914792500631349 232048925335761796934189)
                    ·
                      rfl

theorem cell23_1355741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1355741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355741 prefixEnd_1355741 := by exact prefixLift 1355741
  have htrace : WordTrace (prefixWord ++ tailWord_1355741) baseStart_1355741 baseEnd_1355741 := by
    simpa [prefixWord, tailWord_1355741, baseEnd_1355741] using wordTrace_append hprefix tailTrace_1355741
  have hstable : (prefixWord ++ tailWord_1355741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355741).length < 2 ^ (prefixWord ++ tailWord_1355741).sum := by decide
  have hdescent : baseEnd_1355741 < baseStart_1355741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355747 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1355747 : Nat := 118140960795 + 1355747 * 2 ^ 59
def prefixEnd_1355747 : Nat := 4983230072969 + 3 ^ 40 * 1355747 * 2
def baseEnd_1355747 : Nat := 696149856891212367327539

theorem tailTrace_1355747 : CollatzResearch.WordTrace tailWord_1355747 prefixEnd_1355747 696149856891212367327539 := by
  unfold tailWord_1355747
  simp only [CollatzResearch.WordTrace]
  refine ⟨49448155419367636998617495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32965436946245091332411663 49448155419367636998617495)
  ·
    refine ⟨74172233129051455497926243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49448155419367636998617495 74172233129051455497926243)
    ·
      refine ⟨111258349693577183246889365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74172233129051455497926243 111258349693577183246889365)
      ·
        refine ⟨5215235141886430464697939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111258349693577183246889365 5215235141886430464697939)
        ·
          refine ⟨7822852712829645697046909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215235141886430464697939 7822852712829645697046909)
          ·
            refine ⟨2933569767311117136392591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7822852712829645697046909 2933569767311117136392591)
            ·
              refine ⟨4400354650966675704588887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933569767311117136392591 4400354650966675704588887)
              ·
                refine ⟨6600531976450013556883331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400354650966675704588887 6600531976450013556883331)
                ·
                  refine ⟨9900797964675020335324997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600531976450013556883331 9900797964675020335324997)
                  ·
                    refine ⟨1856399618376566312873437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9900797964675020335324997 1856399618376566312873437)
                    ·
                      refine ⟨696149856891212367327539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856399618376566312873437 696149856891212367327539)
                      ·
                        rfl

theorem cell23_1355747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1355747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355747 prefixEnd_1355747 := by exact prefixLift 1355747
  have htrace : WordTrace (prefixWord ++ tailWord_1355747) baseStart_1355747 baseEnd_1355747 := by
    simpa [prefixWord, tailWord_1355747, baseEnd_1355747] using wordTrace_append hprefix tailTrace_1355747
  have hstable : (prefixWord ++ tailWord_1355747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355747).length < 2 ^ (prefixWord ++ tailWord_1355747).sum := by decide
  have hdescent : baseEnd_1355747 < baseStart_1355747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355787 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 5, 2]
def baseStart_1355787 : Nat := 118140960795 + 1355787 * 2 ^ 59
def prefixEnd_1355787 : Nat := 4983230072969 + 3 ^ 40 * 1355787 * 2
def baseEnd_1355787 : Nat := 696170396117392210827355

theorem tailTrace_1355787 : CollatzResearch.WordTrace tailWord_1355787 prefixEnd_1355787 696170396117392210827355 := by
  unfold tailWord_1355787
  simp only [CollatzResearch.WordTrace]
  refine ⟨49449614339222723830073615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32966409559481815886715743 49449614339222723830073615)
  ·
    refine ⟨74174421508834085745110423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49449614339222723830073615 74174421508834085745110423)
    ·
      refine ⟨111261632263251128617665635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74174421508834085745110423 111261632263251128617665635)
      ·
        refine ⟨166892448394876692926498453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111261632263251128617665635 166892448394876692926498453)
        ·
          refine ⟨7823083518509844980929615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166892448394876692926498453 7823083518509844980929615)
          ·
            refine ⟨11734625277764767471394423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823083518509844980929615 11734625277764767471394423)
            ·
              refine ⟨17601937916647151207091635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11734625277764767471394423 17601937916647151207091635)
              ·
                refine ⟨26402906874970726810637453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17601937916647151207091635 26402906874970726810637453)
                ·
                  refine ⟨9901090078114022553989045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26402906874970726810637453 9901090078114022553989045)
                  ·
                    refine ⟨928227194823189614436473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901090078114022553989045 928227194823189614436473)
                    ·
                      refine ⟨696170396117392210827355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928227194823189614436473 696170396117392210827355)
                      ·
                        rfl

theorem cell23_1355787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5, 2].length) (baseStart_1355787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355787 prefixEnd_1355787 := by exact prefixLift 1355787
  have htrace : WordTrace (prefixWord ++ tailWord_1355787) baseStart_1355787 baseEnd_1355787 := by
    simpa [prefixWord, tailWord_1355787, baseEnd_1355787] using wordTrace_append hprefix tailTrace_1355787
  have hstable : (prefixWord ++ tailWord_1355787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355787).length < 2 ^ (prefixWord ++ tailWord_1355787).sum := by decide
  have hdescent : baseEnd_1355787 < baseStart_1355787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355804 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1355804 : Nat := 118140960795 + 1355804 * 2 ^ 59
def prefixEnd_1355804 : Nat := 4983230072969 + 3 ^ 40 * 1355804 * 2
def baseEnd_1355804 : Nat := 696179125288518644314777

theorem tailTrace_1355804 : CollatzResearch.WordTrace tailWord_1355804 prefixEnd_1355804 696179125288518644314777 := by
  unfold tailWord_1355804
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725117190080567866721233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32966822920107423822294977 24725117190080567866721233)
  ·
    refine ⟨18543837892560425900040925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24725117190080567866721233 18543837892560425900040925)
    ·
      refine ⟨6953939209710159712515347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18543837892560425900040925 6953939209710159712515347)
      ·
        refine ⟨10430908814565239568773021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953939209710159712515347 10430908814565239568773021)
        ·
          refine ⟨3911590805461964838289883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10430908814565239568773021 3911590805461964838289883)
          ·
            refine ⟨5867386208192947257434825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911590805461964838289883 5867386208192947257434825)
            ·
              refine ⟨4400539656144710443076119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867386208192947257434825 4400539656144710443076119)
              ·
                refine ⟨6600809484217065664614179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400539656144710443076119 6600809484217065664614179)
                ·
                  refine ⟨9901214226325598496921269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600809484217065664614179 9901214226325598496921269)
                  ·
                    refine ⟨928238833718024859086369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901214226325598496921269 928238833718024859086369)
                    ·
                      refine ⟨696179125288518644314777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928238833718024859086369 696179125288518644314777)
                      ·
                        rfl

theorem cell23_1355804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1355804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355804 prefixEnd_1355804 := by exact prefixLift 1355804
  have htrace : WordTrace (prefixWord ++ tailWord_1355804) baseStart_1355804 baseEnd_1355804 := by
    simpa [prefixWord, tailWord_1355804, baseEnd_1355804] using wordTrace_append hprefix tailTrace_1355804
  have hstable : (prefixWord ++ tailWord_1355804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355804).length < 2 ^ (prefixWord ++ tailWord_1355804).sum := by decide
  have hdescent : baseEnd_1355804 < baseStart_1355804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355827 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 4, 4]
def baseStart_1355827 : Nat := 118140960795 + 1355827 * 2 ^ 59
def prefixEnd_1355827 : Nat := 4983230072969 + 3 ^ 40 * 1355827 * 2
def baseEnd_1355827 : Nat := 232063645114524018109057

theorem tailTrace_1355827 : CollatzResearch.WordTrace tailWord_1355827 prefixEnd_1355827 232063645114524018109057 := by
  unfold tailWord_1355827
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451073259077810661529735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32967382172718540441019823 49451073259077810661529735)
  ·
    refine ⟨74176609888616715992294603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49451073259077810661529735 74176609888616715992294603)
    ·
      refine ⟨111264914832925073988441905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74176609888616715992294603 111264914832925073988441905)
      ·
        refine ⟨83448686124693805491331429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111264914832925073988441905 83448686124693805491331429)
        ·
          refine ⟨15646628648380088529624643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83448686124693805491331429 15646628648380088529624643)
          ·
            refine ⟨23469942972570132794436965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15646628648380088529624643 23469942972570132794436965)
            ·
              refine ⟨4400614307356899898956931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23469942972570132794436965 4400614307356899898956931)
              ·
                refine ⟨6600921461035349848435397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400614307356899898956931 6600921461035349848435397)
                ·
                  refine ⟨1237672773944128096581637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6600921461035349848435397 1237672773944128096581637)
                  ·
                    refine ⟨232063645114524018109057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237672773944128096581637 232063645114524018109057)
                    ·
                      rfl

theorem cell23_1355827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 4].length) (baseStart_1355827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355827 prefixEnd_1355827 := by exact prefixLift 1355827
  have htrace : WordTrace (prefixWord ++ tailWord_1355827) baseStart_1355827 baseEnd_1355827 := by
    simpa [prefixWord, tailWord_1355827, baseEnd_1355827] using wordTrace_append hprefix tailTrace_1355827
  have hstable : (prefixWord ++ tailWord_1355827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355827).length < 2 ^ (prefixWord ++ tailWord_1355827).sum := by decide
  have hdescent : baseEnd_1355827 < baseStart_1355827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355837 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1355837 : Nat := 118140960795 + 1355837 * 2 ^ 59
def prefixEnd_1355837 : Nat := 4983230072969 + 3 ^ 40 * 1355837 * 2
def baseEnd_1355837 : Nat := 696196070150117015202125

theorem tailTrace_1355837 : CollatzResearch.WordTrace tailWord_1355837 prefixEnd_1355837 696196070150117015202125 := by
  unfold tailWord_1355837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451437989041582369393765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32967625326027721579595843 49451437989041582369393765)
  ·
    refine ⟨9272144622945296694261331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49451437989041582369393765 9272144622945296694261331)
    ·
      refine ⟨13908216934417945041391997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272144622945296694261331 13908216934417945041391997)
      ·
        refine ⟨5215581350406729390521999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13908216934417945041391997 5215581350406729390521999)
        ·
          refine ⟨7823372025610094085782999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215581350406729390521999 7823372025610094085782999)
          ·
            refine ⟨11735058038415141128674499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823372025610094085782999 11735058038415141128674499)
            ·
              refine ⟨17602587057622711693011749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11735058038415141128674499 17602587057622711693011749)
              ·
                refine ⟨3300485073304258442439703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17602587057622711693011749 3300485073304258442439703)
                ·
                  refine ⟨4950727609956387663659555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300485073304258442439703 4950727609956387663659555)
                  ·
                    refine ⟨7426091414934581495489333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950727609956387663659555 7426091414934581495489333)
                    ·
                      refine ⟨696196070150117015202125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7426091414934581495489333 696196070150117015202125)
                      ·
                        rfl

theorem cell23_1355837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1355837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355837 prefixEnd_1355837 := by exact prefixLift 1355837
  have htrace : WordTrace (prefixWord ++ tailWord_1355837) baseStart_1355837 baseEnd_1355837 := by
    simpa [prefixWord, tailWord_1355837, baseEnd_1355837] using wordTrace_append hprefix tailTrace_1355837
  have hstable : (prefixWord ++ tailWord_1355837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355837).length < 2 ^ (prefixWord ++ tailWord_1355837).sum := by decide
  have hdescent : baseEnd_1355837 < baseStart_1355837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355840 : List Nat := [2, 1, 1, 2, 2, 4, 1, 10]
def baseStart_1355840 : Nat := 118140960795 + 1355840 * 2 ^ 59
def prefixEnd_1355840 : Nat := 4983230072969 + 3 ^ 40 * 1355840 * 2
def baseEnd_1355840 : Nat := 25785096688595574202393

theorem tailTrace_1355840 : CollatzResearch.WordTrace tailWord_1355840 prefixEnd_1355840 25785096688595574202393 := by
  unfold tailWord_1355840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725773704015356940876487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32967698272020475921168649 24725773704015356940876487)
  ·
    refine ⟨37088660556023035411314731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24725773704015356940876487 37088660556023035411314731)
    ·
      refine ⟨55632990834034553116972097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37088660556023035411314731 55632990834034553116972097)
      ·
        refine ⟨41724743125525914837729073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55632990834034553116972097 41724743125525914837729073)
        ·
          refine ⟨31293557344144436128296805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41724743125525914837729073 31293557344144436128296805)
          ·
            refine ⟨5867542002027081774055651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31293557344144436128296805 5867542002027081774055651)
            ·
              refine ⟨8801313003040622661083477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867542002027081774055651 8801313003040622661083477)
              ·
                refine ⟨25785096688595574202393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8801313003040622661083477 25785096688595574202393)
                ·
                  rfl

theorem cell23_1355840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_1355840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355840 prefixEnd_1355840 := by exact prefixLift 1355840
  have htrace : WordTrace (prefixWord ++ tailWord_1355840) baseStart_1355840 baseEnd_1355840 := by
    simpa [prefixWord, tailWord_1355840, baseEnd_1355840] using wordTrace_append hprefix tailTrace_1355840
  have hstable : (prefixWord ++ tailWord_1355840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355840).length < 2 ^ (prefixWord ++ tailWord_1355840).sum := by decide
  have hdescent : baseEnd_1355840 < baseStart_1355840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355847 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1355847 : Nat := 118140960795 + 1355847 * 2 ^ 59
def prefixEnd_1355847 : Nat := 4983230072969 + 3 ^ 40 * 1355847 * 2
def baseEnd_1355847 : Nat := 696201204956661976077079

theorem tailTrace_1355847 : CollatzResearch.WordTrace tailWord_1355847 prefixEnd_1355847 696201204956661976077079 := by
  unfold tailWord_1355847
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451802719005354077257795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32967868479336902718171863 49451802719005354077257795)
  ·
    refine ⟨74177704078508031115886693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49451802719005354077257795 74177704078508031115886693)
    ·
      refine ⟨13908319514720255834228755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74177704078508031115886693 13908319514720255834228755)
      ·
        refine ⟨20862479272080383751343133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13908319514720255834228755 20862479272080383751343133)
        ·
          refine ⟨7823429727030143906753675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20862479272080383751343133 7823429727030143906753675)
          ·
            refine ⟨11735144590545215860130513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823429727030143906753675 11735144590545215860130513)
            ·
              refine ⟨8801358442908911895097885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11735144590545215860130513 8801358442908911895097885)
              ·
                refine ⟨3300509416090841960661707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8801358442908911895097885 3300509416090841960661707)
                ·
                  refine ⟨4950764124136262940992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300509416090841960661707 4950764124136262940992561)
                  ·
                    refine ⟨3713073093102197205744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4950764124136262940992561 3713073093102197205744421)
                    ·
                      refine ⟨696201204956661976077079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3713073093102197205744421 696201204956661976077079)
                      ·
                        rfl

theorem cell23_1355847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1355847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355847 prefixEnd_1355847 := by exact prefixLift 1355847
  have htrace : WordTrace (prefixWord ++ tailWord_1355847) baseStart_1355847 baseEnd_1355847 := by
    simpa [prefixWord, tailWord_1355847, baseEnd_1355847] using wordTrace_append hprefix tailTrace_1355847
  have hstable : (prefixWord ++ tailWord_1355847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355847).length < 2 ^ (prefixWord ++ tailWord_1355847).sum := by decide
  have hdescent : baseEnd_1355847 < baseStart_1355847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355854 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1355854 : Nat := 118140960795 + 1355854 * 2 ^ 59
def prefixEnd_1355854 : Nat := 4983230072969 + 3 ^ 40 * 1355854 * 2
def baseEnd_1355854 : Nat := 696204799321243448689547

theorem tailTrace_1355854 : CollatzResearch.WordTrace tailWord_1355854 prefixEnd_1355854 696204799321243448689547 := by
  unfold tailWord_1355854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181507253747499284095327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32968038686653329515175077 6181507253747499284095327)
  ·
    refine ⟨9272260880621248926142991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6181507253747499284095327 9272260880621248926142991)
    ·
      refine ⟨13908391320931873389214487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272260880621248926142991 13908391320931873389214487)
      ·
        refine ⟨20862586981397810083821731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13908391320931873389214487 20862586981397810083821731)
        ·
          refine ⟨31293880472096715125732597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20862586981397810083821731 31293880472096715125732597)
          ·
            refine ⟨2933801294259067043037431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31293880472096715125732597 2933801294259067043037431)
            ·
              refine ⟨4400701941388600564556147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933801294259067043037431 4400701941388600564556147)
              ·
                refine ⟨6601052912082900846834221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400701941388600564556147 6601052912082900846834221)
                ·
                  refine ⟨2475394842031087817562833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6601052912082900846834221 2475394842031087817562833)
                  ·
                    refine ⟨1856546131523315863172125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475394842031087817562833 1856546131523315863172125)
                    ·
                      refine ⟨696204799321243448689547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856546131523315863172125 696204799321243448689547)
                      ·
                        rfl

theorem cell23_1355854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1355854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355854 prefixEnd_1355854 := by exact prefixLift 1355854
  have htrace : WordTrace (prefixWord ++ tailWord_1355854) baseStart_1355854 baseEnd_1355854 := by
    simpa [prefixWord, tailWord_1355854, baseEnd_1355854] using wordTrace_append hprefix tailTrace_1355854
  have hstable : (prefixWord ++ tailWord_1355854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355854).length < 2 ^ (prefixWord ++ tailWord_1355854).sum := by decide
  have hdescent : baseEnd_1355854 < baseStart_1355854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355874 : List Nat := [3, 3, 2, 2, 3, 10]
def baseStart_1355874 : Nat := 118140960795 + 1355874 * 2 ^ 59
def prefixEnd_1355874 : Nat := 4983230072969 + 3 ^ 40 * 1355874 * 2
def baseEnd_1355874 : Nat := 2865082588207133211685

theorem tailTrace_1355874 : CollatzResearch.WordTrace tailWord_1355874 prefixEnd_1355874 2865082588207133211685 := by
  unfold tailWord_1355874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363196872476884422122669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32968524993271691792327117 12363196872476884422122669)
  ·
    refine ⟨4636198827178831658296001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12363196872476884422122669 4636198827178831658296001)
    ·
      refine ⟨3477149120384123743722001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4636198827178831658296001 3477149120384123743722001)
      ·
        refine ⟨2607861840288092807791501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477149120384123743722001 2607861840288092807791501)
        ·
          refine ⟨977948190108034802921813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2607861840288092807791501 977948190108034802921813)
          ·
            refine ⟨2865082588207133211685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 977948190108034802921813 2865082588207133211685)
            ·
              rfl

theorem cell23_1355874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 10].length) (baseStart_1355874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355874 prefixEnd_1355874 := by exact prefixLift 1355874
  have htrace : WordTrace (prefixWord ++ tailWord_1355874) baseStart_1355874 baseEnd_1355874 := by
    simpa [prefixWord, tailWord_1355874, baseEnd_1355874] using wordTrace_append hprefix tailTrace_1355874
  have hstable : (prefixWord ++ tailWord_1355874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355874).length < 2 ^ (prefixWord ++ tailWord_1355874).sum := by decide
  have hdescent : baseEnd_1355874 < baseStart_1355874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355901 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1355901 : Nat := 118140960795 + 1355901 * 2 ^ 59
def prefixEnd_1355901 : Nat := 4983230072969 + 3 ^ 40 * 1355901 * 2
def baseEnd_1355901 : Nat := 696228932912004764801831

theorem tailTrace_1355901 : CollatzResearch.WordTrace tailWord_1355901 prefixEnd_1355901 696228932912004764801831 := by
  unfold tailWord_1355901
  simp only [CollatzResearch.WordTrace]
  refine ⟨49453772260809721299723557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32969181507206480866482371 49453772260809721299723557)
  ·
    refine ⟨9272582298901822743698167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49453772260809721299723557 9272582298901822743698167)
    ·
      refine ⟨13908873448352734115547251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272582298901822743698167 13908873448352734115547251)
      ·
        refine ⟨20863310172529101173320877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13908873448352734115547251 20863310172529101173320877)
        ·
          refine ⟨7823741314698412939995329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20863310172529101173320877 7823741314698412939995329)
          ·
            refine ⟨5867805986023809704996497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7823741314698412939995329 5867805986023809704996497)
            ·
              refine ⟨4400854489517857278747373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867805986023809704996497 4400854489517857278747373)
              ·
                refine ⟨1650320433569196479530265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4400854489517857278747373 1650320433569196479530265)
                ·
                  refine ⟨1237740325176897359647699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650320433569196479530265 1237740325176897359647699)
                  ·
                    refine ⟨1856610487765346039471549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237740325176897359647699 1856610487765346039471549)
                    ·
                      refine ⟨696228932912004764801831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1856610487765346039471549 696228932912004764801831)
                      ·
                        rfl

theorem cell23_1355901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1355901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355901 prefixEnd_1355901 := by exact prefixLift 1355901
  have htrace : WordTrace (prefixWord ++ tailWord_1355901) baseStart_1355901 baseEnd_1355901 := by
    simpa [prefixWord, tailWord_1355901, baseEnd_1355901] using wordTrace_append hprefix tailTrace_1355901
  have hstable : (prefixWord ++ tailWord_1355901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355901).length < 2 ^ (prefixWord ++ tailWord_1355901).sum := by decide
  have hdescent : baseEnd_1355901 < baseStart_1355901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355928 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1355928 : Nat := 118140960795 + 1355928 * 2 ^ 59
def prefixEnd_1355928 : Nat := 4983230072969 + 3 ^ 40 * 1355928 * 2
def baseEnd_1355928 : Nat := 696242796889676159164207

theorem tailTrace_1355928 : CollatzResearch.WordTrace tailWord_1355928 prefixEnd_1355928 696242796889676159164207 := by
  unfold tailWord_1355928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24727378515855952455478219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32969838021141269940637625 24727378515855952455478219)
  ·
    refine ⟨37091067773783928683217329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24727378515855952455478219 37091067773783928683217329)
    ·
      refine ⟨27818300830337946512412997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37091067773783928683217329 27818300830337946512412997)
      ·
        refine ⟨5215931405688364971077437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27818300830337946512412997 5215931405688364971077437)
        ·
          refine ⟨1955974277133136864154039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5215931405688364971077437 1955974277133136864154039)
          ·
            refine ⟨2933961415699705296231059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955974277133136864154039 2933961415699705296231059)
            ·
              refine ⟨4400942123549557944346589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933961415699705296231059 4400942123549557944346589)
              ·
                refine ⟨1650353296331084229129971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4400942123549557944346589 1650353296331084229129971)
                ·
                  refine ⟨2475529944496626343694957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650353296331084229129971 2475529944496626343694957)
                  ·
                    refine ⟨928323729186234878885609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475529944496626343694957 928323729186234878885609)
                    ·
                      refine ⟨696242796889676159164207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928323729186234878885609 696242796889676159164207)
                      ·
                        rfl

theorem cell23_1355928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1355928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355928 prefixEnd_1355928 := by exact prefixLift 1355928
  have htrace : WordTrace (prefixWord ++ tailWord_1355928) baseStart_1355928 baseEnd_1355928 := by
    simpa [prefixWord, tailWord_1355928, baseEnd_1355928] using wordTrace_append hprefix tailTrace_1355928
  have hstable : (prefixWord ++ tailWord_1355928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355928).length < 2 ^ (prefixWord ++ tailWord_1355928).sum := by decide
  have hdescent : baseEnd_1355928 < baseStart_1355928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355941 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_1355941 : Nat := 118140960795 + 1355941 * 2 ^ 59
def prefixEnd_1355941 : Nat := 4983230072969 + 3 ^ 40 * 1355941 * 2
def baseEnd_1355941 : Nat := 696249472138184608301647

theorem tailTrace_1355941 : CollatzResearch.WordTrace tailWord_1355941 prefixEnd_1355941 696249472138184608301647 := by
  unfold tailWord_1355941
  simp only [CollatzResearch.WordTrace]
  refine ⟨49455231180664808131179677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32970154120443205420786451 49455231180664808131179677)
  ·
    refine ⟨18545711692749303049192379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49455231180664808131179677 18545711692749303049192379)
    ·
      refine ⟨27818567539123954573788569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18545711692749303049192379 27818567539123954573788569)
      ·
        refine ⟨20863925654342965930341427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27818567539123954573788569 20863925654342965930341427)
        ·
          refine ⟨31295888481514448895512141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20863925654342965930341427 31295888481514448895512141)
          ·
            refine ⟨11735958180567918335817053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31295888481514448895512141 11735958180567918335817053)
            ·
              refine ⟨4400984317712969375931395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11735958180567918335817053 4400984317712969375931395)
              ·
                refine ⟨6601476476569454063897093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400984317712969375931395 6601476476569454063897093)
                ·
                  refine ⟨1237776839356772636980705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6601476476569454063897093 1237776839356772636980705)
                  ·
                    refine ⟨928332629517579477735529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1237776839356772636980705 928332629517579477735529)
                    ·
                      refine ⟨696249472138184608301647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928332629517579477735529 696249472138184608301647)
                      ·
                        rfl

theorem cell23_1355941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_1355941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1355941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1355941 prefixEnd_1355941 := by exact prefixLift 1355941
  have htrace : WordTrace (prefixWord ++ tailWord_1355941) baseStart_1355941 baseEnd_1355941 := by
    simpa [prefixWord, tailWord_1355941, baseEnd_1355941] using wordTrace_append hprefix tailTrace_1355941
  have hstable : (prefixWord ++ tailWord_1355941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355941).length < 2 ^ (prefixWord ++ tailWord_1355941).sum := by decide
  have hdescent : baseEnd_1355941 < baseStart_1355941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356014 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1356014 : Nat := 118140960795 + 1356014 * 2 ^ 59
def prefixEnd_1356014 : Nat := 4983230072969 + 3 ^ 40 * 1356014 * 2
def baseEnd_1356014 : Nat := 696286956225962822688811

theorem tailTrace_1356014 : CollatzResearch.WordTrace tailWord_1356014 prefixEnd_1356014 696286956225962822688811 := by
  unfold tailWord_1356014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182236713675042699823387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32971929139600227732391397 6182236713675042699823387)
  ·
    refine ⟨9273355070512564049735081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6182236713675042699823387 9273355070512564049735081)
    ·
      refine ⟨6955016302884423037301311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9273355070512564049735081 6955016302884423037301311)
      ·
        refine ⟨10432524454326634555951967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955016302884423037301311 10432524454326634555951967)
        ·
          refine ⟨15648786681489951833927951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10432524454326634555951967 15648786681489951833927951)
          ·
            refine ⟨23473180022234927750891927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15648786681489951833927951 23473180022234927750891927)
            ·
              refine ⟨35209770033352391626337891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23473180022234927750891927 35209770033352391626337891)
              ·
                refine ⟨52814655050028587439506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35209770033352391626337891 52814655050028587439506837)
                ·
                  refine ⟨2475686955470090036226883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52814655050028587439506837 2475686955470090036226883)
                  ·
                    refine ⟨3713530433205135054340325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2475686955470090036226883 3713530433205135054340325)
                    ·
                      refine ⟨696286956225962822688811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3713530433205135054340325 696286956225962822688811)
                      ·
                        rfl

theorem cell23_1356014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1356014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356014 prefixEnd_1356014 := by exact prefixLift 1356014
  have htrace : WordTrace (prefixWord ++ tailWord_1356014) baseStart_1356014 baseEnd_1356014 := by
    simpa [prefixWord, tailWord_1356014, baseEnd_1356014] using wordTrace_append hprefix tailTrace_1356014
  have hstable : (prefixWord ++ tailWord_1356014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356014).length < 2 ^ (prefixWord ++ tailWord_1356014).sum := by decide
  have hdescent : baseEnd_1356014 < baseStart_1356014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356024 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_1356024 : Nat := 118140960795 + 1356024 * 2 ^ 59
def prefixEnd_1356024 : Nat := 4983230072969 + 3 ^ 40 * 1356024 * 2
def baseEnd_1356024 : Nat := 232097363677502594521255

theorem tailTrace_1356024 : CollatzResearch.WordTrace tailWord_1356024 prefixEnd_1356024 232097363677502594521255 := by
  unfold tailWord_1356024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24729129219682056653225563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32972172292909408870967417 24729129219682056653225563)
  ·
    refine ⟨37093693829523084979838345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24729129219682056653225563 37093693829523084979838345)
    ·
      refine ⟨27820270372142313734878759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37093693829523084979838345 27820270372142313734878759)
      ·
        refine ⟨41730405558213470602318139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27820270372142313734878759 41730405558213470602318139)
        ·
          refine ⟨62595608337320205903477209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41730405558213470602318139 62595608337320205903477209)
          ·
            refine ⟨46946706252990154427607907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62595608337320205903477209 46946706252990154427607907)
            ·
              refine ⟨70420059379485231641411861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46946706252990154427607907 70420059379485231641411861)
              ·
                refine ⟨3300940283413370233191181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70420059379485231641411861 3300940283413370233191181)
                ·
                  refine ⟨1237852606280013837446693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3300940283413370233191181 1237852606280013837446693)
                  ·
                    refine ⟨232097363677502594521255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237852606280013837446693 232097363677502594521255)
                    ·
                      rfl

theorem cell23_1356024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_1356024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356024 prefixEnd_1356024 := by exact prefixLift 1356024
  have htrace : WordTrace (prefixWord ++ tailWord_1356024) baseStart_1356024 baseEnd_1356024 := by
    simpa [prefixWord, tailWord_1356024, baseEnd_1356024] using wordTrace_append hprefix tailTrace_1356024
  have hstable : (prefixWord ++ tailWord_1356024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356024).length < 2 ^ (prefixWord ++ tailWord_1356024).sum := by decide
  have hdescent : baseEnd_1356024 < baseStart_1356024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356037 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 8]
def baseStart_1356037 : Nat := 118140960795 + 1356037 * 2 ^ 59
def prefixEnd_1356037 : Nat := 4983230072969 + 3 ^ 40 * 1356037 * 2
def baseEnd_1356037 : Nat := 77366529586779581411245

theorem tailTrace_1356037 : CollatzResearch.WordTrace tailWord_1356037 prefixEnd_1356037 77366529586779581411245 := by
  unfold tailWord_1356037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49458732588317016526674365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32972488392211344351116243 49458732588317016526674365)
  ·
    refine ⟨18547024720618881197502887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49458732588317016526674365 18547024720618881197502887)
    ·
      refine ⟨27820537080928321796254331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18547024720618881197502887 27820537080928321796254331)
      ·
        refine ⟨41730805621392482694381497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27820537080928321796254331 41730805621392482694381497)
        ·
          refine ⟨31298104216044362020786123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41730805621392482694381497 31298104216044362020786123)
          ·
            refine ⟨46947156324066543031179185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31298104216044362020786123 46947156324066543031179185)
            ·
              refine ⟨35210367243049907273384389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46947156324066543031179185 35210367243049907273384389)
              ·
                refine ⟨6601943858071857613759573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35210367243049907273384389 6601943858071857613759573)
                ·
                  refine ⟨77366529586779581411245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6601943858071857613759573 77366529586779581411245)
                  ·
                    rfl

theorem cell23_1356037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_1356037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356037 prefixEnd_1356037 := by exact prefixLift 1356037
  have htrace : WordTrace (prefixWord ++ tailWord_1356037) baseStart_1356037 baseEnd_1356037 := by
    simpa [prefixWord, tailWord_1356037, baseEnd_1356037] using wordTrace_append hprefix tailTrace_1356037
  have hstable : (prefixWord ++ tailWord_1356037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356037).length < 2 ^ (prefixWord ++ tailWord_1356037).sum := by decide
  have hdescent : baseEnd_1356037 < baseStart_1356037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356114 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1356114 : Nat := 118140960795 + 1356114 * 2 ^ 59
def prefixEnd_1356114 : Nat := 4983230072969 + 3 ^ 40 * 1356114 * 2
def baseEnd_1356114 : Nat := 232112768097137477146117

theorem tailTrace_1356114 : CollatzResearch.WordTrace tailWord_1356114 prefixEnd_1356114 232112768097137477146117 := by
  unfold tailWord_1356114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365385252259514669306849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32974360672692039118151597 12365385252259514669306849)
  ·
    refine ⟨9274038939194636001980137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12365385252259514669306849 9274038939194636001980137)
    ·
      refine ⟨6955529204395977001485103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9274038939194636001980137 6955529204395977001485103)
      ·
        refine ⟨10433293806593965502227655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955529204395977001485103 10433293806593965502227655)
        ·
          refine ⟨15649940709890948253341483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433293806593965502227655 15649940709890948253341483)
          ·
            refine ⟨23474911064836422380012225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15649940709890948253341483 23474911064836422380012225)
            ·
              refine ⟨17606183298627316785009169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23474911064836422380012225 17606183298627316785009169)
              ·
                refine ⟨13204637473970487588756877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17606183298627316785009169 13204637473970487588756877)
                ·
                  refine ⟨4951739052738932845783829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13204637473970487588756877 4951739052738932845783829)
                  ·
                    refine ⟨232112768097137477146117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4951739052738932845783829 232112768097137477146117)
                    ·
                      rfl

theorem cell23_1356114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1356114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356114 prefixEnd_1356114 := by exact prefixLift 1356114
  have htrace : WordTrace (prefixWord ++ tailWord_1356114) baseStart_1356114 baseEnd_1356114 := by
    simpa [prefixWord, tailWord_1356114, baseEnd_1356114] using wordTrace_append hprefix tailTrace_1356114
  have hstable : (prefixWord ++ tailWord_1356114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356114).length < 2 ^ (prefixWord ++ tailWord_1356114).sum := by decide
  have hdescent : baseEnd_1356114 < baseStart_1356114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356138 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1356138 : Nat := 118140960795 + 1356138 * 2 ^ 59
def prefixEnd_1356138 : Nat := 4983230072969 + 3 ^ 40 * 1356138 * 2
def baseEnd_1356138 : Nat := 696350627827120337538241

theorem tailTrace_1356138 : CollatzResearch.WordTrace tailWord_1356138 prefixEnd_1356138 696350627827120337538241 := by
  unfold tailWord_1356138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365604090237777694025267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32974944240634073850734045 12365604090237777694025267)
  ·
    refine ⟨18548406135356666541037901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12365604090237777694025267 18548406135356666541037901)
    ·
      refine ⟨6955652300758749952889213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18548406135356666541037901 6955652300758749952889213)
      ·
        refine ⟨2608369612784531232333455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6955652300758749952889213 2608369612784531232333455)
        ·
          refine ⟨3912554419176796848500183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608369612784531232333455 3912554419176796848500183)
          ·
            refine ⟨5868831628765195272750275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912554419176796848500183 5868831628765195272750275)
            ·
              refine ⟨8803247443147792909125413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868831628765195272750275 8803247443147792909125413)
              ·
                refine ⟨1650608895590211170461015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8803247443147792909125413 1650608895590211170461015)
                ·
                  refine ⟨2475913343385316755691523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650608895590211170461015 2475913343385316755691523)
                  ·
                    refine ⟨3713870015077975133537285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2475913343385316755691523 3713870015077975133537285)
                    ·
                      refine ⟨696350627827120337538241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3713870015077975133537285 696350627827120337538241)
                      ·
                        rfl

theorem cell23_1356138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1356138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356138 prefixEnd_1356138 := by exact prefixLift 1356138
  have htrace : WordTrace (prefixWord ++ tailWord_1356138) baseStart_1356138 baseEnd_1356138 := by
    simpa [prefixWord, tailWord_1356138, baseEnd_1356138] using wordTrace_append hprefix tailTrace_1356138
  have hstable : (prefixWord ++ tailWord_1356138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356138).length < 2 ^ (prefixWord ++ tailWord_1356138).sum := by decide
  have hdescent : baseEnd_1356138 < baseStart_1356138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356144 : List Nat := [2, 1, 1, 1, 4, 4, 1, 9]
def baseStart_1356144 : Nat := 118140960795 + 1356144 * 2 ^ 59
def prefixEnd_1356144 : Nat := 4983230072969 + 3 ^ 40 * 1356144 * 2
def baseEnd_1356144 : Nat := 25790878100409159780119

theorem tailTrace_1356144 : CollatzResearch.WordTrace tailWord_1356144 prefixEnd_1356144 25790878100409159780119 := by
  unfold tailWord_1356144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731317599464686900409743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32975090132619582533879657 24731317599464686900409743)
  ·
    refine ⟨37096976399197030350614615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24731317599464686900409743 37096976399197030350614615)
    ·
      refine ⟨55645464598795545525921923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37096976399197030350614615 55645464598795545525921923)
      ·
        refine ⟨83468196898193318288882885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55645464598795545525921923 83468196898193318288882885)
        ·
          refine ⟨15650286918411247179165541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83468196898193318288882885 15650286918411247179165541)
          ·
            refine ⟨2934428797202108846093539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15650286918411247179165541 2934428797202108846093539)
            ·
              refine ⟨4401643195803163269140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934428797202108846093539 4401643195803163269140309)
              ·
                refine ⟨25790878100409159780119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4401643195803163269140309 25790878100409159780119)
                ·
                  rfl

theorem cell23_1356144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_1356144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356144 prefixEnd_1356144 := by exact prefixLift 1356144
  have htrace : WordTrace (prefixWord ++ tailWord_1356144) baseStart_1356144 baseEnd_1356144 := by
    simpa [prefixWord, tailWord_1356144, baseEnd_1356144] using wordTrace_append hprefix tailTrace_1356144
  have hstable : (prefixWord ++ tailWord_1356144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356144).length < 2 ^ (prefixWord ++ tailWord_1356144).sum := by decide
  have hdescent : baseEnd_1356144 < baseStart_1356144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356161 : List Nat := [1, 2, 4, 3, 1, 3, 9]
def baseStart_1356161 : Nat := 118140960795 + 1356161 * 2 ^ 59
def prefixEnd_1356161 : Nat := 4983230072969 + 3 ^ 40 * 1356161 * 2
def baseEnd_1356161 : Nat := 8597067134347824043835

theorem tailTrace_1356161 : CollatzResearch.WordTrace tailWord_1356161 prefixEnd_1356161 8597067134347824043835 := by
  unfold tailWord_1356161
  simp only [CollatzResearch.WordTrace]
  refine ⟨49463255239867785704188337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32975503493245190469458891 49463255239867785704188337)
  ·
    refine ⟨37097441429900839278141253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49463255239867785704188337 37097441429900839278141253)
    ·
      refine ⟨6955770268106407364651485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37097441429900839278141253 6955770268106407364651485)
      ·
        refine ⟨2608413850539902761744307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6955770268106407364651485 2608413850539902761744307)
        ·
          refine ⟨3912620775809854142616461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608413850539902761744307 3912620775809854142616461)
          ·
            refine ⟨1467232790928695303481173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3912620775809854142616461 1467232790928695303481173)
            ·
              refine ⟨8597067134347824043835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1467232790928695303481173 8597067134347824043835)
              ·
                rfl

theorem cell23_1356161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 9].length) (baseStart_1356161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356161 prefixEnd_1356161 := by exact prefixLift 1356161
  have htrace : WordTrace (prefixWord ++ tailWord_1356161) baseStart_1356161 baseEnd_1356161 := by
    simpa [prefixWord, tailWord_1356161, baseEnd_1356161] using wordTrace_append hprefix tailTrace_1356161
  have hstable : (prefixWord ++ tailWord_1356161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356161).length < 2 ^ (prefixWord ++ tailWord_1356161).sum := by decide
  have hdescent : baseEnd_1356161 < baseStart_1356161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356181 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_1356181 : Nat := 118140960795 + 1356181 * 2 ^ 59
def prefixEnd_1356181 : Nat := 4983230072969 + 3 ^ 40 * 1356181 * 2
def baseEnd_1356181 : Nat := 696372707495263669300543

theorem tailTrace_1356181 : CollatzResearch.WordTrace tailWord_1356181 prefixEnd_1356181 696372707495263669300543 := by
  unfold tailWord_1356181
  simp only [CollatzResearch.WordTrace]
  refine ⟨49463984699795329119916397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32975989799863552746610931 49463984699795329119916397)
  ·
    refine ⟨18548994262423248419968649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49463984699795329119916397 18548994262423248419968649)
    ·
      refine ⟨13911745696817436314976487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18548994262423248419968649 13911745696817436314976487)
      ·
        refine ⟨20867618545226154472464731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911745696817436314976487 20867618545226154472464731)
        ·
          refine ⟨31301427817839231708697097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20867618545226154472464731 31301427817839231708697097)
          ·
            refine ⟨23476070863379423781522823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31301427817839231708697097 23476070863379423781522823)
            ·
              refine ⟨35214106295069135672284235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23476070863379423781522823 35214106295069135672284235)
              ·
                refine ⟨52821159442603703508426353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35214106295069135672284235 52821159442603703508426353)
                ·
                  refine ⟨39615869581952777631319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52821159442603703508426353 39615869581952777631319765)
                  ·
                    refine ⟨928496943327018225734057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39615869581952777631319765 928496943327018225734057)
                    ·
                      refine ⟨696372707495263669300543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928496943327018225734057 696372707495263669300543)
                      ·
                        rfl

theorem cell23_1356181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_1356181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356181 prefixEnd_1356181 := by exact prefixLift 1356181
  have htrace : WordTrace (prefixWord ++ tailWord_1356181) baseStart_1356181 baseEnd_1356181 := by
    simpa [prefixWord, tailWord_1356181, baseEnd_1356181] using wordTrace_append hprefix tailTrace_1356181
  have hstable : (prefixWord ++ tailWord_1356181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356181).length < 2 ^ (prefixWord ++ tailWord_1356181).sum := by decide
  have hdescent : baseEnd_1356181 < baseStart_1356181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356202 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1356202 : Nat := 118140960795 + 1356202 * 2 ^ 59
def prefixEnd_1356202 : Nat := 4983230072969 + 3 ^ 40 * 1356202 * 2
def baseEnd_1356202 : Nat := 696383490589008087137947

theorem tailTrace_1356202 : CollatzResearch.WordTrace tailWord_1356202 prefixEnd_1356202 696383490589008087137947 := by
  unfold tailWord_1356202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12366187658179812426607715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32976500421812833137620573 12366187658179812426607715)
  ·
    refine ⟨18549281487269718639911573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12366187658179812426607715 18549281487269718639911573)
    ·
      refine ⟨869497569715768061245855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18549281487269718639911573 869497569715768061245855)
      ·
        refine ⟨1304246354573652091868783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869497569715768061245855 1304246354573652091868783)
        ·
          refine ⟨1956369531860478137803175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304246354573652091868783 1956369531860478137803175)
          ·
            refine ⟨2934554297790717206704763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956369531860478137803175 2934554297790717206704763)
            ·
              refine ⟨4401831446686075810057145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934554297790717206704763 4401831446686075810057145)
              ·
                refine ⟨3301373585014556857542859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401831446686075810057145 3301373585014556857542859)
                ·
                  refine ⟨4952060377521835286314289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301373585014556857542859 4952060377521835286314289)
                  ·
                    refine ⟨3714045283141376464735717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952060377521835286314289 3714045283141376464735717)
                    ·
                      refine ⟨696383490589008087137947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3714045283141376464735717 696383490589008087137947)
                      ·
                        rfl

theorem cell23_1356202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1356202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356202 prefixEnd_1356202 := by exact prefixLift 1356202
  have htrace : WordTrace (prefixWord ++ tailWord_1356202) baseStart_1356202 baseEnd_1356202 := by
    simpa [prefixWord, tailWord_1356202, baseEnd_1356202] using wordTrace_append hprefix tailTrace_1356202
  have hstable : (prefixWord ++ tailWord_1356202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356202).length < 2 ^ (prefixWord ++ tailWord_1356202).sum := by decide
  have hdescent : baseEnd_1356202 < baseStart_1356202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356204 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1356204 : Nat := 118140960795 + 1356204 * 2 ^ 59
def prefixEnd_1356204 : Nat := 4983230072969 + 3 ^ 40 * 1356204 * 2
def baseEnd_1356204 : Nat := 232128172516772359770979

theorem tailTrace_1356204 : CollatzResearch.WordTrace tailWord_1356204 prefixEnd_1356204 232128172516772359770979 := by
  unfold tailWord_1356204
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732411789356002024001833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32976549052474669365335777 24732411789356002024001833)
  ·
    refine ⟨18549308842017001518001375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24732411789356002024001833 18549308842017001518001375)
    ·
      refine ⟨27823963263025502277002063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18549308842017001518001375 27823963263025502277002063)
      ·
        refine ⟨41735944894538253415503095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27823963263025502277002063 41735944894538253415503095)
        ·
          refine ⟨62603917341807380123254643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41735944894538253415503095 62603917341807380123254643)
          ·
            refine ⟨93905876012711070184881965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62603917341807380123254643 93905876012711070184881965)
            ·
              refine ⟨35214703504766651319330737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93905876012711070184881965 35214703504766651319330737)
              ·
                refine ⟨26411027628574988489498053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35214703504766651319330737 26411027628574988489498053)
                ·
                  refine ⟨4952067680357810341780885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26411027628574988489498053 4952067680357810341780885)
                  ·
                    refine ⟨232128172516772359770979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4952067680357810341780885 232128172516772359770979)
                    ·
                      rfl

theorem cell23_1356204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1356204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356204 prefixEnd_1356204 := by exact prefixLift 1356204
  have htrace : WordTrace (prefixWord ++ tailWord_1356204) baseStart_1356204 baseEnd_1356204 := by
    simpa [prefixWord, tailWord_1356204, baseEnd_1356204] using wordTrace_append hprefix tailTrace_1356204
  have hstable : (prefixWord ++ tailWord_1356204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356204).length < 2 ^ (prefixWord ++ tailWord_1356204).sum := by decide
  have hdescent : baseEnd_1356204 < baseStart_1356204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356205 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1356205 : Nat := 118140960795 + 1356205 * 2 ^ 59
def prefixEnd_1356205 : Nat := 4983230072969 + 3 ^ 40 * 1356205 * 2
def baseEnd_1356205 : Nat := 696385031030971575400433

theorem tailTrace_1356205 : CollatzResearch.WordTrace tailWord_1356205 prefixEnd_1356205 696385031030971575400433 := by
  unfold tailWord_1356205
  simp only [CollatzResearch.WordTrace]
  refine ⟨49464860051708381218790069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32976573367805587479193379 49464860051708381218790069)
  ·
    refine ⟨4637330629847660739261569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49464860051708381218790069 4637330629847660739261569)
    ·
      refine ⟨3477997972385745554446177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4637330629847660739261569 3477997972385745554446177)
      ·
        refine ⟨2608498479289309165834633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477997972385745554446177 2608498479289309165834633)
        ·
          refine ⟨1956373859466981874375975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608498479289309165834633 1956373859466981874375975)
          ·
            refine ⟨2934560789200472811563963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956373859466981874375975 2934560789200472811563963)
            ·
              refine ⟨4401841183800709217345945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934560789200472811563963 4401841183800709217345945)
              ·
                refine ⟨3301380887850531913009459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401841183800709217345945 3301380887850531913009459)
                ·
                  refine ⟨4952071331775797869514189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301380887850531913009459 4952071331775797869514189)
                  ·
                    refine ⟨1857026749415924201067821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4952071331775797869514189 1857026749415924201067821)
                    ·
                      refine ⟨696385031030971575400433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857026749415924201067821 696385031030971575400433)
                      ·
                        rfl

theorem cell23_1356205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1356205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356205 prefixEnd_1356205 := by exact prefixLift 1356205
  have htrace : WordTrace (prefixWord ++ tailWord_1356205) baseStart_1356205 baseEnd_1356205 := by
    simpa [prefixWord, tailWord_1356205, baseEnd_1356205] using wordTrace_append hprefix tailTrace_1356205
  have hstable : (prefixWord ++ tailWord_1356205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356205).length < 2 ^ (prefixWord ++ tailWord_1356205).sum := by decide
  have hdescent : baseEnd_1356205 < baseStart_1356205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356224 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1356224 : Nat := 118140960795 + 1356224 * 2 ^ 59
def prefixEnd_1356224 : Nat := 4983230072969 + 3 ^ 40 * 1356224 * 2
def baseEnd_1356224 : Nat := 696394787163407001062845

theorem tailTrace_1356224 : CollatzResearch.WordTrace tailWord_1356224 prefixEnd_1356224 696394787163407001062845 := by
  unfold tailWord_1356224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732776519319773731865863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32977035359093031642487817 24732776519319773731865863)
  ·
    refine ⟨37099164778979660597798795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24732776519319773731865863 37099164778979660597798795)
    ·
      refine ⟨55648747168469490896698193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37099164778979660597798795 55648747168469490896698193)
      ·
        refine ⟨41736560376352118172523645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55648747168469490896698193 41736560376352118172523645)
        ·
          refine ⟨15651210141132044314696367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41736560376352118172523645 15651210141132044314696367)
          ·
            refine ⟨23476815211698066472044551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15651210141132044314696367 23476815211698066472044551)
            ·
              refine ⟨35215222817547099708066827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23476815211698066472044551 35215222817547099708066827)
              ·
                refine ⟨52822834226320649562100241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35215222817547099708066827 52822834226320649562100241)
                ·
                  refine ⟨39617125669740487171575181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52822834226320649562100241 39617125669740487171575181)
                  ·
                    refine ⟨14856422126152682689340693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39617125669740487171575181 14856422126152682689340693)
                    ·
                      refine ⟨696394787163407001062845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14856422126152682689340693 696394787163407001062845)
                      ·
                        rfl

theorem cell23_1356224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1356224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356224 prefixEnd_1356224 := by exact prefixLift 1356224
  have htrace : WordTrace (prefixWord ++ tailWord_1356224) baseStart_1356224 baseEnd_1356224 := by
    simpa [prefixWord, tailWord_1356224, baseEnd_1356224] using wordTrace_append hprefix tailTrace_1356224
  have hstable : (prefixWord ++ tailWord_1356224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356224).length < 2 ^ (prefixWord ++ tailWord_1356224).sum := by decide
  have hdescent : baseEnd_1356224 < baseStart_1356224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356231 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1356231 : Nat := 118140960795 + 1356231 * 2 ^ 59
def prefixEnd_1356231 : Nat := 4983230072969 + 3 ^ 40 * 1356231 * 2
def baseEnd_1356231 : Nat := 696398381527988473675313

theorem tailTrace_1356231 : CollatzResearch.WordTrace tailWord_1356231 prefixEnd_1356231 696398381527988473675313 := by
  unfold tailWord_1356231
  simp only [CollatzResearch.WordTrace]
  refine ⟨49465808349614187659236547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32977205566409458439491031 49465808349614187659236547)
  ·
    refine ⟨74198712524421281488854821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49465808349614187659236547 74198712524421281488854821)
    ·
      refine ⟨13912258598328990279160279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74198712524421281488854821 13912258598328990279160279)
      ·
        refine ⟨20868387897493485418740419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13912258598328990279160279 20868387897493485418740419)
        ·
          refine ⟨31302581846240228128110629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20868387897493485418740419 31302581846240228128110629)
          ·
            refine ⟨5869234096170042774020743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31302581846240228128110629 5869234096170042774020743)
            ·
              refine ⟨8803851144255064161031115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869234096170042774020743 8803851144255064161031115)
              ·
                refine ⟨13205776716382596241546673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8803851144255064161031115 13205776716382596241546673)
                ·
                  refine ⟨9904332537286947181160005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13205776716382596241546673 9904332537286947181160005)
                  ·
                    refine ⟨1857062350741302596467501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9904332537286947181160005 1857062350741302596467501)
                    ·
                      refine ⟨696398381527988473675313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857062350741302596467501 696398381527988473675313)
                      ·
                        rfl

theorem cell23_1356231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1356231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356231 prefixEnd_1356231 := by exact prefixLift 1356231
  have htrace : WordTrace (prefixWord ++ tailWord_1356231) baseStart_1356231 baseEnd_1356231 := by
    simpa [prefixWord, tailWord_1356231, baseEnd_1356231] using wordTrace_append hprefix tailTrace_1356231
  have hstable : (prefixWord ++ tailWord_1356231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356231).length < 2 ^ (prefixWord ++ tailWord_1356231).sum := by decide
  have hdescent : baseEnd_1356231 < baseStart_1356231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356245 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1356245 : Nat := 118140960795 + 1356245 * 2 ^ 59
def prefixEnd_1356245 : Nat := 4983230072969 + 3 ^ 40 * 1356245 * 2
def baseEnd_1356245 : Nat := 696405570257151418900249

theorem tailTrace_1356245 : CollatzResearch.WordTrace tailWord_1356245 prefixEnd_1356245 696405570257151418900249 := by
  unfold tailWord_1356245
  simp only [CollatzResearch.WordTrace]
  refine ⟨49466318971563468050246189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32977545981042312033497459 49466318971563468050246189)
  ·
    refine ⟨18549869614336300518842321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49466318971563468050246189 18549869614336300518842321)
    ·
      refine ⟨13912402210752225389131741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18549869614336300518842321 13912402210752225389131741)
      ·
        refine ⟨5217150829032084520924403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13912402210752225389131741 5217150829032084520924403)
        ·
          refine ⟨7825726243548126781386605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5217150829032084520924403 7825726243548126781386605)
          ·
            refine ⟨2934647341330547543019977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7825726243548126781386605 2934647341330547543019977)
            ·
              refine ⟨2200985505997910657264983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934647341330547543019977 2200985505997910657264983)
              ·
                refine ⟨3301478258996865985897475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200985505997910657264983 3301478258996865985897475)
                ·
                  refine ⟨4952217388495298978846213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301478258996865985897475 4952217388495298978846213)
                  ·
                    refine ⟨928540760342868558533665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952217388495298978846213 928540760342868558533665)
                    ·
                      refine ⟨696405570257151418900249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928540760342868558533665 696405570257151418900249)
                      ·
                        rfl

theorem cell23_1356245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1356245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356245 prefixEnd_1356245 := by exact prefixLift 1356245
  have htrace : WordTrace (prefixWord ++ tailWord_1356245) baseStart_1356245 baseEnd_1356245 := by
    simpa [prefixWord, tailWord_1356245, baseEnd_1356245] using wordTrace_append hprefix tailTrace_1356245
  have hstable : (prefixWord ++ tailWord_1356245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356245).length < 2 ^ (prefixWord ++ tailWord_1356245).sum := by decide
  have hdescent : baseEnd_1356245 < baseStart_1356245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356268 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 5]
def baseStart_1356268 : Nat := 118140960795 + 1356268 * 2 ^ 59
def prefixEnd_1356268 : Nat := 4983230072969 + 3 ^ 40 * 1356268 * 2
def baseEnd_1356268 : Nat := 77379708923578314323627

theorem tailTrace_1356268 : CollatzResearch.WordTrace tailWord_1356268 prefixEnd_1356268 77379708923578314323627 := by
  unfold tailWord_1356268
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733578925240071489166729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32978105233653428652222305 24733578925240071489166729)
  ·
    refine ⟨18550184193930053616875047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24733578925240071489166729 18550184193930053616875047)
    ·
      refine ⟨27825276290895080425312571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18550184193930053616875047 27825276290895080425312571)
      ·
        refine ⟨41737914436342620637968857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27825276290895080425312571 41737914436342620637968857)
        ·
          refine ⟨31303435827256965478476643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41737914436342620637968857 31303435827256965478476643)
          ·
            refine ⟨46955153740885448217714965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31303435827256965478476643 46955153740885448217714965)
            ·
              refine ⟨2201022831604005385205389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46955153740885448217714965 2201022831604005385205389)
              ·
                refine ⟨825383561851502019452021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201022831604005385205389 825383561851502019452021)
                ·
                  refine ⟨77379708923578314323627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825383561851502019452021 77379708923578314323627)
                  ·
                    rfl

theorem cell23_1356268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_1356268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356268 prefixEnd_1356268 := by exact prefixLift 1356268
  have htrace : WordTrace (prefixWord ++ tailWord_1356268) baseStart_1356268 baseEnd_1356268 := by
    simpa [prefixWord, tailWord_1356268, baseEnd_1356268] using wordTrace_append hprefix tailTrace_1356268
  have hstable : (prefixWord ++ tailWord_1356268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356268).length < 2 ^ (prefixWord ++ tailWord_1356268).sum := by decide
  have hdescent : baseEnd_1356268 < baseStart_1356268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356278 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1356278 : Nat := 118140960795 + 1356278 * 2 ^ 59
def prefixEnd_1356278 : Nat := 4983230072969 + 3 ^ 40 * 1356278 * 2
def baseEnd_1356278 : Nat := 696422515118749789787597

theorem tailTrace_1356278 : CollatzResearch.WordTrace tailWord_1356278 prefixEnd_1356278 696422515118749789787597 := by
  unfold tailWord_1356278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091720161277744667887343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32978348386962609790798325 3091720161277744667887343)
  ·
    refine ⟨4637580241916617001831015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091720161277744667887343 4637580241916617001831015)
    ·
      refine ⟨6956370362874925502746523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637580241916617001831015 6956370362874925502746523)
      ·
        refine ⟨10434555544312388254119785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956370362874925502746523 10434555544312388254119785)
        ·
          refine ⟨7825916658234291190589839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10434555544312388254119785 7825916658234291190589839)
          ·
            refine ⟨11738874987351436785884759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825916658234291190589839 11738874987351436785884759)
            ·
              refine ⟨17608312481027155178827139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738874987351436785884759 17608312481027155178827139)
              ·
                refine ⟨26412468721540732768240709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17608312481027155178827139 26412468721540732768240709)
                ·
                  refine ⟨4952337885288887394045133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26412468721540732768240709 4952337885288887394045133)
                  ·
                    refine ⟨1857126706983332772766925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4952337885288887394045133 1857126706983332772766925)
                    ·
                      refine ⟨696422515118749789787597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857126706983332772766925 696422515118749789787597)
                      ·
                        rfl

theorem cell23_1356278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1356278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356278 prefixEnd_1356278 := by exact prefixLift 1356278
  have htrace : WordTrace (prefixWord ++ tailWord_1356278) baseStart_1356278 baseEnd_1356278 := by
    simpa [prefixWord, tailWord_1356278, baseEnd_1356278] using wordTrace_append hprefix tailTrace_1356278
  have hstable : (prefixWord ++ tailWord_1356278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356278).length < 2 ^ (prefixWord ++ tailWord_1356278).sum := by decide
  have hdescent : baseEnd_1356278 < baseStart_1356278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356281 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_1356281 : Nat := 118140960795 + 1356281 * 2 ^ 59
def prefixEnd_1356281 : Nat := 4983230072969 + 3 ^ 40 * 1356281 * 2
def baseEnd_1356281 : Nat := 232141351853571092683361

theorem tailTrace_1356281 : CollatzResearch.WordTrace tailWord_1356281 prefixEnd_1356281 232141351853571092683361 := by
  unfold tailWord_1356281
  simp only [CollatzResearch.WordTrace]
  refine ⟨49467631999433046198556697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32978421332955364132371131 49467631999433046198556697)
  ·
    refine ⟨37100723999574784648917523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49467631999433046198556697 37100723999574784648917523)
    ·
      refine ⟨55651085999362176973376285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37100723999574784648917523 55651085999362176973376285)
      ·
        refine ⟨20869157249760816365016107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55651085999362176973376285 20869157249760816365016107)
        ·
          refine ⟨31303735874641224547524161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20869157249760816365016107 31303735874641224547524161)
          ·
            refine ⟨23477801905980918410643121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31303735874641224547524161 23477801905980918410643121)
            ·
              refine ⟨17608351429485688807982341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23477801905980918410643121 17608351429485688807982341)
              ·
                refine ⟨3301565893028566651496689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17608351429485688807982341 3301565893028566651496689)
                ·
                  refine ⟨2476174419771424988622517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301565893028566651496689 2476174419771424988622517)
                  ·
                    refine ⟨232141351853571092683361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2476174419771424988622517 232141351853571092683361)
                    ·
                      rfl

theorem cell23_1356281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_1356281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356281 prefixEnd_1356281 := by exact prefixLift 1356281
  have htrace : WordTrace (prefixWord ++ tailWord_1356281) baseStart_1356281 baseEnd_1356281 := by
    simpa [prefixWord, tailWord_1356281, baseEnd_1356281] using wordTrace_append hprefix tailTrace_1356281
  have hstable : (prefixWord ++ tailWord_1356281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356281).length < 2 ^ (prefixWord ++ tailWord_1356281).sum := by decide
  have hdescent : baseEnd_1356281 < baseStart_1356281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356338 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1356338 : Nat := 118140960795 + 1356338 * 2 ^ 59
def prefixEnd_1356338 : Nat := 4983230072969 + 3 ^ 40 * 1356338 * 2
def baseEnd_1356338 : Nat := 696453323958019555037321

theorem tailTrace_1356338 : CollatzResearch.WordTrace tailWord_1356338 prefixEnd_1356338 696453323958019555037321 := by
  unfold tailWord_1356338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367427740056636233345417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32979807306817696622254445 12367427740056636233345417)
  ·
    refine ⟨9275570805042477175009063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12367427740056636233345417 9275570805042477175009063)
    ·
      refine ⟨13913356207563715762513595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9275570805042477175009063 13913356207563715762513595)
      ·
        refine ⟨20870034311345573643770393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13913356207563715762513595 20870034311345573643770393)
        ·
          refine ⟨15652525733509180232827795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20870034311345573643770393 15652525733509180232827795)
          ·
            refine ⟨23478788600263770349241693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15652525733509180232827795 23478788600263770349241693)
            ·
              refine ⟨8804545725098913880965635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23478788600263770349241693 8804545725098913880965635)
              ·
                refine ⟨13206818587648370821448453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8804545725098913880965635 13206818587648370821448453)
                ·
                  refine ⟨2476278485184069529021585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13206818587648370821448453 2476278485184069529021585)
                  ·
                    refine ⟨1857208863888052146766189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476278485184069529021585 1857208863888052146766189)
                    ·
                      refine ⟨696453323958019555037321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857208863888052146766189 696453323958019555037321)
                      ·
                        rfl

theorem cell23_1356338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1356338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356338 prefixEnd_1356338 := by exact prefixLift 1356338
  have htrace : WordTrace (prefixWord ++ tailWord_1356338) baseStart_1356338 baseEnd_1356338 := by
    simpa [prefixWord, tailWord_1356338, baseEnd_1356338] using wordTrace_append hprefix tailTrace_1356338
  have hstable : (prefixWord ++ tailWord_1356338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356338).length < 2 ^ (prefixWord ++ tailWord_1356338).sum := by decide
  have hdescent : baseEnd_1356338 < baseStart_1356338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356341 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 8]
def baseStart_1356341 : Nat := 118140960795 + 1356341 * 2 ^ 59
def prefixEnd_1356341 : Nat := 4983230072969 + 3 ^ 40 * 1356341 * 2
def baseEnd_1356341 : Nat := 77383873822220338144423

theorem tailTrace_1356341 : CollatzResearch.WordTrace tailWord_1356341 prefixEnd_1356341 77383873822220338144423 := by
  unfold tailWord_1356341
  simp only [CollatzResearch.WordTrace]
  refine ⟨49469820379215676445740877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32979880252810450963827251 49469820379215676445740877)
  ·
    refine ⟨18551182642205878667152829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49469820379215676445740877 18551182642205878667152829)
    ·
      refine ⟨6956693490827204500182311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18551182642205878667152829 6956693490827204500182311)
      ·
        refine ⟨10435040236240806750273467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956693490827204500182311 10435040236240806750273467)
        ·
          refine ⟨15652560354361210125410201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435040236240806750273467 15652560354361210125410201)
          ·
            refine ⟨11739420265770907594057651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15652560354361210125410201 11739420265770907594057651)
            ·
              refine ⟨17609130398656361391086477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739420265770907594057651 17609130398656361391086477)
              ·
                refine ⟨6603423899496135521657429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17609130398656361391086477 6603423899496135521657429)
                ·
                  refine ⟨77383873822220338144423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6603423899496135521657429 77383873822220338144423)
                  ·
                    rfl

theorem cell23_1356341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_1356341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356341 prefixEnd_1356341 := by exact prefixLift 1356341
  have htrace : WordTrace (prefixWord ++ tailWord_1356341) baseStart_1356341 baseEnd_1356341 := by
    simpa [prefixWord, tailWord_1356341, baseEnd_1356341] using wordTrace_append hprefix tailTrace_1356341
  have hstable : (prefixWord ++ tailWord_1356341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356341).length < 2 ^ (prefixWord ++ tailWord_1356341).sum := by decide
  have hdescent : baseEnd_1356341 < baseStart_1356341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356436 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1356436 : Nat := 118140960795 + 1356436 * 2 ^ 59
def prefixEnd_1356436 : Nat := 4983230072969 + 3 ^ 40 * 1356436 * 2
def baseEnd_1356436 : Nat := 696503645062160171611871

theorem tailTrace_1356436 : CollatzResearch.WordTrace tailWord_1356436 prefixEnd_1356436 696503645062160171611871 := by
  unfold tailWord_1356436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24736642656935753835224581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32982190209247671780299441 24736642656935753835224581)
  ·
    refine ⟨4638120498175453844104609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24736642656935753835224581 4638120498175453844104609)
    ·
      refine ⟨3478590373631590383078457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638120498175453844104609 3478590373631590383078457)
      ·
        refine ⟨2608942780223692787308843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3478590373631590383078457 2608942780223692787308843)
        ·
          refine ⟨3913414170335539180963265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608942780223692787308843 3913414170335539180963265)
          ·
            refine ⟨2935060627751654385722449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913414170335539180963265 2935060627751654385722449)
            ·
              refine ⟨2201295470813740789291837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935060627751654385722449 2201295470813740789291837)
              ·
                refine ⟨825485801555152795984439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201295470813740789291837 825485801555152795984439)
                ·
                  refine ⟨1238228702332729193976659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825485801555152795984439 1238228702332729193976659)
                  ·
                    refine ⟨1857343053499093790964989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238228702332729193976659 1857343053499093790964989)
                    ·
                      refine ⟨696503645062160171611871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857343053499093790964989 696503645062160171611871)
                      ·
                        rfl

theorem cell23_1356436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1356436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356436 prefixEnd_1356436 := by exact prefixLift 1356436
  have htrace : WordTrace (prefixWord ++ tailWord_1356436) baseStart_1356436 baseEnd_1356436 := by
    simpa [prefixWord, tailWord_1356436, baseEnd_1356436] using wordTrace_append hprefix tailTrace_1356436
  have hstable : (prefixWord ++ tailWord_1356436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356436).length < 2 ^ (prefixWord ++ tailWord_1356436).sum := by decide
  have hdescent : baseEnd_1356436 < baseStart_1356436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356448 : List Nat := [2, 1, 1, 4, 4, 1, 10]
def baseStart_1356448 : Nat := 118140960795 + 1356448 * 2 ^ 59
def prefixEnd_1356448 : Nat := 4983230072969 + 3 ^ 40 * 1356448 * 2
def baseEnd_1356448 : Nat := 8598886504074248452615

theorem tailTrace_1356448 : CollatzResearch.WordTrace tailWord_1356448 prefixEnd_1356448 8598886504074248452615 := by
  unfold tailWord_1356448
  simp only [CollatzResearch.WordTrace]
  refine ⟨24736861494914016859942999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32982481993218689146590665 24736861494914016859942999)
  ·
    refine ⟨37105292242371025289914499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24736861494914016859942999 37105292242371025289914499)
    ·
      refine ⟨55657938363556537934871749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37105292242371025289914499 55657938363556537934871749)
      ·
        refine ⟨10435863443166850862788453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55657938363556537934871749 10435863443166850862788453)
        ·
          refine ⟨1956724395593784536772835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10435863443166850862788453 1956724395593784536772835)
          ·
            refine ⟨2935086593390676805159253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956724395593784536772835 2935086593390676805159253)
            ·
              refine ⟨8598886504074248452615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2935086593390676805159253 8598886504074248452615)
              ·
                rfl

theorem cell23_1356448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 10].length) (baseStart_1356448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356448 prefixEnd_1356448 := by exact prefixLift 1356448
  have htrace : WordTrace (prefixWord ++ tailWord_1356448) baseStart_1356448 baseEnd_1356448 := by
    simpa [prefixWord, tailWord_1356448, baseEnd_1356448] using wordTrace_append hprefix tailTrace_1356448
  have hstable : (prefixWord ++ tailWord_1356448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356448).length < 2 ^ (prefixWord ++ tailWord_1356448).sum := by decide
  have hdescent : baseEnd_1356448 < baseStart_1356448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356462 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1356462 : Nat := 118140960795 + 1356462 * 2 ^ 59
def prefixEnd_1356462 : Nat := 4983230072969 + 3 ^ 40 * 1356462 * 2
def baseEnd_1356462 : Nat := 696516995559177069886751

theorem tailTrace_1356462 : CollatzResearch.WordTrace tailWord_1356462 prefixEnd_1356462 696516995559177069886751 := by
  unfold tailWord_1356462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184279201472164263861955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32982822407851542740597093 6184279201472164263861955)
  ·
    refine ⟨9276418802208246395792933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6184279201472164263861955 9276418802208246395792933)
    ·
      refine ⟨1739328525414046199211175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9276418802208246395792933 1739328525414046199211175)
      ·
        refine ⟨2608992788121069298816763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739328525414046199211175 2608992788121069298816763)
        ·
          refine ⟨3913489182181603948225145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608992788121069298816763 3913489182181603948225145)
          ·
            refine ⟨2935116886636202961168859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913489182181603948225145 2935116886636202961168859)
            ·
              refine ⟨4402675329954304441753289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935116886636202961168859 4402675329954304441753289)
              ·
                refine ⟨3302006497465728331314967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402675329954304441753289 3302006497465728331314967)
                ·
                  refine ⟨4953009746198592496972451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302006497465728331314967 4953009746198592496972451)
                  ·
                    refine ⟨7429514619297888745458677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953009746198592496972451 7429514619297888745458677)
                    ·
                      refine ⟨696516995559177069886751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7429514619297888745458677 696516995559177069886751)
                      ·
                        rfl

theorem cell23_1356462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1356462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356462 prefixEnd_1356462 := by exact prefixLift 1356462
  have htrace : WordTrace (prefixWord ++ tailWord_1356462) baseStart_1356462 baseEnd_1356462 := by
    simpa [prefixWord, tailWord_1356462, baseEnd_1356462] using wordTrace_append hprefix tailTrace_1356462
  have hstable : (prefixWord ++ tailWord_1356462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356462).length < 2 ^ (prefixWord ++ tailWord_1356462).sum := by decide
  have hdescent : baseEnd_1356462 < baseStart_1356462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356469 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1356469 : Nat := 118140960795 + 1356469 * 2 ^ 59
def prefixEnd_1356469 : Nat := 4983230072969 + 3 ^ 40 * 1356469 * 2
def baseEnd_1356469 : Nat := 232173529974586180833073

theorem tailTrace_1356469 : CollatzResearch.WordTrace tailWord_1356469 prefixEnd_1356469 232173529974586180833073 := by
  unfold tailWord_1356469
  simp only [CollatzResearch.WordTrace]
  refine ⟨49474488922751954306400461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32982992615167969537600307 49474488922751954306400461)
  ·
    refine ⟨18552933346031982864900173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49474488922751954306400461 18552933346031982864900173)
    ·
      refine ⟨6957350004761993574337565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18552933346031982864900173 6957350004761993574337565)
      ·
        refine ⟨2609006251785747590376587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6957350004761993574337565 2609006251785747590376587)
        ·
          refine ⟨3913509377678621385564881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609006251785747590376587 3913509377678621385564881)
          ·
            refine ⟨2935132033258966039173661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913509377678621385564881 2935132033258966039173661)
            ·
              refine ⟨1100674512472112264690123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935132033258966039173661 1100674512472112264690123)
              ·
                refine ⟨1651011768708168397035185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100674512472112264690123 1651011768708168397035185)
                ·
                  refine ⟨1238258826531126297776389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651011768708168397035185 1238258826531126297776389)
                  ·
                    refine ⟨232173529974586180833073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238258826531126297776389 232173529974586180833073)
                    ·
                      rfl

theorem cell23_1356469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1356469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356469 prefixEnd_1356469 := by exact prefixLift 1356469
  have htrace : WordTrace (prefixWord ++ tailWord_1356469) baseStart_1356469 baseEnd_1356469 := by
    simpa [prefixWord, tailWord_1356469, baseEnd_1356469] using wordTrace_append hprefix tailTrace_1356469
  have hstable : (prefixWord ++ tailWord_1356469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356469).length < 2 ^ (prefixWord ++ tailWord_1356469).sum := by decide
  have hdescent : baseEnd_1356469 < baseStart_1356469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356488 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1356488 : Nat := 118140960795 + 1356488 * 2 ^ 59
def prefixEnd_1356488 : Nat := 4983230072969 + 3 ^ 40 * 1356488 * 2
def baseEnd_1356488 : Nat := 696530346056193968161631

theorem tailTrace_1356488 : CollatzResearch.WordTrace tailWord_1356488 prefixEnd_1356488 696530346056193968161631 := by
  unfold tailWord_1356488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737590954841560275671059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32983454606455413700894745 24737590954841560275671059)
  ·
    refine ⟨37106386432262340413506589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24737590954841560275671059 37106386432262340413506589)
    ·
      refine ⟨13914894912098377655064971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37106386432262340413506589 13914894912098377655064971)
      ·
        refine ⟨20872342368147566482597457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914894912098377655064971 20872342368147566482597457)
        ·
          refine ⟨15654256776110674861948093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20872342368147566482597457 15654256776110674861948093)
          ·
            refine ⟨5870346291041503073230535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15654256776110674861948093 5870346291041503073230535)
            ·
              refine ⟨8805519436562254609845803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870346291041503073230535 8805519436562254609845803)
              ·
                refine ⟨13208279154843381914768705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805519436562254609845803 13208279154843381914768705)
                ·
                  refine ⟨9906209366132536436076529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13208279154843381914768705 9906209366132536436076529)
                  ·
                    refine ⟨7429657024599402327057397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9906209366132536436076529 7429657024599402327057397)
                    ·
                      refine ⟨696530346056193968161631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7429657024599402327057397 696530346056193968161631)
                      ·
                        rfl

theorem cell23_1356488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1356488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356488 prefixEnd_1356488 := by exact prefixLift 1356488
  have htrace : WordTrace (prefixWord ++ tailWord_1356488) baseStart_1356488 baseEnd_1356488 := by
    simpa [prefixWord, tailWord_1356488, baseEnd_1356488] using wordTrace_append hprefix tailTrace_1356488
  have hstable : (prefixWord ++ tailWord_1356488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356488).length < 2 ^ (prefixWord ++ tailWord_1356488).sum := by decide
  have hdescent : baseEnd_1356488 < baseStart_1356488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356492 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1356492 : Nat := 118140960795 + 1356492 * 2 ^ 59
def prefixEnd_1356492 : Nat := 4983230072969 + 3 ^ 40 * 1356492 * 2
def baseEnd_1356492 : Nat := 696532399978811952511613

theorem tailTrace_1356492 : CollatzResearch.WordTrace tailWord_1356492 prefixEnd_1356492 696532399978811952511613 := by
  unfold tailWord_1356492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737663900834314617243865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32983551867779086156325153 24737663900834314617243865)
  ·
    refine ⟨18553247925625735962932899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24737663900834314617243865 18553247925625735962932899)
    ·
      refine ⟨27829871888438603944399349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18553247925625735962932899 27829871888438603944399349)
      ·
        refine ⟨2609050489541119119787439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27829871888438603944399349 2609050489541119119787439)
        ·
          refine ⟨3913575734311678679681159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609050489541119119787439 3913575734311678679681159)
          ·
            refine ⟨5870363601467518019521739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913575734311678679681159 5870363601467518019521739)
            ·
              refine ⟨8805545402201277029282609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870363601467518019521739 8805545402201277029282609)
              ·
                refine ⟨6604159051650957771961957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8805545402201277029282609 6604159051650957771961957)
                ·
                  refine ⟨1238279822184554582242867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6604159051650957771961957 1238279822184554582242867)
                  ·
                    refine ⟨1857419733276831873364301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238279822184554582242867 1857419733276831873364301)
                    ·
                      refine ⟨696532399978811952511613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857419733276831873364301 696532399978811952511613)
                      ·
                        rfl

theorem cell23_1356492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1356492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356492 prefixEnd_1356492 := by exact prefixLift 1356492
  have htrace : WordTrace (prefixWord ++ tailWord_1356492) baseStart_1356492 baseEnd_1356492 := by
    simpa [prefixWord, tailWord_1356492, baseEnd_1356492] using wordTrace_append hprefix tailTrace_1356492
  have hstable : (prefixWord ++ tailWord_1356492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356492).length < 2 ^ (prefixWord ++ tailWord_1356492).sum := by decide
  have hdescent : baseEnd_1356492 < baseStart_1356492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356526 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1356526 : Nat := 118140960795 + 1356526 * 2 ^ 59
def prefixEnd_1356526 : Nat := 4983230072969 + 3 ^ 40 * 1356526 * 2
def baseEnd_1356526 : Nat := 696549858321064819486457

theorem tailTrace_1356526 : CollatzResearch.WordTrace tailWord_1356526 prefixEnd_1356526 696549858321064819486457 := by
  unfold tailWord_1356526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184570985443181630153179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32984378589030302027483621 6184570985443181630153179)
  ·
    refine ⟨9276856478164772445229769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6184570985443181630153179 9276856478164772445229769)
    ·
      refine ⟨6957642358623579333922327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9276856478164772445229769 6957642358623579333922327)
      ·
        refine ⟨10436463537935369000883491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6957642358623579333922327 10436463537935369000883491)
        ·
          refine ⟨15654695306903053501325237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436463537935369000883491 15654695306903053501325237)
          ·
            refine ⟨1467627685022161265749241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15654695306903053501325237 1467627685022161265749241)
            ·
              refine ⟨1100720763766620949311931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467627685022161265749241 1100720763766620949311931)
              ·
                refine ⟨1651081145649931423967897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100720763766620949311931 1651081145649931423967897)
                ·
                  refine ⟨1238310859237448567975923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651081145649931423967897 1238310859237448567975923)
                  ·
                    refine ⟨1857466288856172851963885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238310859237448567975923 1857466288856172851963885)
                    ·
                      refine ⟨696549858321064819486457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857466288856172851963885 696549858321064819486457)
                      ·
                        rfl

theorem cell23_1356526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1356526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356526 prefixEnd_1356526 := by exact prefixLift 1356526
  have htrace : WordTrace (prefixWord ++ tailWord_1356526) baseStart_1356526 baseEnd_1356526 := by
    simpa [prefixWord, tailWord_1356526, baseEnd_1356526] using wordTrace_append hprefix tailTrace_1356526
  have hstable : (prefixWord ++ tailWord_1356526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356526).length < 2 ^ (prefixWord ++ tailWord_1356526).sum := by decide
  have hdescent : baseEnd_1356526 < baseStart_1356526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356528 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_1356528 : Nat := 118140960795 + 1356528 * 2 ^ 59
def prefixEnd_1356528 : Nat := 4983230072969 + 3 ^ 40 * 1356528 * 2
def baseEnd_1356528 : Nat := 696550885282373811661447

theorem tailTrace_1356528 : CollatzResearch.WordTrace tailWord_1356528 prefixEnd_1356528 696550885282373811661447 := by
  unfold tailWord_1356528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738320414769103691399119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32984427219692138255198825 24738320414769103691399119)
  ·
    refine ⟨37107480622153655537098679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24738320414769103691399119 37107480622153655537098679)
    ·
      refine ⟨55661220933230483305648019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37107480622153655537098679 55661220933230483305648019)
      ·
        refine ⟨83491831399845724958472029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55661220933230483305648019 83491831399845724958472029)
        ·
          refine ⟨31309436774942146859427011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83491831399845724958472029 31309436774942146859427011)
          ·
            refine ⟨46964155162413220289140517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31309436774942146859427011 46964155162413220289140517)
            ·
              refine ⟨8805779092952478804213847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46964155162413220289140517 8805779092952478804213847)
              ·
                refine ⟨13208668639428718206320771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805779092952478804213847 13208668639428718206320771)
                ·
                  refine ⟨19813002959143077309481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13208668639428718206320771 19813002959143077309481157)
                  ·
                    refine ⟨3714938054839326995527717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19813002959143077309481157 3714938054839326995527717)
                    ·
                      refine ⟨696550885282373811661447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3714938054839326995527717 696550885282373811661447)
                      ·
                        rfl

theorem cell23_1356528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_1356528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356528 prefixEnd_1356528 := by exact prefixLift 1356528
  have htrace : WordTrace (prefixWord ++ tailWord_1356528) baseStart_1356528 baseEnd_1356528 := by
    simpa [prefixWord, tailWord_1356528, baseEnd_1356528] using wordTrace_append hprefix tailTrace_1356528
  have hstable : (prefixWord ++ tailWord_1356528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356528).length < 2 ^ (prefixWord ++ tailWord_1356528).sum := by decide
  have hdescent : baseEnd_1356528 < baseStart_1356528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356538 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_1356538 : Nat := 118140960795 + 1356538 * 2 ^ 59
def prefixEnd_1356538 : Nat := 4983230072969 + 3 ^ 40 * 1356538 * 2
def baseEnd_1356538 : Nat := 77395113343213196948489

theorem tailTrace_1356538 : CollatzResearch.WordTrace tailWord_1356538 prefixEnd_1356538 77395113343213196948489 := by
  unfold tailWord_1356538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369251389875494772665567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32984670373001319393774845 12369251389875494772665567)
  ·
    refine ⟨18553877084813242158998351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12369251389875494772665567 18553877084813242158998351)
    ·
      refine ⟨27830815627219863238497527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18553877084813242158998351 27830815627219863238497527)
      ·
        refine ⟨41746223440829794857746291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27830815627219863238497527 41746223440829794857746291)
        ·
          refine ⟨62619335161244692286619437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41746223440829794857746291 62619335161244692286619437)
          ·
            refine ⟨23482250685466759607482289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62619335161244692286619437 23482250685466759607482289)
            ·
              refine ⟨17611688014100069705611717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23482250685466759607482289 17611688014100069705611717)
              ·
                refine ⟨3302191502643763069802197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17611688014100069705611717 3302191502643763069802197)
                ·
                  refine ⟨77395113343213196948489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3302191502643763069802197 77395113343213196948489)
                  ·
                    rfl

theorem cell23_1356538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_1356538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356538 prefixEnd_1356538 := by exact prefixLift 1356538
  have htrace : WordTrace (prefixWord ++ tailWord_1356538) baseStart_1356538 baseEnd_1356538 := by
    simpa [prefixWord, tailWord_1356538, baseEnd_1356538] using wordTrace_append hprefix tailTrace_1356538
  have hstable : (prefixWord ++ tailWord_1356538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356538).length < 2 ^ (prefixWord ++ tailWord_1356538).sum := by decide
  have hdescent : baseEnd_1356538 < baseStart_1356538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356555 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 5]
def baseStart_1356555 : Nat := 118140960795 + 1356555 * 2 ^ 59
def prefixEnd_1356555 : Nat := 4983230072969 + 3 ^ 40 * 1356555 * 2
def baseEnd_1356555 : Nat := 77396083251116134002647

theorem tailTrace_1356555 : CollatzResearch.WordTrace tailWord_1356555 prefixEnd_1356555 77396083251116134002647 := by
  unfold tailWord_1356555
  simp only [CollatzResearch.WordTrace]
  refine ⟨49477625600440390994031119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32985083733626927329354079 49477625600440390994031119)
  ·
    refine ⟨74216438400660586491046679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49477625600440390994031119 74216438400660586491046679)
    ·
      refine ⟨111324657600990879736570019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74216438400660586491046679 111324657600990879736570019)
      ·
        refine ⟨166986986401486319604855029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111324657600990879736570019 166986986401486319604855029)
        ·
          refine ⟨15655029975139342462955159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166986986401486319604855029 15655029975139342462955159)
          ·
            refine ⟨23482544962709013694432739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15655029975139342462955159 23482544962709013694432739)
            ·
              refine ⟨35223817444063520541649109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23482544962709013694432739 35223817444063520541649109)
              ·
                refine ⟨825558221345238762694901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35223817444063520541649109 825558221345238762694901)
                ·
                  refine ⟨77396083251116134002647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825558221345238762694901 77396083251116134002647)
                  ·
                    rfl

theorem cell23_1356555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 5].length) (baseStart_1356555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356555 prefixEnd_1356555 := by exact prefixLift 1356555
  have htrace : WordTrace (prefixWord ++ tailWord_1356555) baseStart_1356555 baseEnd_1356555 := by
    simpa [prefixWord, tailWord_1356555, baseEnd_1356555] using wordTrace_append hprefix tailTrace_1356555
  have hstable : (prefixWord ++ tailWord_1356555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356555).length < 2 ^ (prefixWord ++ tailWord_1356555).sum := by decide
  have hdescent : baseEnd_1356555 < baseStart_1356555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356565 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1356565 : Nat := 118140960795 + 1356565 * 2 ^ 59
def prefixEnd_1356565 : Nat := 4983230072969 + 3 ^ 40 * 1356565 * 2
def baseEnd_1356565 : Nat := 696569884066590166898777

theorem tailTrace_1356565 : CollatzResearch.WordTrace tailWord_1356565 prefixEnd_1356565 696569884066590166898777 := by
  unfold tailWord_1356565
  simp only [CollatzResearch.WordTrace]
  refine ⟨49477990330404162701895149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32985326886936108467930099 49477990330404162701895149)
  ·
    refine ⟨18554246373901561013210681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49477990330404162701895149 18554246373901561013210681)
    ·
      refine ⟨13915684780426170759908011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18554246373901561013210681 13915684780426170759908011)
      ·
        refine ⟨20873527170639256139862017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13915684780426170759908011 20873527170639256139862017)
        ·
          refine ⟨15655145377979442104896513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20873527170639256139862017 15655145377979442104896513)
          ·
            refine ⟨11741359033484581578672385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15655145377979442104896513 11741359033484581578672385)
            ·
              refine ⟨8806019275113436184004289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11741359033484581578672385 8806019275113436184004289)
              ·
                refine ⟨6604514456335077138003217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806019275113436184004289 6604514456335077138003217)
                ·
                  refine ⟨4953385842251307853502413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6604514456335077138003217 4953385842251307853502413)
                  ·
                    refine ⟨1857519690844240445063405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4953385842251307853502413 1857519690844240445063405)
                    ·
                      refine ⟨696569884066590166898777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857519690844240445063405 696569884066590166898777)
                      ·
                        rfl

theorem cell23_1356565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1356565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356565 prefixEnd_1356565 := by exact prefixLift 1356565
  have htrace : WordTrace (prefixWord ++ tailWord_1356565) baseStart_1356565 baseEnd_1356565 := by
    simpa [prefixWord, tailWord_1356565, baseEnd_1356565] using wordTrace_append hprefix tailTrace_1356565
  have hstable : (prefixWord ++ tailWord_1356565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356565).length < 2 ^ (prefixWord ++ tailWord_1356565).sum := by decide
  have hdescent : baseEnd_1356565 < baseStart_1356565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356568 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_1356568 : Nat := 118140960795 + 1356568 * 2 ^ 59
def prefixEnd_1356568 : Nat := 4983230072969 + 3 ^ 40 * 1356568 * 2
def baseEnd_1356568 : Nat := 232190474836184551720421

theorem tailTrace_1356568 : CollatzResearch.WordTrace tailWord_1356568 prefixEnd_1356568 232190474836184551720421 := by
  unfold tailWord_1356568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739049874696647107127179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32985399832928862809502905 24739049874696647107127179)
  ·
    refine ⟨37108574812044970660690769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24739049874696647107127179 37108574812044970660690769)
    ·
      refine ⟨27831431109033727995518077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37108574812044970660690769 27831431109033727995518077)
      ·
        refine ⟨10436786665887647998319279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27831431109033727995518077 10436786665887647998319279)
        ·
          refine ⟨15655179998831471997478919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436786665887647998319279 15655179998831471997478919)
          ·
            refine ⟨23482769998247207996218379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15655179998831471997478919 23482769998247207996218379)
            ·
              refine ⟨35224154997370811994327569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23482769998247207996218379 35224154997370811994327569)
              ·
                refine ⟨26418116248028108995745677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35224154997370811994327569 26418116248028108995745677)
                ·
                  refine ⟨9906793593010540873404629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26418116248028108995745677 9906793593010540873404629)
                  ·
                    refine ⟨232190474836184551720421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9906793593010540873404629 232190474836184551720421)
                    ·
                      rfl

theorem cell23_1356568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_1356568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356568 prefixEnd_1356568 := by exact prefixLift 1356568
  have htrace : WordTrace (prefixWord ++ tailWord_1356568) baseStart_1356568 baseEnd_1356568 := by
    simpa [prefixWord, tailWord_1356568, baseEnd_1356568] using wordTrace_append hprefix tailTrace_1356568
  have hstable : (prefixWord ++ tailWord_1356568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356568).length < 2 ^ (prefixWord ++ tailWord_1356568).sum := by decide
  have hdescent : baseEnd_1356568 < baseStart_1356568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356572 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 5]
def baseStart_1356572 : Nat := 118140960795 + 1356572 * 2 ^ 59
def prefixEnd_1356572 : Nat := 4983230072969 + 3 ^ 40 * 1356572 * 2
def baseEnd_1356572 : Nat := 77397053159019071056805

theorem tailTrace_1356572 : CollatzResearch.WordTrace tailWord_1356572 prefixEnd_1356572 77397053159019071056805 := by
  unfold tailWord_1356572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739122820689401448699985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32985497094252535264933313 24739122820689401448699985)
  ·
    refine ⟨18554342115517051086524989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24739122820689401448699985 18554342115517051086524989)
    ·
      refine ⟨6957878293318894157446871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18554342115517051086524989 6957878293318894157446871)
      ·
        refine ⟨10436817439978341236170307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6957878293318894157446871 10436817439978341236170307)
        ·
          refine ⟨15655226159967511854255461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10436817439978341236170307 15655226159967511854255461)
          ·
            refine ⟨2935354904993908472672899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15655226159967511854255461 2935354904993908472672899)
            ·
              refine ⟨4403032357490862709009349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935354904993908472672899 4403032357490862709009349)
              ·
                refine ⟨825568567029536757939253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4403032357490862709009349 825568567029536757939253)
                ·
                  refine ⟨77397053159019071056805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825568567029536757939253 77397053159019071056805)
                  ·
                    rfl

theorem cell23_1356572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_1356572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356572 prefixEnd_1356572 := by exact prefixLift 1356572
  have htrace : WordTrace (prefixWord ++ tailWord_1356572) baseStart_1356572 baseEnd_1356572 := by
    simpa [prefixWord, tailWord_1356572, baseEnd_1356572] using wordTrace_append hprefix tailTrace_1356572
  have hstable : (prefixWord ++ tailWord_1356572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356572).length < 2 ^ (prefixWord ++ tailWord_1356572).sum := by decide
  have hdescent : baseEnd_1356572 < baseStart_1356572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356589 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1356589 : Nat := 118140960795 + 1356589 * 2 ^ 59
def prefixEnd_1356589 : Nat := 4983230072969 + 3 ^ 40 * 1356589 * 2
def baseEnd_1356589 : Nat := 77398023066922008110963

theorem tailTrace_1356589 : CollatzResearch.WordTrace tailWord_1356589 prefixEnd_1356589 77398023066922008110963 := by
  unfold tailWord_1356589
  simp only [CollatzResearch.WordTrace]
  refine ⟨49478865682317214800768821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32985910454878143200512547 49478865682317214800768821)
  ·
    refine ⟨4638643657717238887572077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49478865682317214800768821 4638643657717238887572077)
    ·
      refine ⟨1739491371643964582839529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4638643657717238887572077 1739491371643964582839529)
      ·
        refine ⟨1304618528732973437129647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1739491371643964582839529 1304618528732973437129647)
        ·
          refine ⟨1956927793099460155694471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304618528732973437129647 1956927793099460155694471)
          ·
            refine ⟨2935391689649190233541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956927793099460155694471 2935391689649190233541707)
            ·
              refine ⟨4403087534473785350312561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935391689649190233541707 4403087534473785350312561)
              ·
                refine ⟨3302315650855339012734421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403087534473785350312561 3302315650855339012734421)
                ·
                  refine ⟨77398023066922008110963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3302315650855339012734421 77398023066922008110963)
                  ·
                    rfl

theorem cell23_1356589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1356589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356589 prefixEnd_1356589 := by exact prefixLift 1356589
  have htrace : WordTrace (prefixWord ++ tailWord_1356589) baseStart_1356589 baseEnd_1356589 := by
    simpa [prefixWord, tailWord_1356589, baseEnd_1356589] using wordTrace_append hprefix tailTrace_1356589
  have hstable : (prefixWord ++ tailWord_1356589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356589).length < 2 ^ (prefixWord ++ tailWord_1356589).sum := by decide
  have hdescent : baseEnd_1356589 < baseStart_1356589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356615 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 7, 4]
def baseStart_1356615 : Nat := 118140960795 + 1356615 * 2 ^ 59
def prefixEnd_1356615 : Nat := 4983230072969 + 3 ^ 40 * 1356615 * 2
def baseEnd_1356615 : Nat := 232198519366438323757849

theorem tailTrace_1356615 : CollatzResearch.WordTrace tailWord_1356615 prefixEnd_1356615 232198519366438323757849 := by
  unfold tailWord_1356615
  simp only [CollatzResearch.WordTrace]
  refine ⟨49479813980223021241215299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32986542653482014160810199 49479813980223021241215299)
  ·
    refine ⟨74219720970334531861822949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49479813980223021241215299 74219720970334531861822949)
    ·
      refine ⟨13916197681937724724091803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74219720970334531861822949 13916197681937724724091803)
      ·
        refine ⟨20874296522906587086137705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13916197681937724724091803 20874296522906587086137705)
        ·
          refine ⟨15655722392179940314603279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20874296522906587086137705 15655722392179940314603279)
          ·
            refine ⟨23483583588269910471904919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15655722392179940314603279 23483583588269910471904919)
            ·
              refine ⟨35225375382404865707857379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23483583588269910471904919 35225375382404865707857379)
              ·
                refine ⟨52838063073607298561786069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35225375382404865707857379 52838063073607298561786069)
                ·
                  refine ⟨1238392103287671060041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52838063073607298561786069 1238392103287671060041861)
                  ·
                    refine ⟨232198519366438323757849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238392103287671060041861 232198519366438323757849)
                    ·
                      rfl

theorem cell23_1356615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_1356615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356615 prefixEnd_1356615 := by exact prefixLift 1356615
  have htrace : WordTrace (prefixWord ++ tailWord_1356615) baseStart_1356615 baseEnd_1356615 := by
    simpa [prefixWord, tailWord_1356615, baseEnd_1356615] using wordTrace_append hprefix tailTrace_1356615
  have hstable : (prefixWord ++ tailWord_1356615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356615).length < 2 ^ (prefixWord ++ tailWord_1356615).sum := by decide
  have hdescent : baseEnd_1356615 < baseStart_1356615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356645 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 6]
def baseStart_1356645 : Nat := 118140960795 + 1356645 * 2 ^ 59
def prefixEnd_1356645 : Nat := 4983230072969 + 3 ^ 40 * 1356645 * 2
def baseEnd_1356645 : Nat := 77401218057661094877601

theorem tailTrace_1356645 : CollatzResearch.WordTrace tailWord_1356645 prefixEnd_1356645 77401218057661094877601 := by
  unfold tailWord_1356645
  simp only [CollatzResearch.WordTrace]
  refine ⟨49480908170114336364807389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32987272113409557576538259 49480908170114336364807389)
  ·
    refine ⟨18555340563792876136802771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49480908170114336364807389 18555340563792876136802771)
    ·
      refine ⟨27833010845689314205204157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18555340563792876136802771 27833010845689314205204157)
      ·
        refine ⟨10437379067133492826951559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27833010845689314205204157 10437379067133492826951559)
        ·
          refine ⟨15656068600700239240427339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10437379067133492826951559 15656068600700239240427339)
          ·
            refine ⟨23484102901050358860641009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15656068600700239240427339 23484102901050358860641009)
            ·
              refine ⟨17613077175787769145480757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23484102901050358860641009 17613077175787769145480757)
              ·
                refine ⟨1651225985230103357388821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17613077175787769145480757 1651225985230103357388821)
                ·
                  refine ⟨77401218057661094877601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1651225985230103357388821 77401218057661094877601)
                  ·
                    rfl

theorem cell23_1356645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_1356645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356645 prefixEnd_1356645 := by exact prefixLift 1356645
  have htrace : WordTrace (prefixWord ++ tailWord_1356645) baseStart_1356645 baseEnd_1356645 := by
    simpa [prefixWord, tailWord_1356645, baseEnd_1356645] using wordTrace_append hprefix tailTrace_1356645
  have hstable : (prefixWord ++ tailWord_1356645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356645).length < 2 ^ (prefixWord ++ tailWord_1356645).sum := by decide
  have hdescent : baseEnd_1356645 < baseStart_1356645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356662 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1356662 : Nat := 118140960795 + 1356662 * 2 ^ 59
def prefixEnd_1356662 : Nat := 4983230072969 + 3 ^ 40 * 1356662 * 2
def baseEnd_1356662 : Nat := 77402187965564031931759

theorem tailTrace_1356662 : CollatzResearch.WordTrace tailWord_1356662 prefixEnd_1356662 77402187965564031931759 := by
  unfold tailWord_1356662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092595513190796766761015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32987685474035165512117493 3092595513190796766761015)
  ·
    refine ⟨4638893269786195150141523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092595513190796766761015 4638893269786195150141523)
    ·
      refine ⟨6958339904679292725212285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638893269786195150141523 6958339904679292725212285)
      ·
        refine ⟨2609377464254734771954607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6958339904679292725212285 2609377464254734771954607)
        ·
          refine ⟨3914066196382102157931911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609377464254734771954607 3914066196382102157931911)
          ·
            refine ⟨5871099294573153236897867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914066196382102157931911 5871099294573153236897867)
            ·
              refine ⟨8806648941859729855346801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871099294573153236897867 8806648941859729855346801)
              ·
                refine ⟨6604986706394797391510101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806648941859729855346801 6604986706394797391510101)
                ·
                  refine ⟨77402187965564031931759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6604986706394797391510101 77402187965564031931759)
                  ·
                    rfl

theorem cell23_1356662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1356662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356662 prefixEnd_1356662 := by exact prefixLift 1356662
  have htrace : WordTrace (prefixWord ++ tailWord_1356662) baseStart_1356662 baseEnd_1356662 := by
    simpa [prefixWord, tailWord_1356662, baseEnd_1356662] using wordTrace_append hprefix tailTrace_1356662
  have hstable : (prefixWord ++ tailWord_1356662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356662).length < 2 ^ (prefixWord ++ tailWord_1356662).sum := by decide
  have hdescent : baseEnd_1356662 < baseStart_1356662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356692 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1356692 : Nat := 118140960795 + 1356692 * 2 ^ 59
def prefixEnd_1356692 : Nat := 4983230072969 + 3 ^ 40 * 1356692 * 2
def baseEnd_1356692 : Nat := 232211698703237056670231

theorem tailTrace_1356692 : CollatzResearch.WordTrace tailWord_1356692 prefixEnd_1356692 232211698703237056670231 := by
  unfold tailWord_1356692
  simp only [CollatzResearch.WordTrace]
  refine ⟨24741311200472031695884165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32988414933962708927845553 24741311200472031695884165)
  ·
    refine ⟨4638995850088505942978281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24741311200472031695884165 4638995850088505942978281)
    ·
      refine ⟨3479246887566379457233711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638995850088505942978281 3479246887566379457233711)
      ·
        refine ⟨5218870331349569185850567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479246887566379457233711 5218870331349569185850567)
        ·
          refine ⟨7828305497024353778775851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218870331349569185850567 7828305497024353778775851)
          ·
            refine ⟨11742458245536530668163777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828305497024353778775851 11742458245536530668163777)
            ·
              refine ⟨8806843684152398001122833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11742458245536530668163777 8806843684152398001122833)
              ·
                refine ⟨6605132763114298500842125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806843684152398001122833 6605132763114298500842125)
                ·
                  refine ⟨2476924786167861937815797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6605132763114298500842125 2476924786167861937815797)
                  ·
                    refine ⟨232211698703237056670231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2476924786167861937815797 232211698703237056670231)
                    ·
                      rfl

theorem cell23_1356692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1356692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356692 prefixEnd_1356692 := by exact prefixLift 1356692
  have htrace : WordTrace (prefixWord ++ tailWord_1356692) baseStart_1356692 baseEnd_1356692 := by
    simpa [prefixWord, tailWord_1356692, baseEnd_1356692] using wordTrace_append hprefix tailTrace_1356692
  have hstable : (prefixWord ++ tailWord_1356692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356692).length < 2 ^ (prefixWord ++ tailWord_1356692).sum := by decide
  have hdescent : baseEnd_1356692 < baseStart_1356692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356715 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3]
def baseStart_1356715 : Nat := 118140960795 + 1356715 * 2 ^ 59
def prefixEnd_1356715 : Nat := 4983230072969 + 3 ^ 40 * 1356715 * 2
def baseEnd_1356715 : Nat := 696646906164764580023087

theorem tailTrace_1356715 : CollatzResearch.WordTrace tailWord_1356715 prefixEnd_1356715 696646906164764580023087 := by
  unfold tailWord_1356715
  simp only [CollatzResearch.WordTrace]
  refine ⟨49483461279860738319855599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32988974186573825546570399 49483461279860738319855599)
  ·
    refine ⟨74225191919791107479783399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49483461279860738319855599 74225191919791107479783399)
    ·
      refine ⟨111337787879686661219675099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74225191919791107479783399 111337787879686661219675099)
      ·
        refine ⟨167006681819529991829512649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111337787879686661219675099 167006681819529991829512649)
        ·
          refine ⟨125255011364647493872134487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167006681819529991829512649 125255011364647493872134487)
          ·
            refine ⟨187882517046971240808201731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125255011364647493872134487 187882517046971240808201731)
            ·
              refine ⟨281823775570456861212302597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187882517046971240808201731 281823775570456861212302597)
              ·
                refine ⟨52841957919460661477306737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281823775570456861212302597 52841957919460661477306737)
                ·
                  refine ⟨39631468439595496107980053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52841957919460661477306737 39631468439595496107980053)
                  ·
                    refine ⟨1857725083106038880061565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39631468439595496107980053 1857725083106038880061565)
                    ·
                      refine ⟨696646906164764580023087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857725083106038880061565 696646906164764580023087)
                      ·
                        rfl

theorem cell23_1356715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].length) (baseStart_1356715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356715 prefixEnd_1356715 := by exact prefixLift 1356715
  have htrace : WordTrace (prefixWord ++ tailWord_1356715) baseStart_1356715 baseEnd_1356715 := by
    simpa [prefixWord, tailWord_1356715, baseEnd_1356715] using wordTrace_append hprefix tailTrace_1356715
  have hstable : (prefixWord ++ tailWord_1356715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356715).length < 2 ^ (prefixWord ++ tailWord_1356715).sum := by decide
  have hdescent : baseEnd_1356715 < baseStart_1356715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356740 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1356740 : Nat := 118140960795 + 1356740 * 2 ^ 59
def prefixEnd_1356740 : Nat := 4983230072969 + 3 ^ 40 * 1356740 * 2
def baseEnd_1356740 : Nat := 696659743181126982210473

theorem tailTrace_1356740 : CollatzResearch.WordTrace tailWord_1356740 prefixEnd_1356740 696659743181126982210473 := by
  unfold tailWord_1356740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742186552385083794757837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32989582069846778393010449 24742186552385083794757837)
  ·
    refine ⟨9278319957144406423034189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24742186552385083794757837 9278319957144406423034189)
    ·
      refine ⟨3479369983929152408637821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9278319957144406423034189 3479369983929152408637821)
      ·
        refine ⟨1304763743973432153239183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3479369983929152408637821 1304763743973432153239183)
        ·
          refine ⟨1957145615960148229858775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304763743973432153239183 1957145615960148229858775)
          ·
            refine ⟨2935718423940222344788163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957145615960148229858775 2935718423940222344788163)
            ·
              refine ⟨4403577635910333517182245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935718423940222344788163 4403577635910333517182245)
              ·
                refine ⟨825670806733187534471671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4403577635910333517182245 825670806733187534471671)
                ·
                  refine ⟨1238506210099781301707507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825670806733187534471671 1238506210099781301707507)
                  ·
                    refine ⟨1857759315149671952561261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238506210099781301707507 1857759315149671952561261)
                    ·
                      refine ⟨696659743181126982210473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857759315149671952561261 696659743181126982210473)
                      ·
                        rfl

theorem cell23_1356740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1356740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356740 prefixEnd_1356740 := by exact prefixLift 1356740
  have htrace : WordTrace (prefixWord ++ tailWord_1356740) baseStart_1356740 baseEnd_1356740 := by
    simpa [prefixWord, tailWord_1356740, baseEnd_1356740] using wordTrace_append hprefix tailTrace_1356740
  have hstable : (prefixWord ++ tailWord_1356740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356740).length < 2 ^ (prefixWord ++ tailWord_1356740).sum := by decide
  have hdescent : baseEnd_1356740 < baseStart_1356740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356796 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_1356796 : Nat := 118140960795 + 1356796 * 2 ^ 59
def prefixEnd_1356796 : Nat := 4983230072969 + 3 ^ 40 * 1356796 * 2
def baseEnd_1356796 : Nat := 696688498097778763110215

theorem tailTrace_1356796 : CollatzResearch.WordTrace tailWord_1356796 prefixEnd_1356796 696688498097778763110215 := by
  unfold tailWord_1356796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743207796283644576777121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32990943728378192769036161 24743207796283644576777121)
  ·
    refine ⟨18557405847212733432582841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24743207796283644576777121 18557405847212733432582841)
    ·
      refine ⟨13918054385409550074437131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18557405847212733432582841 13918054385409550074437131)
      ·
        refine ⟨20877081578114325111655697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13918054385409550074437131 20877081578114325111655697)
        ·
          refine ⟨15657811183585743833741773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20877081578114325111655697 15657811183585743833741773)
          ·
            refine ⟨5871679193844653937653165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15657811183585743833741773 5871679193844653937653165)
            ·
              refine ⟨2201879697691745226619937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871679193844653937653165 2201879697691745226619937)
              ·
                refine ⟨1651409773268808919964953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201879697691745226619937 1651409773268808919964953)
                ·
                  refine ⟨1238557329951606689973715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651409773268808919964953 1238557329951606689973715)
                  ·
                    refine ⟨1857835994927410034960573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238557329951606689973715 1857835994927410034960573)
                    ·
                      refine ⟨696688498097778763110215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1857835994927410034960573 696688498097778763110215)
                      ·
                        rfl

theorem cell23_1356796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_1356796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356796 prefixEnd_1356796 := by exact prefixLift 1356796
  have htrace : WordTrace (prefixWord ++ tailWord_1356796) baseStart_1356796 baseEnd_1356796 := by
    simpa [prefixWord, tailWord_1356796, baseEnd_1356796] using wordTrace_append hprefix tailTrace_1356796
  have hstable : (prefixWord ++ tailWord_1356796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356796).length < 2 ^ (prefixWord ++ tailWord_1356796).sum := by decide
  have hdescent : baseEnd_1356796 < baseStart_1356796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356812 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1356812 : Nat := 118140960795 + 1356812 * 2 ^ 59
def prefixEnd_1356812 : Nat := 4983230072969 + 3 ^ 40 * 1356812 * 2
def baseEnd_1356812 : Nat := 232232237929416900170047

theorem tailTrace_1356812 : CollatzResearch.WordTrace tailWord_1356812 prefixEnd_1356812 232232237929416900170047 := by
  unfold tailWord_1356812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743499580254661943068345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32991332773672882590757793 24743499580254661943068345)
  ·
    refine ⟨18557624685190996457301259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24743499580254661943068345 18557624685190996457301259)
    ·
      refine ⟨27836437027786494685951889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18557624685190996457301259 27836437027786494685951889)
      ·
        refine ⟨20877327770839871014463917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27836437027786494685951889 20877327770839871014463917)
        ·
          refine ⟨7828997914064951630423969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20877327770839871014463917 7828997914064951630423969)
          ·
            refine ⟨5871748435548713722817977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7828997914064951630423969 5871748435548713722817977)
            ·
              refine ⟨4403811326661535292113483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871748435548713722817977 4403811326661535292113483)
              ·
                refine ⟨6605716989992302938170225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403811326661535292113483 6605716989992302938170225)
                ·
                  refine ⟨4954287742494227203627669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6605716989992302938170225 4954287742494227203627669)
                  ·
                    refine ⟨232232237929416900170047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4954287742494227203627669 232232237929416900170047)
                    ·
                      rfl

theorem cell23_1356812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1356812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356812 prefixEnd_1356812 := by exact prefixLift 1356812
  have htrace : WordTrace (prefixWord ++ tailWord_1356812) baseStart_1356812 baseEnd_1356812 := by
    simpa [prefixWord, tailWord_1356812, baseEnd_1356812] using wordTrace_append hprefix tailTrace_1356812
  have hstable : (prefixWord ++ tailWord_1356812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356812).length < 2 ^ (prefixWord ++ tailWord_1356812).sum := by decide
  have hdescent : baseEnd_1356812 < baseStart_1356812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356815 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_1356815 : Nat := 118140960795 + 1356815 * 2 ^ 59
def prefixEnd_1356815 : Nat := 4983230072969 + 3 ^ 40 * 1356815 * 2
def baseEnd_1356815 : Nat := 696698254230214188772627

theorem tailTrace_1356815 : CollatzResearch.WordTrace tailWord_1356815 prefixEnd_1356815 696698254230214188772627 := by
  unfold tailWord_1356815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49487108579498455398495899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32991405719665636932330599 49487108579498455398495899)
  ·
    refine ⟨74230662869247683097743849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49487108579498455398495899 74230662869247683097743849)
    ·
      refine ⟨55672997151935762323307887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74230662869247683097743849 55672997151935762323307887)
      ·
        refine ⟨83509495727903643484961831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55672997151935762323307887 83509495727903643484961831)
        ·
          refine ⟨125264243591855465227442747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83509495727903643484961831 125264243591855465227442747)
          ·
            refine ⟨187896365387783197841164121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125264243591855465227442747 187896365387783197841164121)
            ·
              refine ⟨140922274040837398380873091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187896365387783197841164121 140922274040837398380873091)
              ·
                refine ⟨211383411061256097571309637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140922274040837398380873091 211383411061256097571309637)
                ·
                  refine ⟨39634389573985518294620557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211383411061256097571309637 39634389573985518294620557)
                  ·
                    refine ⟨14862896090244569360482709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39634389573985518294620557 14862896090244569360482709)
                    ·
                      refine ⟨696698254230214188772627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14862896090244569360482709 696698254230214188772627)
                      ·
                        rfl

theorem cell23_1356815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_1356815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356815 prefixEnd_1356815 := by exact prefixLift 1356815
  have htrace : WordTrace (prefixWord ++ tailWord_1356815) baseStart_1356815 baseEnd_1356815 := by
    simpa [prefixWord, tailWord_1356815, baseEnd_1356815] using wordTrace_append hprefix tailTrace_1356815
  have hstable : (prefixWord ++ tailWord_1356815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356815).length < 2 ^ (prefixWord ++ tailWord_1356815).sum := by decide
  have hdescent : baseEnd_1356815 < baseStart_1356815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356823 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1356823 : Nat := 118140960795 + 1356823 * 2 ^ 59
def prefixEnd_1356823 : Nat := 4983230072969 + 3 ^ 40 * 1356823 * 2
def baseEnd_1356823 : Nat := 696702362075450157472591

theorem tailTrace_1356823 : CollatzResearch.WordTrace tailWord_1356823 prefixEnd_1356823 696702362075450157472591 := by
  unfold tailWord_1356823
  simp only [CollatzResearch.WordTrace]
  refine ⟨49487400363469472764787123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32991600242312981843191415 49487400363469472764787123)
  ·
    refine ⟨74231100545204209147180685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49487400363469472764787123 74231100545204209147180685)
    ·
      refine ⟨27836662704451578430192757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74231100545204209147180685 27836662704451578430192757)
      ·
        refine ⟨2609687128542335477830571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27836662704451578430192757 2609687128542335477830571)
        ·
          refine ⟨3914530692813503216745857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609687128542335477830571 3914530692813503216745857)
          ·
            refine ⟨2935898019610127412559393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914530692813503216745857 2935898019610127412559393)
            ·
              refine ⟨2201923514707595559419545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935898019610127412559393 2201923514707595559419545)
              ·
                refine ⟨1651442636030696669564659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201923514707595559419545 1651442636030696669564659)
                ·
                  refine ⟨2477163954046045004346989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651442636030696669564659 2477163954046045004346989)
                  ·
                    refine ⟨928936482767266876630121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477163954046045004346989 928936482767266876630121)
                    ·
                      refine ⟨696702362075450157472591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 928936482767266876630121 696702362075450157472591)
                      ·
                        rfl

theorem cell23_1356823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1356823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356823 prefixEnd_1356823 := by exact prefixLift 1356823
  have htrace : WordTrace (prefixWord ++ tailWord_1356823) baseStart_1356823 baseEnd_1356823 := by
    simpa [prefixWord, tailWord_1356823, baseEnd_1356823] using wordTrace_append hprefix tailTrace_1356823
  have hstable : (prefixWord ++ tailWord_1356823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356823).length < 2 ^ (prefixWord ++ tailWord_1356823).sum := by decide
  have hdescent : baseEnd_1356823 < baseStart_1356823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356839 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1356839 : Nat := 118140960795 + 1356839 * 2 ^ 59
def prefixEnd_1356839 : Nat := 4983230072969 + 3 ^ 40 * 1356839 * 2
def baseEnd_1356839 : Nat := 696710577765922094872517

theorem tailTrace_1356839 : CollatzResearch.WordTrace tailWord_1356839 prefixEnd_1356839 696710577765922094872517 := by
  unfold tailWord_1356839
  simp only [CollatzResearch.WordTrace]
  refine ⟨49487983931411507497369571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32991989287607671664913047 49487983931411507497369571)
  ·
    refine ⟨74231975897117261246054357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49487983931411507497369571 74231975897117261246054357)
    ·
      refine ⟨1739811935088685810454399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74231975897117261246054357 1739811935088685810454399)
      ·
        refine ⟨2609717902633028715681599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739811935088685810454399 2609717902633028715681599)
        ·
          refine ⟨3914576853949543073522399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609717902633028715681599 3914576853949543073522399)
          ·
            refine ⟨5871865280924314610283599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914576853949543073522399 5871865280924314610283599)
            ·
              refine ⟨8807797921386471915425399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871865280924314610283599 8807797921386471915425399)
              ·
                refine ⟨13211696882079707873138099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8807797921386471915425399 13211696882079707873138099)
                ·
                  refine ⟨19817545323119561809707149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13211696882079707873138099 19817545323119561809707149)
                  ·
                    refine ⟨7431579496169835678640181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19817545323119561809707149 7431579496169835678640181)
                    ·
                      refine ⟨696710577765922094872517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7431579496169835678640181 696710577765922094872517)
                      ·
                        rfl

theorem cell23_1356839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1356839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356839 prefixEnd_1356839 := by exact prefixLift 1356839
  have htrace : WordTrace (prefixWord ++ tailWord_1356839) baseStart_1356839 baseEnd_1356839 := by
    simpa [prefixWord, tailWord_1356839, baseEnd_1356839] using wordTrace_append hprefix tailTrace_1356839
  have hstable : (prefixWord ++ tailWord_1356839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356839).length < 2 ^ (prefixWord ++ tailWord_1356839).sum := by decide
  have hdescent : baseEnd_1356839 < baseStart_1356839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356872 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1356872 : Nat := 118140960795 + 1356872 * 2 ^ 59
def prefixEnd_1356872 : Nat := 4983230072969 + 3 ^ 40 * 1356872 * 2
def baseEnd_1356872 : Nat := 232242507542506821919955

theorem tailTrace_1356872 : CollatzResearch.WordTrace tailWord_1356872 prefixEnd_1356872 232242507542506821919955 := by
  unfold tailWord_1356872
  simp only [CollatzResearch.WordTrace]
  refine ⟨24744593770145977066660435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32992791693527969422213913 24744593770145977066660435)
  ·
    refine ⟨37116890655218965599990653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24744593770145977066660435 37116890655218965599990653)
    ·
      refine ⟨13918833995707112099996495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37116890655218965599990653 13918833995707112099996495)
      ·
        refine ⟨20878250993560668149994743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13918833995707112099996495 20878250993560668149994743)
        ·
          refine ⟨31317376490341002224992115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20878250993560668149994743 31317376490341002224992115)
          ·
            refine ⟨46976064735511503337488173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31317376490341002224992115 46976064735511503337488173)
            ·
              refine ⟨17616024275816813751558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46976064735511503337488173 17616024275816813751558065)
              ·
                refine ⟨13212018206862610313668549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17616024275816813751558065 13212018206862610313668549)
                ·
                  refine ⟨2477253413786739433812853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13212018206862610313668549 2477253413786739433812853)
                  ·
                    refine ⟨232242507542506821919955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2477253413786739433812853 232242507542506821919955)
                    ·
                      rfl

theorem cell23_1356872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1356872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356872 prefixEnd_1356872 := by exact prefixLift 1356872
  have htrace : WordTrace (prefixWord ++ tailWord_1356872) baseStart_1356872 baseEnd_1356872 := by
    simpa [prefixWord, tailWord_1356872, baseEnd_1356872] using wordTrace_append hprefix tailTrace_1356872
  have hstable : (prefixWord ++ tailWord_1356872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356872).length < 2 ^ (prefixWord ++ tailWord_1356872).sum := by decide
  have hdescent : baseEnd_1356872 < baseStart_1356872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356912 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1356912 : Nat := 118140960795 + 1356912 * 2 ^ 59
def prefixEnd_1356912 : Nat := 4983230072969 + 3 ^ 40 * 1356912 * 2
def baseEnd_1356912 : Nat := 696748061853700309259681

theorem tailTrace_1356912 : CollatzResearch.WordTrace tailWord_1356912 prefixEnd_1356912 696748061853700309259681 := by
  unfold tailWord_1356912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24745323230073520482388495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32993764306764693976517993 24745323230073520482388495)
  ·
    refine ⟨37117984845110280723582743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24745323230073520482388495 37117984845110280723582743)
    ·
      refine ⟨55676977267665421085374115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37117984845110280723582743 55676977267665421085374115)
      ·
        refine ⟨83515465901498131628061173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55676977267665421085374115 83515465901498131628061173)
        ·
          refine ⟨7829574928265449840130735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83515465901498131628061173 7829574928265449840130735)
          ·
            refine ⟨11744362392398174760196103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829574928265449840130735 11744362392398174760196103)
            ·
              refine ⟨17616543588597262140294155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11744362392398174760196103 17616543588597262140294155)
              ·
                refine ⟨26424815382895893210441233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17616543588597262140294155 26424815382895893210441233)
                ·
                  refine ⟨19818611537171919907830925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26424815382895893210441233 19818611537171919907830925)
                  ·
                    refine ⟨7431979326439469965436597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19818611537171919907830925 7431979326439469965436597)
                    ·
                      refine ⟨696748061853700309259681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7431979326439469965436597 696748061853700309259681)
                      ·
                        rfl

theorem cell23_1356912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1356912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356912 prefixEnd_1356912 := by exact prefixLift 1356912
  have htrace : WordTrace (prefixWord ++ tailWord_1356912) baseStart_1356912 baseEnd_1356912 := by
    simpa [prefixWord, tailWord_1356912, baseEnd_1356912] using wordTrace_append hprefix tailTrace_1356912
  have hstable : (prefixWord ++ tailWord_1356912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356912).length < 2 ^ (prefixWord ++ tailWord_1356912).sum := by decide
  have hdescent : baseEnd_1356912 < baseStart_1356912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356919 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 3, 4]
def baseStart_1356919 : Nat := 118140960795 + 1356919 * 2 ^ 59
def prefixEnd_1356919 : Nat := 4983230072969 + 3 ^ 40 * 1356919 * 2
def baseEnd_1356919 : Nat := 232250552072760593957383

theorem tailTrace_1356919 : CollatzResearch.WordTrace tailWord_1356919 prefixEnd_1356919 232250552072760593957383 := by
  unfold tailWord_1356919
  simp only [CollatzResearch.WordTrace]
  refine ⟨49490901771121681160281811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32993934514081120773521207 49490901771121681160281811)
  ·
    refine ⟨74236352656682521740422717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49490901771121681160281811 74236352656682521740422717)
    ·
      refine ⟨27838632246255945652658519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74236352656682521740422717 27838632246255945652658519)
      ·
        refine ⟨41757948369383918478987779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27838632246255945652658519 41757948369383918478987779)
        ·
          refine ⟨62636922554075877718481669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41757948369383918478987779 62636922554075877718481669)
          ·
            refine ⟨11744422978889227072215313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62636922554075877718481669 11744422978889227072215313)
            ·
              refine ⟨8808317234166920304161485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11744422978889227072215313 8808317234166920304161485)
              ·
                refine ⟨3303118962812595114060557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8808317234166920304161485 3303118962812595114060557)
                ·
                  refine ⟨1238669611054723167772709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3303118962812595114060557 1238669611054723167772709)
                  ·
                    refine ⟨232250552072760593957383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238669611054723167772709 232250552072760593957383)
                    ·
                      rfl

theorem cell23_1356919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_1356919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356919 prefixEnd_1356919 := by exact prefixLift 1356919
  have htrace : WordTrace (prefixWord ++ tailWord_1356919) baseStart_1356919 baseEnd_1356919 := by
    simpa [prefixWord, tailWord_1356919, baseEnd_1356919] using wordTrace_append hprefix tailTrace_1356919
  have hstable : (prefixWord ++ tailWord_1356919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356919).length < 2 ^ (prefixWord ++ tailWord_1356919).sum := by decide
  have hdescent : baseEnd_1356919 < baseStart_1356919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356946 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1356946 : Nat := 118140960795 + 1356946 * 2 ^ 59
def prefixEnd_1356946 : Nat := 4983230072969 + 3 ^ 40 * 1356946 * 2
def baseEnd_1356946 : Nat := 696765520195953176234525

theorem tailTrace_1356946 : CollatzResearch.WordTrace tailWord_1356946 prefixEnd_1356946 696765520195953176234525 := by
  unfold tailWord_1356946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372971635505966192878673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32994591028015909847676461 12372971635505966192878673)
  ·
    refine ⟨9279728726629474644659005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12372971635505966192878673 9279728726629474644659005)
    ·
      refine ⟨3479898272486052991747127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9279728726629474644659005 3479898272486052991747127)
      ·
        refine ⟨5219847408729079487620691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479898272486052991747127 5219847408729079487620691)
        ·
          refine ⟨7829771113093619231431037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219847408729079487620691 7829771113093619231431037)
          ·
            refine ⟨2936164167410107211786639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7829771113093619231431037 2936164167410107211786639)
            ·
              refine ⟨4404246251115160817679959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936164167410107211786639 4404246251115160817679959)
              ·
                refine ⟨6606369376672741226519939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404246251115160817679959 6606369376672741226519939)
                ·
                  refine ⟨9909554065009111839779909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6606369376672741226519939 9909554065009111839779909)
                  ·
                    refine ⟨1858041387189208469958733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9909554065009111839779909 1858041387189208469958733)
                    ·
                      refine ⟨696765520195953176234525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858041387189208469958733 696765520195953176234525)
                      ·
                        rfl

theorem cell23_1356946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1356946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356946 prefixEnd_1356946 := by exact prefixLift 1356946
  have htrace : WordTrace (prefixWord ++ tailWord_1356946) baseStart_1356946 baseEnd_1356946 := by
    simpa [prefixWord, tailWord_1356946, baseEnd_1356946] using wordTrace_append hprefix tailTrace_1356946
  have hstable : (prefixWord ++ tailWord_1356946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356946).length < 2 ^ (prefixWord ++ tailWord_1356946).sum := by decide
  have hdescent : baseEnd_1356946 < baseStart_1356946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 9, 2]
def baseStart_1356969 : Nat := 118140960795 + 1356969 * 2 ^ 59
def prefixEnd_1356969 : Nat := 4983230072969 + 3 ^ 40 * 1356969 * 2
def baseEnd_1356969 : Nat := 696777330251006586246919

theorem tailTrace_1356969 : CollatzResearch.WordTrace tailWord_1356969 prefixEnd_1356969 696777330251006586246919 := by
  unfold tailWord_1356969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49492725420940539699601961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32995150280627026466401307 49492725420940539699601961)
  ·
    refine ⟨37119544065705404774701471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49492725420940539699601961 37119544065705404774701471)
    ·
      refine ⟨55679316098558107162052207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37119544065705404774701471 55679316098558107162052207)
      ·
        refine ⟨83518974147837160743078311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55679316098558107162052207 83518974147837160743078311)
        ·
          refine ⟨125278461221755741114617467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83518974147837160743078311 125278461221755741114617467)
          ·
            refine ⟨187917691832633611671926201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125278461221755741114617467 187917691832633611671926201)
            ·
              refine ⟨140938268874475208753944651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187917691832633611671926201 140938268874475208753944651)
              ·
                refine ⟨211407403311712813130916977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140938268874475208753944651 211407403311712813130916977)
                ·
                  refine ⟨158555552483784609848187733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211407403311712813130916977 158555552483784609848187733)
                  ·
                    refine ⟨929036440334675448329225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158555552483784609848187733 929036440334675448329225)
                    ·
                      refine ⟨696777330251006586246919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929036440334675448329225 696777330251006586246919)
                      ·
                        rfl

theorem cell23_1356969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9, 2].length) (baseStart_1356969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356969 prefixEnd_1356969 := by exact prefixLift 1356969
  have htrace : WordTrace (prefixWord ++ tailWord_1356969) baseStart_1356969 baseEnd_1356969 := by
    simpa [prefixWord, tailWord_1356969, baseEnd_1356969] using wordTrace_append hprefix tailTrace_1356969
  have hstable : (prefixWord ++ tailWord_1356969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356969).length < 2 ^ (prefixWord ++ tailWord_1356969).sum := by decide
  have hdescent : baseEnd_1356969 < baseStart_1356969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356970 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1356970 : Nat := 118140960795 + 1356970 * 2 ^ 59
def prefixEnd_1356970 : Nat := 4983230072969 + 3 ^ 40 * 1356970 * 2
def baseEnd_1356970 : Nat := 232259281243887027444805

theorem tailTrace_1356970 : CollatzResearch.WordTrace tailWord_1356970 prefixEnd_1356970 232259281243887027444805 := by
  unfold tailWord_1356970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373190473484229217597091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32995174595957944580258909 12373190473484229217597091)
  ·
    refine ⟨18559785710226343826395637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12373190473484229217597091 18559785710226343826395637)
    ·
      refine ⟨1739979910333719733724591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18559785710226343826395637 1739979910333719733724591)
      ·
        refine ⟨2609969865500579600586887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739979910333719733724591 2609969865500579600586887)
        ·
          refine ⟨3914954798250869400880331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609969865500579600586887 3914954798250869400880331)
          ·
            refine ⟨5872432197376304101320497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914954798250869400880331 5872432197376304101320497)
            ·
              refine ⟨4404324148032228075990373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872432197376304101320497 4404324148032228075990373)
              ·
                refine ⟨825810777756042764248195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4404324148032228075990373 825810777756042764248195)
                ·
                  refine ⟨1238716166634064146372293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825810777756042764248195 1238716166634064146372293)
                  ·
                    refine ⟨232259281243887027444805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238716166634064146372293 232259281243887027444805)
                    ·
                      rfl

theorem cell23_1356970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1356970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356970 prefixEnd_1356970 := by exact prefixLift 1356970
  have htrace : WordTrace (prefixWord ++ tailWord_1356970) baseStart_1356970 baseEnd_1356970 := by
    simpa [prefixWord, tailWord_1356970, baseEnd_1356970] using wordTrace_append hprefix tailTrace_1356970
  have hstable : (prefixWord ++ tailWord_1356970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356970).length < 2 ^ (prefixWord ++ tailWord_1356970).sum := by decide
  have hdescent : baseEnd_1356970 < baseStart_1356970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356972 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1356972 : Nat := 118140960795 + 1356972 * 2 ^ 59
def prefixEnd_1356972 : Nat := 4983230072969 + 3 ^ 40 * 1356972 * 2
def baseEnd_1356972 : Nat := 696778870692970074509405

theorem tailTrace_1356972 : CollatzResearch.WordTrace tailWord_1356972 prefixEnd_1356972 696778870692970074509405 := by
  unfold tailWord_1356972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746417419964835605980585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32995223226619780807974113 24746417419964835605980585)
  ·
    refine ⟨18559813064973626704485439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24746417419964835605980585 18559813064973626704485439)
    ·
      refine ⟨27839719597460440056728159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18559813064973626704485439 27839719597460440056728159)
      ·
        refine ⟨41759579396190660085092239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27839719597460440056728159 41759579396190660085092239)
        ·
          refine ⟨62639369094285990127638359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41759579396190660085092239 62639369094285990127638359)
          ·
            refine ⟨93959053641428985191457539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62639369094285990127638359 93959053641428985191457539)
            ·
              refine ⟨140938580462143477787186309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93959053641428985191457539 140938580462143477787186309)
              ·
                refine ⟨26425983836651902085097433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140938580462143477787186309 26425983836651902085097433)
                ·
                  refine ⟨19819487877488926563823075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26425983836651902085097433 19819487877488926563823075)
                  ·
                    refine ⟨29729231816233389845734613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19819487877488926563823075 29729231816233389845734613)
                    ·
                      refine ⟨696778870692970074509405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29729231816233389845734613 696778870692970074509405)
                      ·
                        rfl

theorem cell23_1356972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1356972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356972 prefixEnd_1356972 := by exact prefixLift 1356972
  have htrace : WordTrace (prefixWord ++ tailWord_1356972) baseStart_1356972 baseEnd_1356972 := by
    simpa [prefixWord, tailWord_1356972, baseEnd_1356972] using wordTrace_append hprefix tailTrace_1356972
  have hstable : (prefixWord ++ tailWord_1356972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356972).length < 2 ^ (prefixWord ++ tailWord_1356972).sum := by decide
  have hdescent : baseEnd_1356972 < baseStart_1356972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356999 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1356999 : Nat := 118140960795 + 1356999 * 2 ^ 59
def prefixEnd_1356999 : Nat := 4983230072969 + 3 ^ 40 * 1356999 * 2
def baseEnd_1356999 : Nat := 696792734670641468871781

theorem tailTrace_1356999 : CollatzResearch.WordTrace tailWord_1356999 prefixEnd_1356999 696792734670641468871781 := by
  unfold tailWord_1356999
  simp only [CollatzResearch.WordTrace]
  refine ⟨49493819610831854823194051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32995879740554569882129367 49493819610831854823194051)
  ·
    refine ⟨74240729416247782234791077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49493819610831854823194051 74240729416247782234791077)
    ·
      refine ⟨13920136765546459169023327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74240729416247782234791077 13920136765546459169023327)
      ·
        refine ⟨20880205148319688753534991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13920136765546459169023327 20880205148319688753534991)
        ·
          refine ⟨31320307722479533130302487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20880205148319688753534991 31320307722479533130302487)
          ·
            refine ⟨46980461583719299695453731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31320307722479533130302487 46980461583719299695453731)
            ·
              refine ⟨70470692375578949543180597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46980461583719299695453731 70470692375578949543180597)
              ·
                refine ⟨6606627410210526519673181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70470692375578949543180597 6606627410210526519673181)
                ·
                  refine ⟨2477485278828947444877443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6606627410210526519673181 2477485278828947444877443)
                  ·
                    refine ⟨3716227918243421167316165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2477485278828947444877443 3716227918243421167316165)
                    ·
                      refine ⟨696792734670641468871781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3716227918243421167316165 696792734670641468871781)
                      ·
                        rfl

theorem cell23_1356999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1356999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1356999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1356999 prefixEnd_1356999 := by exact prefixLift 1356999
  have htrace : WordTrace (prefixWord ++ tailWord_1356999) baseStart_1356999 baseEnd_1356999 := by
    simpa [prefixWord, tailWord_1356999, baseEnd_1356999] using wordTrace_append hprefix tailTrace_1356999
  have hstable : (prefixWord ++ tailWord_1356999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356999).length < 2 ^ (prefixWord ++ tailWord_1356999).sum := by decide
  have hdescent : baseEnd_1356999 < baseStart_1356999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357043 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 2, 4]
def baseStart_1357043 : Nat := 118140960795 + 1357043 * 2 ^ 59
def prefixEnd_1357043 : Nat := 4983230072969 + 3 ^ 40 * 1357043 * 2
def baseEnd_1357043 : Nat := 232271775939813098907193

theorem tailTrace_1357043 : CollatzResearch.WordTrace tailWord_1357043 prefixEnd_1357043 232271775939813098907193 := by
  unfold tailWord_1357043
  simp only [CollatzResearch.WordTrace]
  refine ⟨49495424422672450337795783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32996949615114966891863855 49495424422672450337795783)
  ·
    refine ⟨74243136634008675506693675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49495424422672450337795783 74243136634008675506693675)
    ·
      refine ⟨111364704951013013260040513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74243136634008675506693675 111364704951013013260040513)
      ·
        refine ⟨83523528713259759945030385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111364704951013013260040513 83523528713259759945030385)
        ·
          refine ⟨62642646534944819958772789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83523528713259759945030385 62642646534944819958772789)
          ·
            refine ⟨5872748112651076871134949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62642646534944819958772789 5872748112651076871134949)
            ·
              refine ⟨1101140271122076913337803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5872748112651076871134949 1101140271122076913337803)
              ·
                refine ⟨1651710406683115370006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101140271122076913337803 1651710406683115370006705)
                ·
                  refine ⟨1238782805012336527505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651710406683115370006705 1238782805012336527505029)
                  ·
                    refine ⟨232271775939813098907193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238782805012336527505029 232271775939813098907193)
                    ·
                      rfl

theorem cell23_1357043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 4].length) (baseStart_1357043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357043 prefixEnd_1357043 := by exact prefixLift 1357043
  have htrace : WordTrace (prefixWord ++ tailWord_1357043) baseStart_1357043 baseEnd_1357043 := by
    simpa [prefixWord, tailWord_1357043, baseEnd_1357043] using wordTrace_append hprefix tailTrace_1357043
  have hstable : (prefixWord ++ tailWord_1357043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357043).length < 2 ^ (prefixWord ++ tailWord_1357043).sum := by decide
  have hdescent : baseEnd_1357043 < baseStart_1357043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357046 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1357046 : Nat := 118140960795 + 1357046 * 2 ^ 59
def prefixEnd_1357046 : Nat := 4983230072969 + 3 ^ 40 * 1357046 * 2
def baseEnd_1357046 : Nat := 696816868261402784984065

theorem tailTrace_1357046 : CollatzResearch.WordTrace tailWord_1357046 prefixEnd_1357046 696816868261402784984065 := by
  unfold tailWord_1357046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093470865103848865634687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32997022561107721233436661 3093470865103848865634687)
  ·
    refine ⟨4640206297655773298452031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093470865103848865634687 4640206297655773298452031)
    ·
      refine ⟨6960309446483659947678047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640206297655773298452031 6960309446483659947678047)
      ·
        refine ⟨10440464169725489921517071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6960309446483659947678047 10440464169725489921517071)
        ·
          refine ⟨15660696254588234882275607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10440464169725489921517071 15660696254588234882275607)
          ·
            refine ⟨23491044381882352323413411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660696254588234882275607 23491044381882352323413411)
            ·
              refine ⟨35236566572823528485120117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23491044381882352323413411 35236566572823528485120117)
              ·
                refine ⟨3303428116202205795480011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35236566572823528485120117 3303428116202205795480011)
                ·
                  refine ⟨4955142174303308693220017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303428116202205795480011 4955142174303308693220017)
                  ·
                    refine ⟨3716356630727481519915013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955142174303308693220017 3716356630727481519915013)
                    ·
                      refine ⟨696816868261402784984065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3716356630727481519915013 696816868261402784984065)
                      ·
                        rfl

theorem cell23_1357046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1357046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357046 prefixEnd_1357046 := by exact prefixLift 1357046
  have htrace : WordTrace (prefixWord ++ tailWord_1357046) baseStart_1357046 baseEnd_1357046 := by
    simpa [prefixWord, tailWord_1357046, baseEnd_1357046] using wordTrace_append hprefix tailTrace_1357046
  have hstable : (prefixWord ++ tailWord_1357046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357046).length < 2 ^ (prefixWord ++ tailWord_1357046).sum := by decide
  have hdescent : baseEnd_1357046 < baseStart_1357046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357070 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1357070 : Nat := 118140960795 + 1357070 * 2 ^ 59
def prefixEnd_1357070 : Nat := 4983230072969 + 3 ^ 40 * 1357070 * 2
def baseEnd_1357070 : Nat := 696829191797110691083955

theorem tailTrace_1357070 : CollatzResearch.WordTrace tailWord_1357070 prefixEnd_1357070 696829191797110691083955 := by
  unfold tailWord_1357070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187051149196829243628583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32997606129049755966019109 6187051149196829243628583)
  ·
    refine ⟨9280576723795243865442875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6187051149196829243628583 9280576723795243865442875)
    ·
      refine ⟨13920865085692865798164313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280576723795243865442875 13920865085692865798164313)
      ·
        refine ⟨10440648814269649348623235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13920865085692865798164313 10440648814269649348623235)
        ·
          refine ⟨15660973221404474022934853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10440648814269649348623235 15660973221404474022934853)
          ·
            refine ⟨2936432479013338879300285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15660973221404474022934853 2936432479013338879300285)
            ·
              refine ⟨1101162179630002079737607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936432479013338879300285 1101162179630002079737607)
              ·
                refine ⟨1651743269445003119606411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101162179630002079737607 1651743269445003119606411)
                ·
                  refine ⟨2477614904167504679409617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651743269445003119606411 2477614904167504679409617)
                  ·
                    refine ⟨1858211178125628509557213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2477614904167504679409617 1858211178125628509557213)
                    ·
                      refine ⟨696829191797110691083955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858211178125628509557213 696829191797110691083955)
                      ·
                        rfl

theorem cell23_1357070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1357070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357070 prefixEnd_1357070 := by exact prefixLift 1357070
  have htrace : WordTrace (prefixWord ++ tailWord_1357070) baseStart_1357070 baseEnd_1357070 := by
    simpa [prefixWord, tailWord_1357070, baseEnd_1357070] using wordTrace_append hprefix tailTrace_1357070
  have hstable : (prefixWord ++ tailWord_1357070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357070).length < 2 ^ (prefixWord ++ tailWord_1357070).sum := by decide
  have hdescent : baseEnd_1357070 < baseStart_1357070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357093 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_1357093 : Nat := 118140960795 + 1357093 * 2 ^ 59
def prefixEnd_1357093 : Nat := 4983230072969 + 3 ^ 40 * 1357093 * 2
def baseEnd_1357093 : Nat := 696841001852164101096349

theorem tailTrace_1357093 : CollatzResearch.WordTrace tailWord_1357093 prefixEnd_1357093 696841001852164101096349 := by
  unfold tailWord_1357093
  simp only [CollatzResearch.WordTrace]
  refine ⟨49497248072491308877115933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32998165381660872584743955 49497248072491308877115933)
  ·
    refine ⟨18561468027184240828918475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49497248072491308877115933 18561468027184240828918475)
    ·
      refine ⟨27842202040776361243377713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18561468027184240828918475 27842202040776361243377713)
      ·
        refine ⟨20881651530582270932533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27842202040776361243377713 20881651530582270932533285)
        ·
          refine ⟨3915309661984175799849991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20881651530582270932533285 3915309661984175799849991)
          ·
            refine ⟨5872964492976263699774987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915309661984175799849991 5872964492976263699774987)
            ·
              refine ⟨8809446739464395549662481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872964492976263699774987 8809446739464395549662481)
              ·
                refine ⟨6607085054598296662246861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8809446739464395549662481 6607085054598296662246861)
                ·
                  refine ⟨2477656895474361248342573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6607085054598296662246861 2477656895474361248342573)
                  ·
                    refine ⟨929121335802885468128465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477656895474361248342573 929121335802885468128465)
                    ·
                      refine ⟨696841001852164101096349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929121335802885468128465 696841001852164101096349)
                      ·
                        rfl

theorem cell23_1357093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_1357093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357093 prefixEnd_1357093 := by exact prefixLift 1357093
  have htrace : WordTrace (prefixWord ++ tailWord_1357093) baseStart_1357093 baseEnd_1357093 := by
    simpa [prefixWord, tailWord_1357093, baseEnd_1357093] using wordTrace_append hprefix tailTrace_1357093
  have hstable : (prefixWord ++ tailWord_1357093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357093).length < 2 ^ (prefixWord ++ tailWord_1357093).sum := by decide
  have hdescent : baseEnd_1357093 < baseStart_1357093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357123 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 4, 2, 2]
def baseStart_1357123 : Nat := 118140960795 + 1357123 * 2 ^ 59
def prefixEnd_1357123 : Nat := 4983230072969 + 3 ^ 40 * 1357123 * 2
def baseEnd_1357123 : Nat := 696856406271798983721211

theorem tailTrace_1357123 : CollatzResearch.WordTrace tailWord_1357123 prefixEnd_1357123 696856406271798983721211 := by
  unfold tailWord_1357123
  simp only [CollatzResearch.WordTrace]
  refine ⟨49498342262382624000708023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32998894841588416000472015 49498342262382624000708023)
  ·
    refine ⟨74247513393573936001062035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49498342262382624000708023 74247513393573936001062035)
    ·
      refine ⟨111371270090360904001593053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74247513393573936001062035 111371270090360904001593053)
      ·
        refine ⟨41764226283885339000597395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111371270090360904001593053 41764226283885339000597395)
        ·
          refine ⟨62646339425828008500896093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41764226283885339000597395 62646339425828008500896093)
          ·
            refine ⟨23492377284685503187836035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62646339425828008500896093 23492377284685503187836035)
            ·
              refine ⟨35238565927028254781754053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23492377284685503187836035 35238565927028254781754053)
              ·
                refine ⟨6607231111317797771578885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35238565927028254781754053 6607231111317797771578885)
                ·
                  refine ⟨1238855833372087082171041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6607231111317797771578885 1238855833372087082171041)
                  ·
                    refine ⟨929141875029065311628281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238855833372087082171041 929141875029065311628281)
                    ·
                      refine ⟨696856406271798983721211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929141875029065311628281 696856406271798983721211)
                      ·
                        rfl

theorem cell23_1357123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_1357123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357123 prefixEnd_1357123 := by exact prefixLift 1357123
  have htrace : WordTrace (prefixWord ++ tailWord_1357123) baseStart_1357123 baseEnd_1357123 := by
    simpa [prefixWord, tailWord_1357123, baseEnd_1357123] using wordTrace_append hprefix tailTrace_1357123
  have hstable : (prefixWord ++ tailWord_1357123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357123).length < 2 ^ (prefixWord ++ tailWord_1357123).sum := by decide
  have hdescent : baseEnd_1357123 < baseStart_1357123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357127 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_1357127 : Nat := 118140960795 + 1357127 * 2 ^ 59
def prefixEnd_1357127 : Nat := 4983230072969 + 3 ^ 40 * 1357127 * 2
def baseEnd_1357127 : Nat := 696858460194416968071193

theorem tailTrace_1357127 : CollatzResearch.WordTrace tailWord_1357127 prefixEnd_1357127 696858460194416968071193 := by
  unfold tailWord_1357127
  simp only [CollatzResearch.WordTrace]
  refine ⟨49498488154368132683853635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32998992102912088455902423 49498488154368132683853635)
  ·
    refine ⟨74247732231552199025780453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49498488154368132683853635 74247732231552199025780453)
    ·
      refine ⟨13921449793416037317333835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74247732231552199025780453 13921449793416037317333835)
      ·
        refine ⟨20882174690124055976000753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921449793416037317333835 20882174690124055976000753)
        ·
          refine ⟨15661631017593041982000565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20882174690124055976000753 15661631017593041982000565)
          ·
            refine ⟨1468277907899347685812553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15661631017593041982000565 1468277907899347685812553)
            ·
              refine ⟨1101208430924510764359415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468277907899347685812553 1101208430924510764359415)
              ·
                refine ⟨1651812646386766146539123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101208430924510764359415 1651812646386766146539123)
                ·
                  refine ⟨2477718969580149219808685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651812646386766146539123 2477718969580149219808685)
                  ·
                    refine ⟨929144613592555957428257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477718969580149219808685 929144613592555957428257)
                    ·
                      refine ⟨696858460194416968071193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929144613592555957428257 696858460194416968071193)
                      ·
                        rfl

theorem cell23_1357127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_1357127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357127 prefixEnd_1357127 := by exact prefixLift 1357127
  have htrace : WordTrace (prefixWord ++ tailWord_1357127) baseStart_1357127 baseEnd_1357127 := by
    simpa [prefixWord, tailWord_1357127, baseEnd_1357127] using wordTrace_append hprefix tailTrace_1357127
  have hstable : (prefixWord ++ tailWord_1357127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357127).length < 2 ^ (prefixWord ++ tailWord_1357127).sum := by decide
  have hdescent : baseEnd_1357127 < baseStart_1357127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357140 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_1357140 : Nat := 118140960795 + 1357140 * 2 ^ 59
def prefixEnd_1357140 : Nat := 4983230072969 + 3 ^ 40 * 1357140 * 2
def baseEnd_1357140 : Nat := 696865135442925417208633

theorem tailTrace_1357140 : CollatzResearch.WordTrace tailWord_1357140 prefixEnd_1357140 696865135442925417208633 := by
  unfold tailWord_1357140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24749481151660517952038437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32999308202214023936051249 24749481151660517952038437)
  ·
    refine ⟨4640527715936347116007207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24749481151660517952038437 4640527715936347116007207)
    ·
      refine ⟨6960791573904520674010811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640527715936347116007207 6960791573904520674010811)
      ·
        refine ⟨10441187360856781011016217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6960791573904520674010811 10441187360856781011016217)
        ·
          refine ⟨7830890520642585758262163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10441187360856781011016217 7830890520642585758262163)
          ·
            refine ⟨11746335780963878637393245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7830890520642585758262163 11746335780963878637393245)
            ·
              refine ⟨4404875917861454489022467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11746335780963878637393245 4404875917861454489022467)
              ·
                refine ⟨6607313876792181733533701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404875917861454489022467 6607313876792181733533701)
                ·
                  refine ⟨1238871351898534075037569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6607313876792181733533701 1238871351898534075037569)
                  ·
                    refine ⟨929153513923900556278177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238871351898534075037569 929153513923900556278177)
                    ·
                      refine ⟨696865135442925417208633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929153513923900556278177 696865135442925417208633)
                      ·
                        rfl

theorem cell23_1357140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_1357140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357140 prefixEnd_1357140 := by exact prefixLift 1357140
  have htrace : WordTrace (prefixWord ++ tailWord_1357140) baseStart_1357140 baseEnd_1357140 := by
    simpa [prefixWord, tailWord_1357140, baseEnd_1357140] using wordTrace_append hprefix tailTrace_1357140
  have hstable : (prefixWord ++ tailWord_1357140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357140).length < 2 ^ (prefixWord ++ tailWord_1357140).sum := by decide
  have hdescent : baseEnd_1357140 < baseStart_1357140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357157 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_1357157 : Nat := 118140960795 + 1357157 * 2 ^ 59
def prefixEnd_1357157 : Nat := 4983230072969 + 3 ^ 40 * 1357157 * 2
def baseEnd_1357157 : Nat := 696873864614051850696055

theorem tailTrace_1357157 : CollatzResearch.WordTrace tailWord_1357157 prefixEnd_1357157 696873864614051850696055 := by
  unfold tailWord_1357157
  simp only [CollatzResearch.WordTrace]
  refine ⟨49499582344259447807445725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32999721562839631871630483 49499582344259447807445725)
  ·
    refine ⟨18562343379097292927792147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49499582344259447807445725 18562343379097292927792147)
    ·
      refine ⟨27843515068645939391688221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562343379097292927792147 27843515068645939391688221)
      ·
        refine ⟨10441318150742227271883083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27843515068645939391688221 10441318150742227271883083)
        ·
          refine ⟨15661977226113340907824625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441318150742227271883083 15661977226113340907824625)
          ·
            refine ⟨11746482919585005680868469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15661977226113340907824625 11746482919585005680868469)
            ·
              refine ⟨1101232773711094282581419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11746482919585005680868469 1101232773711094282581419)
              ·
                refine ⟨1651849160566641423872129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101232773711094282581419 1651849160566641423872129)
                ·
                  refine ⟨1238886870424981067904097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651849160566641423872129 1238886870424981067904097)
                  ·
                    refine ⟨929165152818735800928073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238886870424981067904097 929165152818735800928073)
                    ·
                      refine ⟨696873864614051850696055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929165152818735800928073 696873864614051850696055)
                      ·
                        rfl

theorem cell23_1357157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_1357157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357157 prefixEnd_1357157 := by exact prefixLift 1357157
  have htrace : WordTrace (prefixWord ++ tailWord_1357157) baseStart_1357157 baseEnd_1357157 := by
    simpa [prefixWord, tailWord_1357157, baseEnd_1357157] using wordTrace_append hprefix tailTrace_1357157
  have hstable : (prefixWord ++ tailWord_1357157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357157).length < 2 ^ (prefixWord ++ tailWord_1357157).sum := by decide
  have hdescent : baseEnd_1357157 < baseStart_1357157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357193 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_1357193 : Nat := 118140960795 + 1357193 * 2 ^ 59
def prefixEnd_1357193 : Nat := 4983230072969 + 3 ^ 40 * 1357193 * 2
def baseEnd_1357193 : Nat := 232297449972537903281963

theorem tailTrace_1357193 : CollatzResearch.WordTrace tailWord_1357193 prefixEnd_1357193 232297449972537903281963 := by
  unfold tailWord_1357193
  simp only [CollatzResearch.WordTrace]
  refine ⟨49500895372129025955756233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33000596914752683970504155 49500895372129025955756233)
  ·
    refine ⟨37125671529096769466817175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49500895372129025955756233 37125671529096769466817175)
    ·
      refine ⟨55688507293645154200225763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37125671529096769466817175 55688507293645154200225763)
      ·
        refine ⟨83532760940467731300338645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55688507293645154200225763 83532760940467731300338645)
        ·
          refine ⟨1957799084542212452351687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83532760940467731300338645 1957799084542212452351687)
          ·
            refine ⟨2936698626813318678527531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957799084542212452351687 2936698626813318678527531)
            ·
              refine ⟨4405047940219978017791297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936698626813318678527531 4405047940219978017791297)
              ·
                refine ⟨3303785955164983513343473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4405047940219978017791297 3303785955164983513343473)
                ·
                  refine ⟨2477839466373737635007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303785955164983513343473 2477839466373737635007605)
                  ·
                    refine ⟨232297449972537903281963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2477839466373737635007605 232297449972537903281963)
                    ·
                      rfl

theorem cell23_1357193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_1357193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357193 prefixEnd_1357193 := by exact prefixLift 1357193
  have htrace : WordTrace (prefixWord ++ tailWord_1357193) baseStart_1357193 baseEnd_1357193 := by
    simpa [prefixWord, tailWord_1357193, baseEnd_1357193] using wordTrace_append hprefix tailTrace_1357193
  have hstable : (prefixWord ++ tailWord_1357193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357193).length < 2 ^ (prefixWord ++ tailWord_1357193).sum := by decide
  have hdescent : baseEnd_1357193 < baseStart_1357193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357223 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1357223 : Nat := 118140960795 + 1357223 * 2 ^ 59
def prefixEnd_1357223 : Nat := 4983230072969 + 3 ^ 40 * 1357223 * 2
def baseEnd_1357223 : Nat := 232302584779082864156917

theorem tailTrace_1357223 : CollatzResearch.WordTrace tailWord_1357223 prefixEnd_1357223 232302584779082864156917 := by
  unfold tailWord_1357223
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501989562020341079348323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33001326374680227386232215 49501989562020341079348323)
  ·
    refine ⟨74252984343030511619022485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49501989562020341079348323 74252984343030511619022485)
    ·
      refine ⟨3480608641079555232141679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74252984343030511619022485 3480608641079555232141679)
      ·
        refine ⟨5220912961619332848212519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480608641079555232141679 5220912961619332848212519)
        ·
          refine ⟨7831369442428999272318779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220912961619332848212519 7831369442428999272318779)
          ·
            refine ⟨11747054163643498908478169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831369442428999272318779 11747054163643498908478169)
            ·
              refine ⟨8810290622732624181358627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747054163643498908478169 8810290622732624181358627)
              ·
                refine ⟨13215435934098936272037941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810290622732624181358627 13215435934098936272037941)
                ·
                  refine ⟨1238947118821775275503557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13215435934098936272037941 1238947118821775275503557)
                  ·
                    refine ⟨232302584779082864156917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1238947118821775275503557 232302584779082864156917)
                    ·
                      rfl

theorem cell23_1357223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1357223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357223 prefixEnd_1357223 := by exact prefixLift 1357223
  have htrace : WordTrace (prefixWord ++ tailWord_1357223) baseStart_1357223 baseEnd_1357223 := by
    simpa [prefixWord, tailWord_1357223, baseEnd_1357223] using wordTrace_append hprefix tailTrace_1357223
  have hstable : (prefixWord ++ tailWord_1357223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357223).length < 2 ^ (prefixWord ++ tailWord_1357223).sum := by decide
  have hdescent : baseEnd_1357223 < baseStart_1357223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357256 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1357256 : Nat := 118140960795 + 1357256 * 2 ^ 59
def prefixEnd_1357256 : Nat := 4983230072969 + 3 ^ 40 * 1357256 * 2
def baseEnd_1357256 : Nat := 696924699198846963358099

theorem tailTrace_1357256 : CollatzResearch.WordTrace tailWord_1357256 prefixEnd_1357256 696924699198846963358099 := by
  unfold tailWord_1357256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751596585450393857649811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33002128780600525143533081 24751596585450393857649811)
  ·
    refine ⟨37127394878175590786474717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24751596585450393857649811 37127394878175590786474717)
    ·
      refine ⟨13922773079315846544928019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37127394878175590786474717 13922773079315846544928019)
      ·
        refine ⟨20884159618973769817392029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13922773079315846544928019 20884159618973769817392029)
        ·
          refine ⟨7831559857115163681522011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20884159618973769817392029 7831559857115163681522011)
          ·
            refine ⟨11747339785672745522283017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831559857115163681522011 11747339785672745522283017)
            ·
              refine ⟨8810504839254559141712263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747339785672745522283017 8810504839254559141712263)
              ·
                refine ⟨13215757258881838712568395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810504839254559141712263 13215757258881838712568395)
                ·
                  refine ⟨19823635888322758068852593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13215757258881838712568395 19823635888322758068852593)
                  ·
                    refine ⟨14867726916242068551639445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19823635888322758068852593 14867726916242068551639445)
                    ·
                      refine ⟨696924699198846963358099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14867726916242068551639445 696924699198846963358099)
                      ·
                        rfl

theorem cell23_1357256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1357256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357256 prefixEnd_1357256 := by exact prefixLift 1357256
  have htrace : WordTrace (prefixWord ++ tailWord_1357256) baseStart_1357256 baseEnd_1357256 := by
    simpa [prefixWord, tailWord_1357256, baseEnd_1357256] using wordTrace_append hprefix tailTrace_1357256
  have hstable : (prefixWord ++ tailWord_1357256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357256).length < 2 ^ (prefixWord ++ tailWord_1357256).sum := by decide
  have hdescent : baseEnd_1357256 < baseStart_1357256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357270 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1357270 : Nat := 118140960795 + 1357270 * 2 ^ 59
def prefixEnd_1357270 : Nat := 4983230072969 + 3 ^ 40 * 1357270 * 2
def baseEnd_1357270 : Nat := 77436876436445545398115

theorem tailTrace_1357270 : CollatzResearch.WordTrace tailWord_1357270 prefixEnd_1357270 77436876436445545398115 := by
  unfold tailWord_1357270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093981487053129256644329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33002469195233378737539509 3093981487053129256644329)
  ·
    refine ⟨2320486115289846942483247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093981487053129256644329 2320486115289846942483247)
    ·
      refine ⟨3480729172934770413724871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320486115289846942483247 3480729172934770413724871)
      ·
        refine ⟨5221093759402155620587307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480729172934770413724871 5221093759402155620587307)
        ·
          refine ⟨7831640639103233430880961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221093759402155620587307 7831640639103233430880961)
          ·
            refine ⟨5873730479327425073160721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831640639103233430880961 5873730479327425073160721)
            ·
              refine ⟨4405297859495568804870541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873730479327425073160721 4405297859495568804870541)
              ·
                refine ⟨1651986697310838301826453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405297859495568804870541 1651986697310838301826453)
                ·
                  refine ⟨77436876436445545398115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1651986697310838301826453 77436876436445545398115)
                  ·
                    rfl

theorem cell23_1357270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1357270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357270 prefixEnd_1357270 := by exact prefixLift 1357270
  have htrace : WordTrace (prefixWord ++ tailWord_1357270) baseStart_1357270 baseEnd_1357270 := by
    simpa [prefixWord, tailWord_1357270, baseEnd_1357270] using wordTrace_append hprefix tailTrace_1357270
  have hstable : (prefixWord ++ tailWord_1357270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357270).length < 2 ^ (prefixWord ++ tailWord_1357270).sum := by decide
  have hdescent : baseEnd_1357270 < baseStart_1357270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357283 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 3, 5]
def baseStart_1357283 : Nat := 118140960795 + 1357283 * 2 ^ 59
def prefixEnd_1357283 : Nat := 4983230072969 + 3 ^ 40 * 1357283 * 2
def baseEnd_1357283 : Nat := 232312854392172785906825

theorem tailTrace_1357283 : CollatzResearch.WordTrace tailWord_1357283 prefixEnd_1357283 232312854392172785906825 := by
  unfold tailWord_1357283
  simp only [CollatzResearch.WordTrace]
  refine ⟨49504177941802971326532503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33002785294535314217688335 49504177941802971326532503)
  ·
    refine ⟨74256266912704456989798755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49504177941802971326532503 74256266912704456989798755)
    ·
      refine ⟨111384400369056685484698133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74256266912704456989798755 111384400369056685484698133)
      ·
        refine ⟨5221143767299532132095225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111384400369056685484698133 5221143767299532132095225)
        ·
          refine ⟨3915857825474649099071419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5221143767299532132095225 3915857825474649099071419)
          ·
            refine ⟨5873786738211973648607129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915857825474649099071419 5873786738211973648607129)
            ·
              refine ⟨4405340053658980236455347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873786738211973648607129 4405340053658980236455347)
              ·
                refine ⟨6608010080488470354683021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405340053658980236455347 6608010080488470354683021)
                ·
                  refine ⟨2478003780183176383006133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6608010080488470354683021 2478003780183176383006133)
                  ·
                    refine ⟨232312854392172785906825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2478003780183176383006133 232312854392172785906825)
                    ·
                      rfl

theorem cell23_1357283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].length) (baseStart_1357283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357283 prefixEnd_1357283 := by exact prefixLift 1357283
  have htrace : WordTrace (prefixWord ++ tailWord_1357283) baseStart_1357283 baseEnd_1357283 := by
    simpa [prefixWord, tailWord_1357283, baseEnd_1357283] using wordTrace_append hprefix tailTrace_1357283
  have hstable : (prefixWord ++ tailWord_1357283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357283).length < 2 ^ (prefixWord ++ tailWord_1357283).sum := by decide
  have hdescent : baseEnd_1357283 < baseStart_1357283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357297 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_1357297 : Nat := 118140960795 + 1357297 * 2 ^ 59
def prefixEnd_1357297 : Nat := 4983230072969 + 3 ^ 40 * 1357297 * 2
def baseEnd_1357297 : Nat := 696945751905681302945411

theorem tailTrace_1357297 : CollatzResearch.WordTrace tailWord_1357297 prefixEnd_1357297 696945751905681302945411 := by
  unfold tailWord_1357297
  simp only [CollatzResearch.WordTrace]
  refine ⟨49504688563752251717542145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33003125709168167811694763 49504688563752251717542145)
  ·
    refine ⟨37128516422814188788156609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49504688563752251717542145 37128516422814188788156609)
    ·
      refine ⟨27846387317110641591117457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37128516422814188788156609 27846387317110641591117457)
      ·
        refine ⟨20884790487832981193338093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27846387317110641591117457 20884790487832981193338093)
        ·
          refine ⟨7831796432937367947501785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20884790487832981193338093 7831796432937367947501785)
          ·
            refine ⟨5873847324703025960626339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831796432937367947501785 5873847324703025960626339)
            ·
              refine ⟨8810770987054538940939509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873847324703025960626339 8810770987054538940939509)
              ·
                refine ⟨826009780036363025713079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8810770987054538940939509 826009780036363025713079)
                ·
                  refine ⟨1239014670054544538569619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826009780036363025713079 1239014670054544538569619)
                  ·
                    refine ⟨1858522005081816807854429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239014670054544538569619 1858522005081816807854429)
                    ·
                      refine ⟨696945751905681302945411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858522005081816807854429 696945751905681302945411)
                      ·
                        rfl

theorem cell23_1357297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_1357297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357297 prefixEnd_1357297 := by exact prefixLift 1357297
  have htrace : WordTrace (prefixWord ++ tailWord_1357297) baseStart_1357297 baseEnd_1357297 := by
    simpa [prefixWord, tailWord_1357297, baseEnd_1357297] using wordTrace_append hprefix tailTrace_1357297
  have hstable : (prefixWord ++ tailWord_1357297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357297).length < 2 ^ (prefixWord ++ tailWord_1357297).sum := by decide
  have hdescent : baseEnd_1357297 < baseStart_1357297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357314 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1357314 : Nat := 118140960795 + 1357314 * 2 ^ 59
def prefixEnd_1357314 : Nat := 4983230072969 + 3 ^ 40 * 1357314 * 2
def baseEnd_1357314 : Nat := 696954481076807736432833

theorem tailTrace_1357314 : CollatzResearch.WordTrace tailWord_1357314 prefixEnd_1357314 696954481076807736432833 := by
  unfold tailWord_1357314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376327151172665905227749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33003539069793775747273997 12376327151172665905227749)
  ·
    refine ⟨2320561340844874857230203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12376327151172665905227749 2320561340844874857230203)
    ·
      refine ⟨3480842011267312285845305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320561340844874857230203 3480842011267312285845305)
      ·
        refine ⟨2610631508450484214383979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480842011267312285845305 2610631508450484214383979)
        ·
          refine ⟨3915947262675726321575969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610631508450484214383979 3915947262675726321575969)
          ·
            refine ⟨2936960447006794741181977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915947262675726321575969 2936960447006794741181977)
            ·
              refine ⟨2202720335255096055886483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936960447006794741181977 2202720335255096055886483)
              ·
                refine ⟨3304080502882644083829725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202720335255096055886483 3304080502882644083829725)
                ·
                  refine ⟨1239030188580991531436147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3304080502882644083829725 1239030188580991531436147)
                  ·
                    refine ⟨1858545282871487297154221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239030188580991531436147 1858545282871487297154221)
                    ·
                      refine ⟨696954481076807736432833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858545282871487297154221 696954481076807736432833)
                      ·
                        rfl

theorem cell23_1357314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1357314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357314 prefixEnd_1357314 := by exact prefixLift 1357314
  have htrace : WordTrace (prefixWord ++ tailWord_1357314) baseStart_1357314 baseEnd_1357314 := by
    simpa [prefixWord, tailWord_1357314, baseEnd_1357314] using wordTrace_append hprefix tailTrace_1357314
  have hstable : (prefixWord ++ tailWord_1357314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357314).length < 2 ^ (prefixWord ++ tailWord_1357314).sum := by decide
  have hdescent : baseEnd_1357314 < baseStart_1357314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357333 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1357333 : Nat := 118140960795 + 1357333 * 2 ^ 59
def prefixEnd_1357333 : Nat := 4983230072969 + 3 ^ 40 * 1357333 * 2
def baseEnd_1357333 : Nat := 696964237209243162095245

theorem tailTrace_1357333 : CollatzResearch.WordTrace tailWord_1357333 prefixEnd_1357333 696964237209243162095245 := by
  unfold tailWord_1357333
  simp only [CollatzResearch.WordTrace]
  refine ⟨49506001591621829865852653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33004001061081219910568435 49506001591621829865852653)
  ·
    refine ⟨18564750596858186199694745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49506001591621829865852653 18564750596858186199694745)
    ·
      refine ⟨13923562947643639649771059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18564750596858186199694745 13923562947643639649771059)
      ·
        refine ⟨20885344421465459474656589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923562947643639649771059 20885344421465459474656589)
        ·
          refine ⟨7832004158049547302996221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20885344421465459474656589 7832004158049547302996221)
          ·
            refine ⟨2937001559268580238623583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7832004158049547302996221 2937001559268580238623583)
            ·
              refine ⟨4405502338902870357935375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937001559268580238623583 4405502338902870357935375)
              ·
                refine ⟨6608253508354305536903063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405502338902870357935375 6608253508354305536903063)
                ·
                  refine ⟨9912380262531458305354595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608253508354305536903063 9912380262531458305354595)
                  ·
                    refine ⟨14868570393797187458031893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9912380262531458305354595 14868570393797187458031893)
                    ·
                      refine ⟨696964237209243162095245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14868570393797187458031893 696964237209243162095245)
                      ·
                        rfl

theorem cell23_1357333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1357333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357333 prefixEnd_1357333 := by exact prefixLift 1357333
  have htrace : WordTrace (prefixWord ++ tailWord_1357333) baseStart_1357333 baseEnd_1357333 := by
    simpa [prefixWord, tailWord_1357333, baseEnd_1357333] using wordTrace_append hprefix tailTrace_1357333
  have hstable : (prefixWord ++ tailWord_1357333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357333).length < 2 ^ (prefixWord ++ tailWord_1357333).sum := by decide
  have hdescent : baseEnd_1357333 < baseStart_1357333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357343 : List Nat := [1, 1, 2, 4, 1, 1, 6, 7]
def baseStart_1357343 : Nat := 118140960795 + 1357343 * 2 ^ 59
def prefixEnd_1357343 : Nat := 4983230072969 + 3 ^ 40 * 1357343 * 2
def baseEnd_1357343 : Nat := 25813680445029189739637

theorem tailTrace_1357343 : CollatzResearch.WordTrace tailWord_1357343 prefixEnd_1357343 25813680445029189739637 := by
  unfold tailWord_1357343
  simp only [CollatzResearch.WordTrace]
  refine ⟨49506366321585601573716683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33004244214390401049144455 49506366321585601573716683)
  ·
    refine ⟨74259549482378402360575025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49506366321585601573716683 74259549482378402360575025)
    ·
      refine ⟨55694662111783801770431269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74259549482378402360575025 55694662111783801770431269)
      ·
        refine ⟨10442749145959462831955863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55694662111783801770431269 10442749145959462831955863)
        ·
          refine ⟨15664123718939194247933795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442749145959462831955863 15664123718939194247933795)
          ·
            refine ⟨23496185578408791371900693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664123718939194247933795 23496185578408791371900693)
            ·
              refine ⟨1101383698987912095557845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23496185578408791371900693 1101383698987912095557845)
              ·
                refine ⟨25813680445029189739637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1101383698987912095557845 25813680445029189739637)
                ·
                  rfl

theorem cell23_1357343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 7].length) (baseStart_1357343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357343 prefixEnd_1357343 := by exact prefixLift 1357343
  have htrace : WordTrace (prefixWord ++ tailWord_1357343) baseStart_1357343 baseEnd_1357343 := by
    simpa [prefixWord, tailWord_1357343, baseEnd_1357343] using wordTrace_append hprefix tailTrace_1357343
  have hstable : (prefixWord ++ tailWord_1357343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357343).length < 2 ^ (prefixWord ++ tailWord_1357343).sum := by decide
  have hdescent : baseEnd_1357343 < baseStart_1357343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357356 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1357356 : Nat := 118140960795 + 1357356 * 2 ^ 59
def prefixEnd_1357356 : Nat := 4983230072969 + 3 ^ 40 * 1357356 * 2
def baseEnd_1357356 : Nat := 232325349088098857369213

theorem tailTrace_1357356 : CollatzResearch.WordTrace tailWord_1357356 prefixEnd_1357356 232325349088098857369213 := by
  unfold tailWord_1357356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753420235269252396969961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33004560313692336529293281 24753420235269252396969961)
  ·
    refine ⟨18565065176451939297727471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24753420235269252396969961 18565065176451939297727471)
    ·
      refine ⟨27847597764677908946591207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18565065176451939297727471 27847597764677908946591207)
      ·
        refine ⟨41771396647016863419886811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847597764677908946591207 41771396647016863419886811)
        ·
          refine ⟨62657094970525295129830217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41771396647016863419886811 62657094970525295129830217)
          ·
            refine ⟨46992821227893971347372663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62657094970525295129830217 46992821227893971347372663)
            ·
              refine ⟨70489231841840957021058995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46992821227893971347372663 70489231841840957021058995)
              ·
                refine ⟨105733847762761435531588493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70489231841840957021058995 105733847762761435531588493)
                ·
                  refine ⟨39650192911035538324345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105733847762761435531588493 39650192911035538324345685)
                  ·
                    refine ⟨232325349088098857369213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39650192911035538324345685 232325349088098857369213)
                    ·
                      rfl

theorem cell23_1357356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1357356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357356 prefixEnd_1357356 := by exact prefixLift 1357356
  have htrace : WordTrace (prefixWord ++ tailWord_1357356) baseStart_1357356 baseEnd_1357356 := by
    simpa [prefixWord, tailWord_1357356, baseEnd_1357356] using wordTrace_append hprefix tailTrace_1357356
  have hstable : (prefixWord ++ tailWord_1357356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357356).length < 2 ^ (prefixWord ++ tailWord_1357356).sum := by decide
  have hdescent : baseEnd_1357356 < baseStart_1357356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357370 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_1357370 : Nat := 118140960795 + 1357370 * 2 ^ 59
def prefixEnd_1357370 : Nat := 4983230072969 + 3 ^ 40 * 1357370 * 2
def baseEnd_1357370 : Nat := 696983235993459517332575

theorem tailTrace_1357370 : CollatzResearch.WordTrace tailWord_1357370 prefixEnd_1357370 696983235993459517332575 := by
  unfold tailWord_1357370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376837773121946296237391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33004900728325190123299709 12376837773121946296237391)
  ·
    refine ⟨18565256659682919444356087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376837773121946296237391 18565256659682919444356087)
    ·
      refine ⟨27847884989524379166534131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18565256659682919444356087 27847884989524379166534131)
      ·
        refine ⟨41771827484286568749801197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847884989524379166534131 41771827484286568749801197)
        ·
          refine ⟨15664435306607463281175449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41771827484286568749801197 15664435306607463281175449)
          ·
            refine ⟨11748326479955597460881587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15664435306607463281175449 11748326479955597460881587)
            ·
              refine ⟨17622489719933396191322381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748326479955597460881587 17622489719933396191322381)
              ·
                refine ⟨6608433644975023571745893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17622489719933396191322381 6608433644975023571745893)
                ·
                  refine ⟨1239081308432816919702355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6608433644975023571745893 1239081308432816919702355)
                  ·
                    refine ⟨1858621962649225379553533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239081308432816919702355 1858621962649225379553533)
                    ·
                      refine ⟨696983235993459517332575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858621962649225379553533 696983235993459517332575)
                      ·
                        rfl

theorem cell23_1357370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_1357370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357370 prefixEnd_1357370 := by exact prefixLift 1357370
  have htrace : WordTrace (prefixWord ++ tailWord_1357370) baseStart_1357370 baseEnd_1357370 := by
    simpa [prefixWord, tailWord_1357370, baseEnd_1357370] using wordTrace_append hprefix tailTrace_1357370
  have hstable : (prefixWord ++ tailWord_1357370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357370).length < 2 ^ (prefixWord ++ tailWord_1357370).sum := by decide
  have hdescent : baseEnd_1357370 < baseStart_1357370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357423 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_1357423 : Nat := 118140960795 + 1357423 * 2 ^ 59
def prefixEnd_1357423 : Nat := 4983230072969 + 3 ^ 40 * 1357423 * 2
def baseEnd_1357423 : Nat := 697010450468147809969831

theorem tailTrace_1357423 : CollatzResearch.WordTrace tailWord_1357423 prefixEnd_1357423 697010450468147809969831 := by
  unfold tailWord_1357423
  simp only [CollatzResearch.WordTrace]
  refine ⟨49509284161295775236628923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33006189440863850157752615 49509284161295775236628923)
  ·
    refine ⟨74263926241943662854943385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49509284161295775236628923 74263926241943662854943385)
    ·
      refine ⟨55697944681457747141207539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74263926241943662854943385 55697944681457747141207539)
      ·
        refine ⟨83546917022186620711811309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55697944681457747141207539 83546917022186620711811309)
        ·
          refine ⟨31330093883319982766929241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83546917022186620711811309 31330093883319982766929241)
          ·
            refine ⟨23497570412489987075196931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31330093883319982766929241 23497570412489987075196931)
            ·
              refine ⟨35246355618734980612795397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23497570412489987075196931 35246355618734980612795397)
              ·
                refine ⟨6608691678512808864899137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35246355618734980612795397 6608691678512808864899137)
                ·
                  refine ⟨4956518758884606648674353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6608691678512808864899137 4956518758884606648674353)
                  ·
                    refine ⟨3717389069163454986505765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956518758884606648674353 3717389069163454986505765)
                    ·
                      refine ⟨697010450468147809969831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3717389069163454986505765 697010450468147809969831)
                      ·
                        rfl

theorem cell23_1357423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_1357423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357423 prefixEnd_1357423 := by exact prefixLift 1357423
  have htrace : WordTrace (prefixWord ++ tailWord_1357423) baseStart_1357423 baseEnd_1357423 := by
    simpa [prefixWord, tailWord_1357423, baseEnd_1357423] using wordTrace_append hprefix tailTrace_1357423
  have hstable : (prefixWord ++ tailWord_1357423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357423).length < 2 ^ (prefixWord ++ tailWord_1357423).sum := by decide
  have hdescent : baseEnd_1357423 < baseStart_1357423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357433 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 7]
def baseStart_1357433 : Nat := 118140960795 + 1357433 * 2 ^ 59
def prefixEnd_1357433 : Nat := 4983230072969 + 3 ^ 40 * 1357433 * 2
def baseEnd_1357433 : Nat := 77446176141632530093865

theorem tailTrace_1357433 : CollatzResearch.WordTrace tailWord_1357433 prefixEnd_1357433 77446176141632530093865 := by
  unfold tailWord_1357433
  simp only [CollatzResearch.WordTrace]
  refine ⟨49509648891259546944492953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33006432594173031296328635 49509648891259546944492953)
  ·
    refine ⟨37132236668444660208369715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49509648891259546944492953 37132236668444660208369715)
    ·
      refine ⟨55698355002666990312554573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37132236668444660208369715 55698355002666990312554573)
      ·
        refine ⟨20886883126000121367207965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55698355002666990312554573 20886883126000121367207965)
        ·
          refine ⟨7832581172250045512702987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20886883126000121367207965 7832581172250045512702987)
          ·
            refine ⟨11748871758375068269054481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832581172250045512702987 11748871758375068269054481)
            ·
              refine ⟨8811653818781301201790861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11748871758375068269054481 8811653818781301201790861)
              ·
                refine ⟨3304370182042987950671573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8811653818781301201790861 3304370182042987950671573)
                ·
                  refine ⟨77446176141632530093865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3304370182042987950671573 77446176141632530093865)
                  ·
                    rfl

theorem cell23_1357433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_1357433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357433 prefixEnd_1357433 := by exact prefixLift 1357433
  have htrace : WordTrace (prefixWord ++ tailWord_1357433) baseStart_1357433 baseEnd_1357433 := by
    simpa [prefixWord, tailWord_1357433, baseEnd_1357433] using wordTrace_append hprefix tailTrace_1357433
  have hstable : (prefixWord ++ tailWord_1357433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357433).length < 2 ^ (prefixWord ++ tailWord_1357433).sum := by decide
  have hdescent : baseEnd_1357433 < baseStart_1357433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357444 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_1357444 : Nat := 118140960795 + 1357444 * 2 ^ 59
def prefixEnd_1357444 : Nat := 4983230072969 + 3 ^ 40 * 1357444 * 2
def baseEnd_1357444 : Nat := 697021233561892227807235

theorem tailTrace_1357444 : CollatzResearch.WordTrace tailWord_1357444 prefixEnd_1357444 697021233561892227807235 := by
  unfold tailWord_1357444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24755025047109847911571693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33006700062813130548762257 24755025047109847911571693)
  ·
    refine ⟨9283134392666192966839385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24755025047109847911571693 9283134392666192966839385)
    ·
      refine ⟨6962350794499644725129539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9283134392666192966839385 6962350794499644725129539)
      ·
        refine ⟨10443526191749467087694309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962350794499644725129539 10443526191749467087694309)
        ·
          refine ⟨1958161160953025078942683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10443526191749467087694309 1958161160953025078942683)
          ·
            refine ⟨2937241741429537618414025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958161160953025078942683 2937241741429537618414025)
            ·
              refine ⟨2202931306072153213810519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937241741429537618414025 2202931306072153213810519)
              ·
                refine ⟨3304396959108229820715779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202931306072153213810519 3304396959108229820715779)
                ·
                  refine ⟨4956595438662344731073669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304396959108229820715779 4956595438662344731073669)
                  ·
                    refine ⟨929361644749189637076313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956595438662344731073669 929361644749189637076313)
                    ·
                      refine ⟨697021233561892227807235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929361644749189637076313 697021233561892227807235)
                      ·
                        rfl

theorem cell23_1357444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_1357444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357444 prefixEnd_1357444 := by exact prefixLift 1357444
  have htrace : WordTrace (prefixWord ++ tailWord_1357444) baseStart_1357444 baseEnd_1357444 := by
    simpa [prefixWord, tailWord_1357444, baseEnd_1357444] using wordTrace_append hprefix tailTrace_1357444
  have hstable : (prefixWord ++ tailWord_1357444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357444).length < 2 ^ (prefixWord ++ tailWord_1357444).sum := by decide
  have hdescent : baseEnd_1357444 < baseStart_1357444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357450 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_1357450 : Nat := 118140960795 + 1357450 * 2 ^ 59
def prefixEnd_1357450 : Nat := 4983230072969 + 3 ^ 40 * 1357450 * 2
def baseEnd_1357450 : Nat := 77447146049535467148023

theorem tailTrace_1357450 : CollatzResearch.WordTrace tailWord_1357450 prefixEnd_1357450 77447146049535467148023 := by
  unfold tailWord_1357450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12377567233049489711965451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33006845954798639231907869 12377567233049489711965451)
  ·
    refine ⟨18566350849574234567948177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12377567233049489711965451 18566350849574234567948177)
    ·
      refine ⟨13924763137180675925961133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18566350849574234567948177 13924763137180675925961133)
      ·
        refine ⟨5221786176442753472235425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13924763137180675925961133 5221786176442753472235425)
        ·
          refine ⟨3916339632332065104176569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5221786176442753472235425 3916339632332065104176569)
          ·
            refine ⟨2937254724249048828132427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3916339632332065104176569 2937254724249048828132427)
            ·
              refine ⟨4405882086373573242198641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937254724249048828132427 4405882086373573242198641)
              ·
                refine ⟨3304411564780179931648981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4405882086373573242198641 3304411564780179931648981)
                ·
                  refine ⟨77447146049535467148023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3304411564780179931648981 77447146049535467148023)
                  ·
                    rfl

theorem cell23_1357450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_1357450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357450 prefixEnd_1357450 := by exact prefixLift 1357450
  have htrace : WordTrace (prefixWord ++ tailWord_1357450) baseStart_1357450 baseEnd_1357450 := by
    simpa [prefixWord, tailWord_1357450, baseEnd_1357450] using wordTrace_append hprefix tailTrace_1357450
  have hstable : (prefixWord ++ tailWord_1357450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357450).length < 2 ^ (prefixWord ++ tailWord_1357450).sum := by decide
  have hdescent : baseEnd_1357450 < baseStart_1357450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357494 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1357494 : Nat := 118140960795 + 1357494 * 2 ^ 59
def prefixEnd_1357494 : Nat := 4983230072969 + 3 ^ 40 * 1357494 * 2
def baseEnd_1357494 : Nat := 697046907594617032182005

theorem tailTrace_1357494 : CollatzResearch.WordTrace tailWord_1357494 prefixEnd_1357494 697046907594617032182005 := by
  unfold tailWord_1357494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094492109002409647653971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33007915829359036241642357 3094492109002409647653971)
  ·
    refine ⟨4641738163503614471480957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3094492109002409647653971 4641738163503614471480957)
    ·
      refine ⟨1740651811313855426805359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4641738163503614471480957 1740651811313855426805359)
      ·
        refine ⟨2610977716970783140208039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740651811313855426805359 2610977716970783140208039)
        ·
          refine ⟨3916466575456174710312059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610977716970783140208039 3916466575456174710312059)
          ·
            refine ⟨5874699863184262065468089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916466575456174710312059 5874699863184262065468089)
            ·
              refine ⟨4406024897388196549101067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5874699863184262065468089 4406024897388196549101067)
              ·
                refine ⟨6609037346082294823651601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406024897388196549101067 6609037346082294823651601)
                ·
                  refine ⟨4956778009561721117738701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609037346082294823651601 4956778009561721117738701)
                  ·
                    refine ⟨1858791753585645419152013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4956778009561721117738701 1858791753585645419152013)
                    ·
                      refine ⟨697046907594617032182005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858791753585645419152013 697046907594617032182005)
                      ·
                        rfl

theorem cell23_1357494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1357494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357494 prefixEnd_1357494 := by exact prefixLift 1357494
  have htrace : WordTrace (prefixWord ++ tailWord_1357494) baseStart_1357494 baseEnd_1357494 := by
    simpa [prefixWord, tailWord_1357494, baseEnd_1357494] using wordTrace_append hprefix tailTrace_1357494
  have hstable : (prefixWord ++ tailWord_1357494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357494).length < 2 ^ (prefixWord ++ tailWord_1357494).sum := by decide
  have hdescent : baseEnd_1357494 < baseStart_1357494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357500 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1357500 : Nat := 118140960795 + 1357500 * 2 ^ 59
def prefixEnd_1357500 : Nat := 4983230072969 + 3 ^ 40 * 1357500 * 2
def baseEnd_1357500 : Nat := 697049988478544008706977

theorem tailTrace_1357500 : CollatzResearch.WordTrace tailWord_1357500 prefixEnd_1357500 697049988478544008706977 := by
  unfold tailWord_1357500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756046291008408693590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33008061721344544924787969 24756046291008408693590977)
  ·
    refine ⟨18567034718256306520193233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24756046291008408693590977 18567034718256306520193233)
    ·
      refine ⟨13925276038692229890144925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18567034718256306520193233 13925276038692229890144925)
      ·
        refine ⟨5221978514509586208804347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13925276038692229890144925 5221978514509586208804347)
        ·
          refine ⟨7832967771764379313206521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221978514509586208804347 7832967771764379313206521)
          ·
            refine ⟨5874725828823284484904891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832967771764379313206521 5874725828823284484904891)
            ·
              refine ⟨8812088743234926727357337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874725828823284484904891 8812088743234926727357337)
              ·
                refine ⟨6609066557426195045518003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8812088743234926727357337 6609066557426195045518003)
                ·
                  refine ⟨9913599836139292568277005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609066557426195045518003 9913599836139292568277005)
                  ·
                    refine ⟨3717599938552234713103877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913599836139292568277005 3717599938552234713103877)
                    ·
                      refine ⟨697049988478544008706977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3717599938552234713103877 697049988478544008706977)
                      ·
                        rfl

theorem cell23_1357500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1357500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357500 prefixEnd_1357500 := by exact prefixLift 1357500
  have htrace : WordTrace (prefixWord ++ tailWord_1357500) baseStart_1357500 baseEnd_1357500 := by
    simpa [prefixWord, tailWord_1357500, baseEnd_1357500] using wordTrace_append hprefix tailTrace_1357500
  have hstable : (prefixWord ++ tailWord_1357500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357500).length < 2 ^ (prefixWord ++ tailWord_1357500).sum := by decide
  have hdescent : baseEnd_1357500 < baseStart_1357500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357540 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1357540 : Nat := 118140960795 + 1357540 * 2 ^ 59
def prefixEnd_1357540 : Nat := 4983230072969 + 3 ^ 40 * 1357540 * 2
def baseEnd_1357540 : Nat := 77452280856080428022977

theorem tailTrace_1357540 : CollatzResearch.WordTrace tailWord_1357540 prefixEnd_1357540 77452280856080428022977 := by
  unfold tailWord_1357540
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756775750935952109319037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33009034334581269479092049 24756775750935952109319037)
  ·
    refine ⟨9283790906600982040994639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24756775750935952109319037 9283790906600982040994639)
    ·
      refine ⟨13925686359901473061491959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9283790906600982040994639 13925686359901473061491959)
      ·
        refine ⟨20888529539852209592237939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925686359901473061491959 20888529539852209592237939)
        ·
          refine ⟨31332794309778314388356909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888529539852209592237939 31332794309778314388356909)
          ·
            refine ⟨11749797866166867895633841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31332794309778314388356909 11749797866166867895633841)
            ·
              refine ⟨8812348399625150921725381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11749797866166867895633841 8812348399625150921725381)
              ·
                refine ⟨1652315324929715797823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8812348399625150921725381 1652315324929715797823509)
                ·
                  refine ⟨77452280856080428022977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1652315324929715797823509 77452280856080428022977)
                  ·
                    rfl

theorem cell23_1357540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1357540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357540 prefixEnd_1357540 := by exact prefixLift 1357540
  have htrace : WordTrace (prefixWord ++ tailWord_1357540) baseStart_1357540 baseEnd_1357540 := by
    simpa [prefixWord, tailWord_1357540, baseEnd_1357540] using wordTrace_append hprefix tailTrace_1357540
  have hstable : (prefixWord ++ tailWord_1357540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357540).length < 2 ^ (prefixWord ++ tailWord_1357540).sum := by decide
  have hdescent : baseEnd_1357540 < baseStart_1357540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357544 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1357544 : Nat := 118140960795 + 1357544 * 2 ^ 59
def prefixEnd_1357544 : Nat := 4983230072969 + 3 ^ 40 * 1357544 * 2
def baseEnd_1357544 : Nat := 232357527209113945518925

theorem tailTrace_1357544 : CollatzResearch.WordTrace tailWord_1357544 prefixEnd_1357544 232357527209113945518925 := by
  unfold tailWord_1357544
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756848696928706450891843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33009131595904941934522457 24756848696928706450891843)
  ·
    refine ⟨37135273045393059676337765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24756848696928706450891843 37135273045393059676337765)
    ·
      refine ⟨6962863696011198689313331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37135273045393059676337765 6962863696011198689313331)
      ·
        refine ⟨10444295544016798033969997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962863696011198689313331 10444295544016798033969997)
        ·
          refine ⟨3916610829006299262738749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10444295544016798033969997 3916610829006299262738749)
          ·
            refine ⟨1468729060877362223527031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3916610829006299262738749 1468729060877362223527031)
            ·
              refine ⟨2203093591316043335290547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468729060877362223527031 2203093591316043335290547)
              ·
                refine ⟨3304640386974065002935821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203093591316043335290547 3304640386974065002935821)
                ·
                  refine ⟨1239240145115274376100933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3304640386974065002935821 1239240145115274376100933)
                  ·
                    refine ⟨232357527209113945518925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239240145115274376100933 232357527209113945518925)
                    ·
                      rfl

theorem cell23_1357544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1357544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357544 prefixEnd_1357544 := by exact prefixLift 1357544
  have htrace : WordTrace (prefixWord ++ tailWord_1357544) baseStart_1357544 baseEnd_1357544 := by
    simpa [prefixWord, tailWord_1357544, baseEnd_1357544] using wordTrace_append hprefix tailTrace_1357544
  have hstable : (prefixWord ++ tailWord_1357544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357544).length < 2 ^ (prefixWord ++ tailWord_1357544).sum := by decide
  have hdescent : baseEnd_1357544 < baseStart_1357544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357563 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_1357563 : Nat := 118140960795 + 1357563 * 2 ^ 59
def prefixEnd_1357563 : Nat := 4983230072969 + 3 ^ 40 * 1357563 * 2
def baseEnd_1357563 : Nat := 697082337759777262219187

theorem tailTrace_1357563 : CollatzResearch.WordTrace tailWord_1357563 prefixEnd_1357563 697082337759777262219187 := by
  unfold tailWord_1357563
  simp only [CollatzResearch.WordTrace]
  refine ⟨49514390380788579146725343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33009593587192386097816895 49514390380788579146725343)
  ·
    refine ⟨74271585571182868720088015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49514390380788579146725343 74271585571182868720088015)
    ·
      refine ⟨111407378356774303080132023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74271585571182868720088015 111407378356774303080132023)
      ·
        refine ⟨167111067535161454620198035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111407378356774303080132023 167111067535161454620198035)
        ·
          refine ⟨250666601302742181930297053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167111067535161454620198035 250666601302742181930297053)
          ·
            refine ⟨93999975488528318223861395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250666601302742181930297053 93999975488528318223861395)
            ·
              refine ⟨140999963232792477335792093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93999975488528318223861395 140999963232792477335792093)
              ·
                refine ⟨52874986212297179000922035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140999963232792477335792093 52874986212297179000922035)
                ·
                  refine ⟨79312479318445768501383053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52874986212297179000922035 79312479318445768501383053)
                  ·
                    refine ⟨29742179744417163188018645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79312479318445768501383053 29742179744417163188018645)
                    ·
                      refine ⟨697082337759777262219187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29742179744417163188018645 697082337759777262219187)
                      ·
                        rfl

theorem cell23_1357563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_1357563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357563 prefixEnd_1357563 := by exact prefixLift 1357563
  have htrace : WordTrace (prefixWord ++ tailWord_1357563) baseStart_1357563 baseEnd_1357563 := by
    simpa [prefixWord, tailWord_1357563, baseEnd_1357563] using wordTrace_append hprefix tailTrace_1357563
  have hstable : (prefixWord ++ tailWord_1357563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357563).length < 2 ^ (prefixWord ++ tailWord_1357563).sum := by decide
  have hdescent : baseEnd_1357563 < baseStart_1357563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357567 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_1357567 : Nat := 118140960795 + 1357567 * 2 ^ 59
def prefixEnd_1357567 : Nat := 4983230072969 + 3 ^ 40 * 1357567 * 2
def baseEnd_1357567 : Nat := 697084391682395246569169

theorem tailTrace_1357567 : CollatzResearch.WordTrace tailWord_1357567 prefixEnd_1357567 697084391682395246569169 := by
  unfold tailWord_1357567
  simp only [CollatzResearch.WordTrace]
  refine ⟨49514536272774087829870955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33009690848516058553247303 49514536272774087829870955)
  ·
    refine ⟨74271804409161131744806433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49514536272774087829870955 74271804409161131744806433)
    ·
      refine ⟨55703853306870848808604825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74271804409161131744806433 55703853306870848808604825)
      ·
        refine ⟨41777889980153136606453619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55703853306870848808604825 41777889980153136606453619)
        ·
          refine ⟨62666834970229704909680429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41777889980153136606453619 62666834970229704909680429)
          ·
            refine ⟨23500063113836139341130161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62666834970229704909680429 23500063113836139341130161)
            ·
              refine ⟨17625047335377104505847621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23500063113836139341130161 17625047335377104505847621)
              ·
                refine ⟨3304696375383207094846429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17625047335377104505847621 3304696375383207094846429)
                ·
                  refine ⟨1239261140768702660567411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3304696375383207094846429 1239261140768702660567411)
                  ·
                    refine ⟨1858891711153053990851117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239261140768702660567411 1858891711153053990851117)
                    ·
                      refine ⟨697084391682395246569169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858891711153053990851117 697084391682395246569169)
                      ·
                        rfl

theorem cell23_1357567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_1357567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357567 prefixEnd_1357567 := by exact prefixLift 1357567
  have htrace : WordTrace (prefixWord ++ tailWord_1357567) baseStart_1357567 baseEnd_1357567 := by
    simpa [prefixWord, tailWord_1357567, baseEnd_1357567] using wordTrace_append hprefix tailTrace_1357567
  have hstable : (prefixWord ++ tailWord_1357567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357567).length < 2 ^ (prefixWord ++ tailWord_1357567).sum := by decide
  have hdescent : baseEnd_1357567 < baseStart_1357567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357594 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_1357594 : Nat := 118140960795 + 1357594 * 2 ^ 59
def prefixEnd_1357594 : Nat := 4983230072969 + 3 ^ 40 * 1357594 * 2
def baseEnd_1357594 : Nat := 697098255660066640931545

theorem tailTrace_1357594 : CollatzResearch.WordTrace tailWord_1357594 prefixEnd_1357594 697098255660066640931545 := by
  unfold tailWord_1357594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378880260919067860275959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33010347362450847627402557 12378880260919067860275959)
  ·
    refine ⟨18568320391378601790413939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12378880260919067860275959 18568320391378601790413939)
    ·
      refine ⟨27852480587067902685620909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18568320391378601790413939 27852480587067902685620909)
      ·
        refine ⟨10444680220150463507107841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27852480587067902685620909 10444680220150463507107841)
        ·
          refine ⟨7833510165112847630330881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10444680220150463507107841 7833510165112847630330881)
          ·
            refine ⟨5875132623834635722748161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833510165112847630330881 5875132623834635722748161)
            ·
              refine ⟨4406349467875976792061121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875132623834635722748161 4406349467875976792061121)
              ·
                refine ⟨3304762100906982594045841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406349467875976792061121 3304762100906982594045841)
                ·
                  refine ⟨2478571575680236945534381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3304762100906982594045841 2478571575680236945534381)
                  ·
                    refine ⟨929464340880088854575393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478571575680236945534381 929464340880088854575393)
                    ·
                      refine ⟨697098255660066640931545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929464340880088854575393 697098255660066640931545)
                      ·
                        rfl

theorem cell23_1357594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_1357594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357594 prefixEnd_1357594 := by exact prefixLift 1357594
  have htrace : WordTrace (prefixWord ++ tailWord_1357594) baseStart_1357594 baseEnd_1357594 := by
    simpa [prefixWord, tailWord_1357594, baseEnd_1357594] using wordTrace_append hprefix tailTrace_1357594
  have hstable : (prefixWord ++ tailWord_1357594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357594).length < 2 ^ (prefixWord ++ tailWord_1357594).sum := by decide
  have hdescent : baseEnd_1357594 < baseStart_1357594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357600 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_1357600 : Nat := 118140960795 + 1357600 * 2 ^ 59
def prefixEnd_1357600 : Nat := 4983230072969 + 3 ^ 40 * 1357600 * 2
def baseEnd_1357600 : Nat := 232367112181331205818839

theorem tailTrace_1357600 : CollatzResearch.WordTrace tailWord_1357600 prefixEnd_1357600 232367112181331205818839 := by
  unfold tailWord_1357600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757869940827267232911127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33010493254436356310548169 24757869940827267232911127)
  ·
    refine ⟨37136804911240900849366691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24757869940827267232911127 37136804911240900849366691)
    ·
      refine ⟨55705207366861351274050037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37136804911240900849366691 55705207366861351274050037)
      ·
        refine ⟨5222363190643251681942191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55705207366861351274050037 5222363190643251681942191)
        ·
          refine ⟨7833544785964877522913287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222363190643251681942191 7833544785964877522913287)
          ·
            refine ⟨11750317178947316284369931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833544785964877522913287 11750317178947316284369931)
            ·
              refine ⟨17625475768420974426554897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750317178947316284369931 17625475768420974426554897)
              ·
                refine ⟨13219106826315730819916173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17625475768420974426554897 13219106826315730819916173)
                ·
                  refine ⟨4957165059868399057468565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13219106826315730819916173 4957165059868399057468565)
                  ·
                    refine ⟨232367112181331205818839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4957165059868399057468565 232367112181331205818839)
                    ·
                      rfl

theorem cell23_1357600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_1357600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357600 prefixEnd_1357600 := by exact prefixLift 1357600
  have htrace : WordTrace (prefixWord ++ tailWord_1357600) baseStart_1357600 baseEnd_1357600 := by
    simpa [prefixWord, tailWord_1357600, baseEnd_1357600] using wordTrace_append hprefix tailTrace_1357600
  have hstable : (prefixWord ++ tailWord_1357600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357600).length < 2 ^ (prefixWord ++ tailWord_1357600).sum := by decide
  have hdescent : baseEnd_1357600 < baseStart_1357600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357601 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1357601 : Nat := 118140960795 + 1357601 * 2 ^ 59
def prefixEnd_1357601 : Nat := 4983230072969 + 3 ^ 40 * 1357601 * 2
def baseEnd_1357601 : Nat := 697101850024648113544013

theorem tailTrace_1357601 : CollatzResearch.WordTrace tailWord_1357601 prefixEnd_1357601 697101850024648113544013 := by
  unfold tailWord_1357601
  simp only [CollatzResearch.WordTrace]
  refine ⟨49515776354650911636608657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33010517569767274424405771 49515776354650911636608657)
  ·
    refine ⟨37136832265988183727456493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49515776354650911636608657 37136832265988183727456493)
    ·
      refine ⟨13926312099745568897796185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37136832265988183727456493 13926312099745568897796185)
      ·
        refine ⟨10444734074809176673347139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13926312099745568897796185 10444734074809176673347139)
        ·
          refine ⟨15667101112213765010020709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10444734074809176673347139 15667101112213765010020709)
          ·
            refine ⟨2937581458540080939378883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15667101112213765010020709 2937581458540080939378883)
            ·
              refine ⟨4406372187810121409068325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937581458540080939378883 4406372187810121409068325)
              ·
                refine ⟨826194785214397764200311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4406372187810121409068325 826194785214397764200311)
                ·
                  refine ⟨1239292177821596646300467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826194785214397764200311 1239292177821596646300467)
                  ·
                    refine ⟨1858938266732394969450701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239292177821596646300467 1858938266732394969450701)
                    ·
                      refine ⟨697101850024648113544013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1858938266732394969450701 697101850024648113544013)
                      ·
                        rfl

theorem cell23_1357601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1357601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357601 prefixEnd_1357601 := by exact prefixLift 1357601
  have htrace : WordTrace (prefixWord ++ tailWord_1357601) baseStart_1357601 baseEnd_1357601 := by
    simpa [prefixWord, tailWord_1357601, baseEnd_1357601] using wordTrace_append hprefix tailTrace_1357601
  have hstable : (prefixWord ++ tailWord_1357601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357601).length < 2 ^ (prefixWord ++ tailWord_1357601).sum := by decide
  have hdescent : baseEnd_1357601 < baseStart_1357601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357617 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1357617 : Nat := 118140960795 + 1357617 * 2 ^ 59
def prefixEnd_1357617 : Nat := 4983230072969 + 3 ^ 40 * 1357617 * 2
def baseEnd_1357617 : Nat := 232370021905040016981313

theorem tailTrace_1357617 : CollatzResearch.WordTrace tailWord_1357617 prefixEnd_1357617 232370021905040016981313 := by
  unfold tailWord_1357617
  simp only [CollatzResearch.WordTrace]
  refine ⟨49516359922592946369191105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33010906615061964246127403 49516359922592946369191105)
  ·
    refine ⟨37137269941944709776893329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49516359922592946369191105 37137269941944709776893329)
    ·
      refine ⟨27852952456458532332669997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37137269941944709776893329 27852952456458532332669997)
      ·
        refine ⟨10444857171171949624751249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27852952456458532332669997 10444857171171949624751249)
        ·
          refine ⟨7833642878378962218563437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10444857171171949624751249 7833642878378962218563437)
          ·
            refine ⟨2937616079392110831961289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7833642878378962218563437 2937616079392110831961289)
            ·
              refine ⟨2203212059544083123970967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937616079392110831961289 2203212059544083123970967)
              ·
                refine ⟨3304818089316124685956451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203212059544083123970967 3304818089316124685956451)
                ·
                  refine ⟨4957227133974187028934677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304818089316124685956451 4957227133974187028934677)
                  ·
                    refine ⟨232370021905040016981313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4957227133974187028934677 232370021905040016981313)
                    ·
                      rfl

theorem cell23_1357617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1357617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357617 prefixEnd_1357617 := by exact prefixLift 1357617
  have htrace : WordTrace (prefixWord ++ tailWord_1357617) baseStart_1357617 baseEnd_1357617 := by
    simpa [prefixWord, tailWord_1357617, baseEnd_1357617] using wordTrace_append hprefix tailTrace_1357617
  have hstable : (prefixWord ++ tailWord_1357617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357617).length < 2 ^ (prefixWord ++ tailWord_1357617).sum := by decide
  have hdescent : baseEnd_1357617 < baseStart_1357617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357624 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_1357624 : Nat := 118140960795 + 1357624 * 2 ^ 59
def prefixEnd_1357624 : Nat := 4983230072969 + 3 ^ 40 * 1357624 * 2
def baseEnd_1357624 : Nat := 697113660079701523556407

theorem tailTrace_1357624 : CollatzResearch.WordTrace tailWord_1357624 prefixEnd_1357624 697113660079701523556407 := by
  unfold tailWord_1357624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758307616783793282347963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33011076822378391043130617 24758307616783793282347963)
  ·
    refine ⟨37137461425175689923521945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24758307616783793282347963 37137461425175689923521945)
    ·
      refine ⟨27853096068881767442641459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37137461425175689923521945 27853096068881767442641459)
      ·
        refine ⟨41779644103322651163962189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27853096068881767442641459 41779644103322651163962189)
        ·
          refine ⟨15667366538745994186485821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41779644103322651163962189 15667366538745994186485821)
          ·
            refine ⟨5875262452029747819932183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15667366538745994186485821 5875262452029747819932183)
            ·
              refine ⟨8812893678044621729898275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875262452029747819932183 8812893678044621729898275)
              ·
                refine ⟨13219340517066932594847413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812893678044621729898275 13219340517066932594847413)
                ·
                  refine ⟨1239313173475024930766945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13219340517066932594847413 1239313173475024930766945)
                  ·
                    refine ⟨929484880106268698075209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1239313173475024930766945 929484880106268698075209)
                    ·
                      refine ⟨697113660079701523556407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929484880106268698075209 697113660079701523556407)
                      ·
                        rfl

theorem cell23_1357624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_1357624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357624 prefixEnd_1357624 := by exact prefixLift 1357624
  have htrace : WordTrace (prefixWord ++ tailWord_1357624) baseStart_1357624 baseEnd_1357624 := by
    simpa [prefixWord, tailWord_1357624, baseEnd_1357624] using wordTrace_append hprefix tailTrace_1357624
  have hstable : (prefixWord ++ tailWord_1357624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357624).length < 2 ^ (prefixWord ++ tailWord_1357624).sum := by decide
  have hdescent : baseEnd_1357624 < baseStart_1357624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357638 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1357638 : Nat := 118140960795 + 1357638 * 2 ^ 59
def prefixEnd_1357638 : Nat := 4983230072969 + 3 ^ 40 * 1357638 * 2
def baseEnd_1357638 : Nat := 232373616269621489593781

theorem tailTrace_1357638 : CollatzResearch.WordTrace tailWord_1357638 prefixEnd_1357638 232373616269621489593781 := by
  unfold tailWord_1357638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547410182984902092365799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33011417237011244637137045 1547410182984902092365799)
  ·
    refine ⟨2321115274477353138548699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1547410182984902092365799 2321115274477353138548699)
    ·
      refine ⟨3481672911716029707823049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321115274477353138548699 3481672911716029707823049)
      ·
        refine ⟨2611254683787022280867287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3481672911716029707823049 2611254683787022280867287)
        ·
          refine ⟨3916882025680533421300931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611254683787022280867287 3916882025680533421300931)
          ·
            refine ⟨5875323038520800131951397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916882025680533421300931 5875323038520800131951397)
            ·
              refine ⟨1101623069722650024740887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5875323038520800131951397 1101623069722650024740887)
              ·
                refine ⟨1652434604583975037111331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101623069722650024740887 1652434604583975037111331)
                ·
                  refine ⟨2478651906875962555666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652434604583975037111331 2478651906875962555666997)
                  ·
                    refine ⟨232373616269621489593781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2478651906875962555666997 232373616269621489593781)
                    ·
                      rfl

theorem cell23_1357638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1357638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357638 prefixEnd_1357638 := by exact prefixLift 1357638
  have htrace : WordTrace (prefixWord ++ tailWord_1357638) baseStart_1357638 baseEnd_1357638 := by
    simpa [prefixWord, tailWord_1357638, baseEnd_1357638] using wordTrace_append hprefix tailTrace_1357638
  have hstable : (prefixWord ++ tailWord_1357638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357638).length < 2 ^ (prefixWord ++ tailWord_1357638).sum := by decide
  have hdescent : baseEnd_1357638 < baseStart_1357638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357690 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_1357690 : Nat := 118140960795 + 1357690 * 2 ^ 59
def prefixEnd_1357690 : Nat := 4983230072969 + 3 ^ 40 * 1357690 * 2
def baseEnd_1357690 : Nat := 232382516600966088443701

theorem tailTrace_1357690 : CollatzResearch.WordTrace tailWord_1357690 prefixEnd_1357690 232382516600966088443701 := by
  unfold tailWord_1357690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379755612832119959149631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33012681634218986557732349 12379755612832119959149631)
  ·
    refine ⟨18569633419248179938724447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12379755612832119959149631 18569633419248179938724447)
    ·
      refine ⟨27854450128872269908086671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569633419248179938724447 27854450128872269908086671)
      ·
        refine ⟨41781675193308404862130007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27854450128872269908086671 41781675193308404862130007)
        ·
          refine ⟨62672512789962607293195011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41781675193308404862130007 62672512789962607293195011)
          ·
            refine ⟨94008769184943910939792517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62672512789962607293195011 94008769184943910939792517)
            ·
              refine ⟨17626644222176983301211097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94008769184943910939792517 17626644222176983301211097)
              ·
                refine ⟨13219983166632737475908323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17626644222176983301211097 13219983166632737475908323)
                ·
                  refine ⟨19829974749949106213862485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13219983166632737475908323 19829974749949106213862485)
                  ·
                    refine ⟨232382516600966088443701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19829974749949106213862485 232382516600966088443701)
                    ·
                      rfl

theorem cell23_1357690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_1357690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357690 prefixEnd_1357690 := by exact prefixLift 1357690
  have htrace : WordTrace (prefixWord ++ tailWord_1357690) baseStart_1357690 baseEnd_1357690 := by
    simpa [prefixWord, tailWord_1357690, baseEnd_1357690] using wordTrace_append hprefix tailTrace_1357690
  have hstable : (prefixWord ++ tailWord_1357690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357690).length < 2 ^ (prefixWord ++ tailWord_1357690).sum := by decide
  have hdescent : baseEnd_1357690 < baseStart_1357690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357717 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1357717 : Nat := 118140960795 + 1357717 * 2 ^ 59
def prefixEnd_1357717 : Nat := 4983230072969 + 3 ^ 40 * 1357717 * 2
def baseEnd_1357717 : Nat := 697161413780569659693479

theorem tailTrace_1357717 : CollatzResearch.WordTrace tailWord_1357717 prefixEnd_1357717 697161413780569659693479 := by
  unfold tailWord_1357717
  simp only [CollatzResearch.WordTrace]
  refine ⟨49520007222230663447831405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33013338148153775631887603 49520007222230663447831405)
  ·
    refine ⟨18570002708336498792936777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49520007222230663447831405 18570002708336498792936777)
    ·
      refine ⟨13927502031252374094702583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18570002708336498792936777 13927502031252374094702583)
      ·
        refine ⟨20891253046878561142053875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13927502031252374094702583 20891253046878561142053875)
        ·
          refine ⟨31336879570317841713080813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20891253046878561142053875 31336879570317841713080813)
          ·
            refine ⟨11751329838869190642405305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31336879570317841713080813 11751329838869190642405305)
            ·
              refine ⟨8813497379151892981803979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11751329838869190642405305 8813497379151892981803979)
              ·
                refine ⟨13220246068727839472705969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8813497379151892981803979 13220246068727839472705969)
                ·
                  refine ⟨9915184551545879604529477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13220246068727839472705969 9915184551545879604529477)
                  ·
                    refine ⟨1859097103414852425849277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9915184551545879604529477 1859097103414852425849277)
                    ·
                      refine ⟨697161413780569659693479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859097103414852425849277 697161413780569659693479)
                      ·
                        rfl

theorem cell23_1357717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1357717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357717 prefixEnd_1357717 := by exact prefixLift 1357717
  have htrace : WordTrace (prefixWord ++ tailWord_1357717) baseStart_1357717 baseEnd_1357717 := by
    simpa [prefixWord, tailWord_1357717, baseEnd_1357717] using wordTrace_append hprefix tailTrace_1357717
  have hstable : (prefixWord ++ tailWord_1357717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357717).length < 2 ^ (prefixWord ++ tailWord_1357717).sum := by decide
  have hdescent : baseEnd_1357717 < baseStart_1357717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357774 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_1357774 : Nat := 118140960795 + 1357774 * 2 ^ 59
def prefixEnd_1357774 : Nat := 4983230072969 + 3 ^ 40 * 1357774 * 2
def baseEnd_1357774 : Nat := 697190682177875936680717

theorem tailTrace_1357774 : CollatzResearch.WordTrace tailWord_1357774 prefixEnd_1357774 697190682177875936680717 := by
  unfold tailWord_1357774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6190260772878020272832047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33014724122016108121770917 6190260772878020272832047)
  ·
    refine ⟨9285391159317030409248071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6190260772878020272832047 9285391159317030409248071)
    ·
      refine ⟨13928086738975545613872107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285391159317030409248071 13928086738975545613872107)
      ·
        refine ⟨20892130108463318420808161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13928086738975545613872107 20892130108463318420808161)
        ·
          refine ⟨15669097581347488815606121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20892130108463318420808161 15669097581347488815606121)
          ·
            refine ⟨11751823186010616611704591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15669097581347488815606121 11751823186010616611704591)
            ·
              refine ⟨17627734779015924917556887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11751823186010616611704591 17627734779015924917556887)
              ·
                refine ⟨26441602168523887376335331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17627734779015924917556887 26441602168523887376335331)
                ·
                  refine ⟨39662403252785831064502997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26441602168523887376335331 39662403252785831064502997)
                  ·
                    refine ⟨929587576237167915574289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39662403252785831064502997 929587576237167915574289)
                    ·
                      refine ⟨697190682177875936680717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929587576237167915574289 697190682177875936680717)
                      ·
                        rfl

theorem cell23_1357774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_1357774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357774 prefixEnd_1357774 := by exact prefixLift 1357774
  have htrace : WordTrace (prefixWord ++ tailWord_1357774) baseStart_1357774 baseEnd_1357774 := by
    simpa [prefixWord, tailWord_1357774, baseEnd_1357774] using wordTrace_append hprefix tailTrace_1357774
  have hstable : (prefixWord ++ tailWord_1357774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357774).length < 2 ^ (prefixWord ++ tailWord_1357774).sum := by decide
  have hdescent : baseEnd_1357774 < baseStart_1357774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357788 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 7]
def baseStart_1357788 : Nat := 118140960795 + 1357788 * 2 ^ 59
def prefixEnd_1357788 : Nat := 4983230072969 + 3 ^ 40 * 1357788 * 2
def baseEnd_1357788 : Nat := 77466430100782097989517

theorem tailTrace_1357788 : CollatzResearch.WordTrace tailWord_1357788 prefixEnd_1357788 77466430100782097989517 := by
  unfold tailWord_1357788
  simp only [CollatzResearch.WordTrace]
  refine ⟨24761298402486721286833009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33015064536648961715777345 24761298402486721286833009)
  ·
    refine ⟨18570973801865040965124757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24761298402486721286833009 18570973801865040965124757)
    ·
      refine ⟨870514396962423795240223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18570973801865040965124757 870514396962423795240223)
      ·
        refine ⟨1305771595443635692860335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870514396962423795240223 1305771595443635692860335)
        ·
          refine ⟨1958657393165453539290503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305771595443635692860335 1958657393165453539290503)
          ·
            refine ⟨2937986089748180308935755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958657393165453539290503 2937986089748180308935755)
            ·
              refine ⟨4406979134622270463403633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937986089748180308935755 4406979134622270463403633)
              ·
                refine ⟨3305234350966702847552725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406979134622270463403633 3305234350966702847552725)
                ·
                  refine ⟨77466430100782097989517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3305234350966702847552725 77466430100782097989517)
                  ·
                    rfl

theorem cell23_1357788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_1357788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357788 prefixEnd_1357788 := by exact prefixLift 1357788
  have htrace : WordTrace (prefixWord ++ tailWord_1357788) baseStart_1357788 baseEnd_1357788 := by
    simpa [prefixWord, tailWord_1357788, baseEnd_1357788] using wordTrace_append hprefix tailTrace_1357788
  have hstable : (prefixWord ++ tailWord_1357788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357788).length < 2 ^ (prefixWord ++ tailWord_1357788).sum := by decide
  have hdescent : baseEnd_1357788 < baseStart_1357788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357817 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1357817 : Nat := 118140960795 + 1357817 * 2 ^ 59
def prefixEnd_1357817 : Nat := 4983230072969 + 3 ^ 40 * 1357817 * 2
def baseEnd_1357817 : Nat := 697212761846019268443019

theorem tailTrace_1357817 : CollatzResearch.WordTrace tailWord_1357817 prefixEnd_1357817 697212761846019268443019 := by
  unfold tailWord_1357817
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523654521868380526471705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33015769681245587017647803 49523654521868380526471705)
  ·
    refine ⟨37142740891401285394853779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49523654521868380526471705 37142740891401285394853779)
    ·
      refine ⟨55714111337101928092280669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37142740891401285394853779 55714111337101928092280669)
      ·
        refine ⟨20892791751413223034605251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55714111337101928092280669 20892791751413223034605251)
        ·
          refine ⟨31339187627119834551907877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20892791751413223034605251 31339187627119834551907877)
          ·
            refine ⟨5876097680084968978482727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31339187627119834551907877 5876097680084968978482727)
            ·
              refine ⟨8814146520127453467724091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876097680084968978482727 8814146520127453467724091)
              ·
                refine ⟨13221219780191180201586137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8814146520127453467724091 13221219780191180201586137)
                ·
                  refine ⟨9915914835143385151189603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13221219780191180201586137 9915914835143385151189603)
                  ·
                    refine ⟨14873872252715077726784405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9915914835143385151189603 14873872252715077726784405)
                    ·
                      refine ⟨697212761846019268443019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14873872252715077726784405 697212761846019268443019)
                      ·
                        rfl

theorem cell23_1357817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1357817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357817 prefixEnd_1357817 := by exact prefixLift 1357817
  have htrace : WordTrace (prefixWord ++ tailWord_1357817) baseStart_1357817 baseEnd_1357817 := by
    simpa [prefixWord, tailWord_1357817, baseEnd_1357817] using wordTrace_append hprefix tailTrace_1357817
  have hstable : (prefixWord ++ tailWord_1357817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357817).length < 2 ^ (prefixWord ++ tailWord_1357817).sum := by decide
  have hdescent : baseEnd_1357817 < baseStart_1357817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357831 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 3, 4]
def baseStart_1357831 : Nat := 118140960795 + 1357831 * 2 ^ 59
def prefixEnd_1357831 : Nat := 4983230072969 + 3 ^ 40 * 1357831 * 2
def baseEnd_1357831 : Nat := 232406650191727404555985

theorem tailTrace_1357831 : CollatzResearch.WordTrace tailWord_1357831 prefixEnd_1357831 232406650191727404555985 := by
  unfold tailWord_1357831
  simp only [CollatzResearch.WordTrace]
  refine ⟨49524165143817660917481347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33016110095878440611654231 49524165143817660917481347)
  ·
    refine ⟨74286247715726491376222021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49524165143817660917481347 74286247715726491376222021)
    ·
      refine ⟨13928671446698717133041629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74286247715726491376222021 13928671446698717133041629)
      ·
        refine ⟨5223251792512018924890611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13928671446698717133041629 5223251792512018924890611)
        ·
          refine ⟨7834877688768028387335917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223251792512018924890611 7834877688768028387335917)
          ·
            refine ⟨2938079133288010645250969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7834877688768028387335917 2938079133288010645250969)
            ·
              refine ⟨2203559349966007983938227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938079133288010645250969 2203559349966007983938227)
              ·
                refine ⟨3305339024949011975907341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203559349966007983938227 3305339024949011975907341)
                ·
                  refine ⟨1239502134355879490965253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3305339024949011975907341 1239502134355879490965253)
                  ·
                    refine ⟨232406650191727404555985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239502134355879490965253 232406650191727404555985)
                    ·
                      rfl

theorem cell23_1357831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_1357831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357831 prefixEnd_1357831 := by exact prefixLift 1357831
  have htrace : WordTrace (prefixWord ++ tailWord_1357831) baseStart_1357831 baseEnd_1357831 := by
    simpa [prefixWord, tailWord_1357831, baseEnd_1357831] using wordTrace_append hprefix tailTrace_1357831
  have hstable : (prefixWord ++ tailWord_1357831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357831).length < 2 ^ (prefixWord ++ tailWord_1357831).sum := by decide
  have hdescent : baseEnd_1357831 < baseStart_1357831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357888 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_1357888 : Nat := 118140960795 + 1357888 * 2 ^ 59
def prefixEnd_1357888 : Nat := 4983230072969 + 3 ^ 40 * 1357888 * 2
def baseEnd_1357888 : Nat := 697249218972488490655193

theorem tailTrace_1357888 : CollatzResearch.WordTrace tailWord_1357888 prefixEnd_1357888 697249218972488490655193 := by
  unfold tailWord_1357888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763122052305579826153159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33017496069740773101537545 24763122052305579826153159)
  ·
    refine ⟨37144683078458369739229739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24763122052305579826153159 37144683078458369739229739)
    ·
      refine ⟨55717024617687554608844609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37144683078458369739229739 55717024617687554608844609)
      ·
        refine ⟨41787768463265665956633457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55717024617687554608844609 41787768463265665956633457)
        ·
          refine ⟨31340826347449249467475093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41787768463265665956633457 31340826347449249467475093)
          ·
            refine ⟨1469101235036683568787895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31340826347449249467475093 1469101235036683568787895)
            ·
              refine ⟨2203651852555025353181843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469101235036683568787895 2203651852555025353181843)
              ·
                refine ⟨3305477778832538029772765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203651852555025353181843 3305477778832538029772765)
                ·
                  refine ⟨1239554167062201761164787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3305477778832538029772765 1239554167062201761164787)
                  ·
                    refine ⟨1859331250593302641747181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239554167062201761164787 1859331250593302641747181)
                    ·
                      refine ⟨697249218972488490655193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859331250593302641747181 697249218972488490655193)
                      ·
                        rfl

theorem cell23_1357888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_1357888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357888 prefixEnd_1357888 := by exact prefixLift 1357888
  have htrace : WordTrace (prefixWord ++ tailWord_1357888) baseStart_1357888 baseEnd_1357888 := by
    simpa [prefixWord, tailWord_1357888, baseEnd_1357888] using wordTrace_append hprefix tailTrace_1357888
  have hstable : (prefixWord ++ tailWord_1357888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357888).length < 2 ^ (prefixWord ++ tailWord_1357888).sum := by decide
  have hdescent : baseEnd_1357888 < baseStart_1357888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_1357907 : Nat := 118140960795 + 1357907 * 2 ^ 59
def prefixEnd_1357907 : Nat := 4983230072969 + 3 ^ 40 * 1357907 * 2
def baseEnd_1357907 : Nat := 697258975104923916317605

theorem tailTrace_1357907 : CollatzResearch.WordTrace tailWord_1357907 prefixEnd_1357907 697258975104923916317605 := by
  unfold tailWord_1357907
  simp only [CollatzResearch.WordTrace]
  refine ⟨49526937091542325897247975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33017958061028217264831983 49526937091542325897247975)
  ·
    refine ⟨74290405637313488845871963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49526937091542325897247975 74290405637313488845871963)
    ·
      refine ⟨111435608455970233268807945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74290405637313488845871963 111435608455970233268807945)
      ·
        refine ⟨83576706341977674951605959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111435608455970233268807945 83576706341977674951605959)
        ·
          refine ⟨125365059512966512427408939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83576706341977674951605959 125365059512966512427408939)
          ·
            refine ⟨188047589269449768641113409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125365059512966512427408939 188047589269449768641113409)
            ·
              refine ⟨141035691952087326480835057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188047589269449768641113409 141035691952087326480835057)
              ·
                refine ⟨105776768964065494860626293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141035691952087326480835057 105776768964065494860626293)
                ·
                  refine ⟨9916572090381140143183715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105776768964065494860626293 9916572090381140143183715)
                  ·
                    refine ⟨14874858135571710214775573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9916572090381140143183715 14874858135571710214775573)
                    ·
                      refine ⟨697258975104923916317605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14874858135571710214775573 697258975104923916317605)
                      ·
                        rfl

theorem cell23_1357907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_1357907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357907 prefixEnd_1357907 := by exact prefixLift 1357907
  have htrace : WordTrace (prefixWord ++ tailWord_1357907) baseStart_1357907 baseEnd_1357907 := by
    simpa [prefixWord, tailWord_1357907, baseEnd_1357907] using wordTrace_append hprefix tailTrace_1357907
  have hstable : (prefixWord ++ tailWord_1357907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357907).length < 2 ^ (prefixWord ++ tailWord_1357907).sum := by decide
  have hdescent : baseEnd_1357907 < baseStart_1357907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357911 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1357911 : Nat := 118140960795 + 1357911 * 2 ^ 59
def prefixEnd_1357911 : Nat := 4983230072969 + 3 ^ 40 * 1357911 * 2
def baseEnd_1357911 : Nat := 697261029027541900667587

theorem tailTrace_1357911 : CollatzResearch.WordTrace tailWord_1357911 prefixEnd_1357911 697261029027541900667587 := by
  unfold tailWord_1357911
  simp only [CollatzResearch.WordTrace]
  refine ⟨49527082983527834580393587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33018055322351889720262391 49527082983527834580393587)
  ·
    refine ⟨74290624475291751870590381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49527082983527834580393587 74290624475291751870590381)
    ·
      refine ⟨27858984178234406951471393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74290624475291751870590381 27858984178234406951471393)
      ·
        refine ⟨20894238133675805213603545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27858984178234406951471393 20894238133675805213603545)
        ·
          refine ⟨15670678600256853910202659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20894238133675805213603545 15670678600256853910202659)
          ·
            refine ⟨23506017900385280865303989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15670678600256853910202659 23506017900385280865303989)
            ·
              refine ⟨2203689178161120081122249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23506017900385280865303989 2203689178161120081122249)
              ·
                refine ⟨1652766883620840060841687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203689178161120081122249 1652766883620840060841687)
                ·
                  refine ⟨2479150325431260091262531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652766883620840060841687 2479150325431260091262531)
                  ·
                    refine ⟨3718725488146890136893797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479150325431260091262531 3718725488146890136893797)
                    ·
                      refine ⟨697261029027541900667587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3718725488146890136893797 697261029027541900667587)
                      ·
                        rfl

theorem cell23_1357911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1357911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357911 prefixEnd_1357911 := by exact prefixLift 1357911
  have htrace : WordTrace (prefixWord ++ tailWord_1357911) baseStart_1357911 baseEnd_1357911 := by
    simpa [prefixWord, tailWord_1357911, baseEnd_1357911] using wordTrace_append hprefix tailTrace_1357911
  have hstable : (prefixWord ++ tailWord_1357911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357911).length < 2 ^ (prefixWord ++ tailWord_1357911).sum := by decide
  have hdescent : baseEnd_1357911 < baseStart_1357911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357924 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_1357924 : Nat := 118140960795 + 1357924 * 2 ^ 59
def prefixEnd_1357924 : Nat := 4983230072969 + 3 ^ 40 * 1357924 * 2
def baseEnd_1357924 : Nat := 697267704276050349805027

theorem tailTrace_1357924 : CollatzResearch.WordTrace tailWord_1357924 prefixEnd_1357924 697267704276050349805027 := by
  unfold tailWord_1357924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763778566240368900308413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33018371421653825200411217 24763778566240368900308413)
  ·
    refine ⟨9286416962340138337615655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24763778566240368900308413 9286416962340138337615655)
    ·
      refine ⟨13929625443510207506423483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286416962340138337615655 13929625443510207506423483)
      ·
        refine ⟨20894438165265311259635225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13929625443510207506423483 20894438165265311259635225)
        ·
          refine ⟨15670828623948983444726419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20894438165265311259635225 15670828623948983444726419)
          ·
            refine ⟨23506242935923475167089629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15670828623948983444726419 23506242935923475167089629)
            ·
              refine ⟨8814841100971303187658611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23506242935923475167089629 8814841100971303187658611)
              ·
                refine ⟨13222261651456954781487917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8814841100971303187658611 13222261651456954781487917)
                ·
                  refine ⟨4958348119296358043057969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13222261651456954781487917 4958348119296358043057969)
                  ·
                    refine ⟨3718761089472268532293477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958348119296358043057969 3718761089472268532293477)
                    ·
                      refine ⟨697267704276050349805027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3718761089472268532293477 697267704276050349805027)
                      ·
                        rfl

theorem cell23_1357924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_1357924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357924 prefixEnd_1357924 := by exact prefixLift 1357924
  have htrace : WordTrace (prefixWord ++ tailWord_1357924) baseStart_1357924 baseEnd_1357924 := by
    simpa [prefixWord, tailWord_1357924, baseEnd_1357924] using wordTrace_append hprefix tailTrace_1357924
  have hstable : (prefixWord ++ tailWord_1357924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357924).length < 2 ^ (prefixWord ++ tailWord_1357924).sum := by decide
  have hdescent : baseEnd_1357924 < baseStart_1357924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357938 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_1357938 : Nat := 118140960795 + 1357938 * 2 ^ 59
def prefixEnd_1357938 : Nat := 4983230072969 + 3 ^ 40 * 1357938 * 2
def baseEnd_1357938 : Nat := 232424964335071098343321

theorem tailTrace_1357938 : CollatzResearch.WordTrace tailWord_1357938 prefixEnd_1357938 232424964335071098343321 := by
  unfold tailWord_1357938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12382016938607504547906617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33018711836286678794417645 12382016938607504547906617)
  ·
    refine ⟨9286512703955628410929963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12382016938607504547906617 9286512703955628410929963)
    ·
      refine ⟨13929769055933442616394945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286512703955628410929963 13929769055933442616394945)
      ·
        refine ⟨10447326791950081962296209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13929769055933442616394945 10447326791950081962296209)
        ·
          refine ⟨7835495093962561471722157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447326791950081962296209 7835495093962561471722157)
          ·
            refine ⟨2938310660235960551895809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7835495093962561471722157 2938310660235960551895809)
            ·
              refine ⟨2203732995176970413921857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938310660235960551895809 2203732995176970413921857)
              ·
                refine ⟨1652799746382727810441393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203732995176970413921857 1652799746382727810441393)
                ·
                  refine ⟨1239599809787045857831045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652799746382727810441393 1239599809787045857831045)
                  ·
                    refine ⟨232424964335071098343321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239599809787045857831045 232424964335071098343321)
                    ·
                      rfl

theorem cell23_1357938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_1357938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357938 prefixEnd_1357938 := by exact prefixLift 1357938
  have htrace : WordTrace (prefixWord ++ tailWord_1357938) baseStart_1357938 baseEnd_1357938 := by
    simpa [prefixWord, tailWord_1357938, baseEnd_1357938] using wordTrace_append hprefix tailTrace_1357938
  have hstable : (prefixWord ++ tailWord_1357938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357938).length < 2 ^ (prefixWord ++ tailWord_1357938).sum := by decide
  have hdescent : baseEnd_1357938 < baseStart_1357938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357944 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_1357944 : Nat := 118140960795 + 1357944 * 2 ^ 59
def prefixEnd_1357944 : Nat := 4983230072969 + 3 ^ 40 * 1357944 * 2
def baseEnd_1357944 : Nat := 697277973889140271554935

theorem tailTrace_1357944 : CollatzResearch.WordTrace tailWord_1357944 prefixEnd_1357944 697277973889140271554935 := by
  unfold tailWord_1357944
  simp only [CollatzResearch.WordTrace]
  refine ⟨24764143296204140608172443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33018857728272187477563257 24764143296204140608172443)
  ·
    refine ⟨37146214944306210912258665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24764143296204140608172443 37146214944306210912258665)
    ·
      refine ⟨27859661208229658184193999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37146214944306210912258665 27859661208229658184193999)
      ·
        refine ⟨41789491812344487276290999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27859661208229658184193999 41789491812344487276290999)
        ·
          refine ⟨62684237718516730914436499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41789491812344487276290999 62684237718516730914436499)
          ·
            refine ⟨94026356577775096371654749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62684237718516730914436499 94026356577775096371654749)
            ·
              refine ⟨35259883716665661139370531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94026356577775096371654749 35259883716665661139370531)
              ·
                refine ⟨52889825574998491709055797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35259883716665661139370531 52889825574998491709055797)
                ·
                  refine ⟨4958421147656108597723981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52889825574998491709055797 4958421147656108597723981)
                  ·
                    refine ⟨1859407930371040724146493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958421147656108597723981 1859407930371040724146493)
                    ·
                      refine ⟨697277973889140271554935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859407930371040724146493 697277973889140271554935)
                      ·
                        rfl

theorem cell23_1357944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_1357944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357944 prefixEnd_1357944 := by exact prefixLift 1357944
  have htrace : WordTrace (prefixWord ++ tailWord_1357944) baseStart_1357944 baseEnd_1357944 := by
    simpa [prefixWord, tailWord_1357944, baseEnd_1357944] using wordTrace_append hprefix tailTrace_1357944
  have hstable : (prefixWord ++ tailWord_1357944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357944).length < 2 ^ (prefixWord ++ tailWord_1357944).sum := by decide
  have hdescent : baseEnd_1357944 < baseStart_1357944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357961 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_1357961 : Nat := 118140960795 + 1357961 * 2 ^ 59
def prefixEnd_1357961 : Nat := 4983230072969 + 3 ^ 40 * 1357961 * 2
def baseEnd_1357961 : Nat := 697286703060266705042357

theorem tailTrace_1357961 : CollatzResearch.WordTrace tailWord_1357961 prefixEnd_1357961 697286703060266705042357 := by
  unfold tailWord_1357961
  simp only [CollatzResearch.WordTrace]
  refine ⟨49528906633346693119713737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33019271088897795413142491 49528906633346693119713737)
  ·
    refine ⟨37146679975010019839785303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49528906633346693119713737 37146679975010019839785303)
    ·
      refine ⟨55720019962515029759677955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37146679975010019839785303 55720019962515029759677955)
      ·
        refine ⟨83580029943772544639516933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55720019962515029759677955 83580029943772544639516933)
        ·
          refine ⟨15671255614457352119909425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83580029943772544639516933 15671255614457352119909425)
          ·
            refine ⟨11753441710843014089932069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15671255614457352119909425 11753441710843014089932069)
            ·
              refine ⟨2203770320783065141862263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11753441710843014089932069 2203770320783065141862263)
              ·
                refine ⟨3305655481174597712793395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203770320783065141862263 3305655481174597712793395)
                ·
                  refine ⟨4958483221761896569190093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305655481174597712793395 4958483221761896569190093)
                  ·
                    refine ⟨1859431208160711213446285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958483221761896569190093 1859431208160711213446285)
                    ·
                      refine ⟨697286703060266705042357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859431208160711213446285 697286703060266705042357)
                      ·
                        rfl

theorem cell23_1357961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_1357961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1357961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1357961 prefixEnd_1357961 := by exact prefixLift 1357961
  have htrace : WordTrace (prefixWord ++ tailWord_1357961) baseStart_1357961 baseEnd_1357961 := by
    simpa [prefixWord, tailWord_1357961, baseEnd_1357961] using wordTrace_append hprefix tailTrace_1357961
  have hstable : (prefixWord ++ tailWord_1357961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357961).length < 2 ^ (prefixWord ++ tailWord_1357961).sum := by decide
  have hdescent : baseEnd_1357961 < baseStart_1357961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358012 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1358012 : Nat := 118140960795 + 1358012 * 2 ^ 59
def prefixEnd_1358012 : Nat := 4983230072969 + 3 ^ 40 * 1358012 * 2
def baseEnd_1358012 : Nat := 697312890573646005504623

theorem tailTrace_1358012 : CollatzResearch.WordTrace tailWord_1358012 prefixEnd_1358012 697312890573646005504623 := by
  unfold tailWord_1358012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24765383378080964414910145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33020511170774619219880193 24765383378080964414910145)
  ·
    refine ⟨18574037533560723311182609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24765383378080964414910145 18574037533560723311182609)
    ·
      refine ⟨13930528150170542483386957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18574037533560723311182609 13930528150170542483386957)
      ·
        refine ⟨5223948056313953431270109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13930528150170542483386957 5223948056313953431270109)
        ·
          refine ⟨1958980521117732536726291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5223948056313953431270109 1958980521117732536726291)
          ·
            refine ⟨2938470781676598805089437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958980521117732536726291 2938470781676598805089437)
            ·
              refine ⟨1101926543128724551908539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2938470781676598805089437 1101926543128724551908539)
              ·
                refine ⟨1652889814693086827862809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101926543128724551908539 1652889814693086827862809)
                ·
                  refine ⟨1239667361019815120897107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652889814693086827862809 1239667361019815120897107)
                  ·
                    refine ⟨1859501041529722681345661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239667361019815120897107 1859501041529722681345661)
                    ·
                      refine ⟨697312890573646005504623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859501041529722681345661 697312890573646005504623)
                      ·
                        rfl

theorem cell23_1358012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1358012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358012 prefixEnd_1358012 := by exact prefixLift 1358012
  have htrace : WordTrace (prefixWord ++ tailWord_1358012) baseStart_1358012 baseEnd_1358012 := by
    simpa [prefixWord, tailWord_1358012, baseEnd_1358012] using wordTrace_append hprefix tailTrace_1358012
  have hstable : (prefixWord ++ tailWord_1358012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358012).length < 2 ^ (prefixWord ++ tailWord_1358012).sum := by decide
  have hdescent : baseEnd_1358012 < baseStart_1358012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358038 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1358038 : Nat := 118140960795 + 1358038 * 2 ^ 59
def prefixEnd_1358038 : Nat := 4983230072969 + 3 ^ 40 * 1358038 * 2
def baseEnd_1358038 : Nat := 697326241070662903779503

theorem tailTrace_1358038 : CollatzResearch.WordTrace tailWord_1358038 prefixEnd_1358038 697326241070662903779503 := by
  unfold tailWord_1358038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095732190879233454391673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33021143369378490180177845 3095732190879233454391673)
  ·
    refine ⟨2321799143159425090793755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3095732190879233454391673 2321799143159425090793755)
    ·
      refine ⟨3482698714739137636190633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321799143159425090793755 3482698714739137636190633)
      ·
        refine ⟨2612024036054353227142975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3482698714739137636190633 2612024036054353227142975)
        ·
          refine ⟨3918036054081529840714463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612024036054353227142975 3918036054081529840714463)
          ·
            refine ⟨5877054081122294761071695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918036054081529840714463 5877054081122294761071695)
            ·
              refine ⟨8815581121683442141607543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877054081122294761071695 8815581121683442141607543)
              ·
                refine ⟨13223371682525163212411315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815581121683442141607543 13223371682525163212411315)
                ·
                  refine ⟨19835057523787744818616973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13223371682525163212411315 19835057523787744818616973)
                  ·
                    refine ⟨7438146571420404306981365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19835057523787744818616973 7438146571420404306981365)
                    ·
                      refine ⟨697326241070662903779503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7438146571420404306981365 697326241070662903779503)
                      ·
                        rfl

theorem cell23_1358038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1358038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358038 prefixEnd_1358038 := by exact prefixLift 1358038
  have htrace : WordTrace (prefixWord ++ tailWord_1358038) baseStart_1358038 baseEnd_1358038 := by
    simpa [prefixWord, tailWord_1358038, baseEnd_1358038] using wordTrace_append hprefix tailTrace_1358038
  have hstable : (prefixWord ++ tailWord_1358038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358038).length < 2 ^ (prefixWord ++ tailWord_1358038).sum := by decide
  have hdescent : baseEnd_1358038 < baseStart_1358038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358088 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1358088 : Nat := 118140960795 + 1358088 * 2 ^ 59
def prefixEnd_1358088 : Nat := 4983230072969 + 3 ^ 40 * 1358088 * 2
def baseEnd_1358088 : Nat := 232450638367795902718091

theorem tailTrace_1358088 : CollatzResearch.WordTrace tailWord_1358088 prefixEnd_1358088 232450638367795902718091 := by
  unfold tailWord_1358088
  simp only [CollatzResearch.WordTrace]
  refine ⟨24766769351943296904793459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33022359135924395873057945 24766769351943296904793459)
  ·
    refine ⟨37150154027914945357190189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24766769351943296904793459 37150154027914945357190189)
    ·
      refine ⟨13931307760468104508946321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37150154027914945357190189 13931307760468104508946321)
      ·
        refine ⟨10448480820351078381709741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13931307760468104508946321 10448480820351078381709741)
        ·
          refine ⟨3918180307631654393141153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10448480820351078381709741 3918180307631654393141153)
          ·
            refine ⟨2938635230723740794855865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3918180307631654393141153 2938635230723740794855865)
            ·
              refine ⟨2203976423042805596141899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938635230723740794855865 2203976423042805596141899)
              ·
                refine ⟨3305964634564208394212849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203976423042805596141899 3305964634564208394212849)
                ·
                  refine ⟨2479473475923156295659637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305964634564208394212849 2479473475923156295659637)
                  ·
                    refine ⟨232450638367795902718091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2479473475923156295659637 232450638367795902718091)
                    ·
                      rfl

theorem cell23_1358088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1358088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358088 prefixEnd_1358088 := by exact prefixLift 1358088
  have htrace : WordTrace (prefixWord ++ tailWord_1358088) baseStart_1358088 baseEnd_1358088 := by
    simpa [prefixWord, tailWord_1358088, baseEnd_1358088] using wordTrace_append hprefix tailTrace_1358088
  have hstable : (prefixWord ++ tailWord_1358088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358088).length < 2 ^ (prefixWord ++ tailWord_1358088).sum := by decide
  have hdescent : baseEnd_1358088 < baseStart_1358088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358108 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1358108 : Nat := 118140960795 + 1358108 * 2 ^ 59
def prefixEnd_1358108 : Nat := 4983230072969 + 3 ^ 40 * 1358108 * 2
def baseEnd_1358108 : Nat := 697362184716477629904181

theorem tailTrace_1358108 : CollatzResearch.WordTrace tailWord_1358108 prefixEnd_1358108 697362184716477629904181 := by
  unfold tailWord_1358108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24767134081907068612657489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33022845442542758150209985 24767134081907068612657489)
  ·
    refine ⟨18575350561430301459493117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24767134081907068612657489 18575350561430301459493117)
    ·
      refine ⟨6965756460536363047309919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18575350561430301459493117 6965756460536363047309919)
      ·
        refine ⟨10448634690804544570964879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965756460536363047309919 10448634690804544570964879)
        ·
          refine ⟨15672952036206816856447319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10448634690804544570964879 15672952036206816856447319)
          ·
            refine ⟨23509428054310225284670979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672952036206816856447319 23509428054310225284670979)
            ·
              refine ⟨35264142081465337927006469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23509428054310225284670979 35264142081465337927006469)
              ·
                refine ⟨6612026640274750861313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35264142081465337927006469 6612026640274750861313713)
                ·
                  refine ⟨4959019980206063145985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612026640274750861313713 4959019980206063145985285)
                  ·
                    refine ⟨929816246288636839872241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959019980206063145985285 929816246288636839872241)
                    ·
                      refine ⟨697362184716477629904181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929816246288636839872241 697362184716477629904181)
                      ·
                        rfl

theorem cell23_1358108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1358108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358108 prefixEnd_1358108 := by exact prefixLift 1358108
  have htrace : WordTrace (prefixWord ++ tailWord_1358108) baseStart_1358108 baseEnd_1358108 := by
    simpa [prefixWord, tailWord_1358108, baseEnd_1358108] using wordTrace_append hprefix tailTrace_1358108
  have hstable : (prefixWord ++ tailWord_1358108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358108).length < 2 ^ (prefixWord ++ tailWord_1358108).sum := by decide
  have hdescent : baseEnd_1358108 < baseStart_1358108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358109 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 5]
def baseStart_1358109 : Nat := 118140960795 + 1358109 * 2 ^ 59
def prefixEnd_1358109 : Nat := 4983230072969 + 3 ^ 40 * 1358109 * 2
def baseEnd_1358109 : Nat := 77484744244125791776853

theorem tailTrace_1358109 : CollatzResearch.WordTrace tailWord_1358109 prefixEnd_1358109 77484744244125791776853 := by
  unfold tailWord_1358109
  simp only [CollatzResearch.WordTrace]
  refine ⟨49534304636810514396101381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33022869757873676264067587 49534304636810514396101381)
  ·
    refine ⟨9287682119401971449269009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49534304636810514396101381 9287682119401971449269009)
    ·
      refine ⟨6965761589551478586951757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9287682119401971449269009 6965761589551478586951757)
      ·
        refine ⟨2612160596081804470106909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6965761589551478586951757 2612160596081804470106909)
        ·
          refine ⟨979560223530676676290091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2612160596081804470106909 979560223530676676290091)
          ·
            refine ⟨1469340335296015014435137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979560223530676676290091 1469340335296015014435137)
            ·
              refine ⟨1102005251472011260826353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469340335296015014435137 1102005251472011260826353)
              ·
                refine ⟨826503938604008445619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102005251472011260826353 826503938604008445619765)
                ·
                  refine ⟨77484744244125791776853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826503938604008445619765 77484744244125791776853)
                  ·
                    rfl

theorem cell23_1358109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_1358109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358109 prefixEnd_1358109 := by exact prefixLift 1358109
  have htrace : WordTrace (prefixWord ++ tailWord_1358109) baseStart_1358109 baseEnd_1358109 := by
    simpa [prefixWord, tailWord_1358109, baseEnd_1358109] using wordTrace_append hprefix tailTrace_1358109
  have hstable : (prefixWord ++ tailWord_1358109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358109).length < 2 ^ (prefixWord ++ tailWord_1358109).sum := by decide
  have hdescent : baseEnd_1358109 < baseStart_1358109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358131 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 6]
def baseStart_1358131 : Nat := 118140960795 + 1358131 * 2 ^ 59
def prefixEnd_1358131 : Nat := 4983230072969 + 3 ^ 40 * 1358131 * 2
def baseEnd_1358131 : Nat := 77485999419059004435175

theorem tailTrace_1358131 : CollatzResearch.WordTrace tailWord_1358131 prefixEnd_1358131 77485999419059004435175 := by
  unfold tailWord_1358131
  simp only [CollatzResearch.WordTrace]
  refine ⟨49535107042730812153402247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33023404695153874768934831 49535107042730812153402247)
  ·
    refine ⟨74302660564096218230103371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49535107042730812153402247 74302660564096218230103371)
    ·
      refine ⟨111453990846144327345155057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74302660564096218230103371 111453990846144327345155057)
      ·
        refine ⟨83590493134608245508866293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111453990846144327345155057 83590493134608245508866293)
        ·
          refine ⟨7836608731369523016456215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83590493134608245508866293 7836608731369523016456215)
          ·
            refine ⟨11754913097054284524684323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7836608731369523016456215 11754913097054284524684323)
            ·
              refine ⟨17632369645581426787026485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11754913097054284524684323 17632369645581426787026485)
              ·
                refine ⟨1653034654273258761283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17632369645581426787026485 1653034654273258761283733)
                ·
                  refine ⟨77485999419059004435175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1653034654273258761283733 77485999419059004435175)
                  ·
                    rfl

theorem cell23_1358131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 6].length) (baseStart_1358131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358131 prefixEnd_1358131 := by exact prefixLift 1358131
  have htrace : WordTrace (prefixWord ++ tailWord_1358131) baseStart_1358131 baseEnd_1358131 := by
    simpa [prefixWord, tailWord_1358131, baseEnd_1358131] using wordTrace_append hprefix tailTrace_1358131
  have hstable : (prefixWord ++ tailWord_1358131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358131).length < 2 ^ (prefixWord ++ tailWord_1358131).sum := by decide
  have hdescent : baseEnd_1358131 < baseStart_1358131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358145 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1358145 : Nat := 118140960795 + 1358145 * 2 ^ 59
def prefixEnd_1358145 : Nat := 4983230072969 + 3 ^ 40 * 1358145 * 2
def baseEnd_1358145 : Nat := 697381183500693985141511

theorem tailTrace_1358145 : CollatzResearch.WordTrace tailWord_1358145 prefixEnd_1358145 697381183500693985141511 := by
  unfold tailWord_1358145
  simp only [CollatzResearch.WordTrace]
  refine ⟨49535617664680092544411889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33023745109786728362941259 49535617664680092544411889)
  ·
    refine ⟨37151713248510069408308917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49535617664680092544411889 37151713248510069408308917)
    ·
      refine ⟨3482973117047819007028961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37151713248510069408308917 3482973117047819007028961)
      ·
        refine ⟨2612229837785864255271721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3482973117047819007028961 2612229837785864255271721)
        ·
          refine ⟨1959172378339398191453791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612229837785864255271721 1959172378339398191453791)
          ·
            refine ⟨2938758567509097287180687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959172378339398191453791 2938758567509097287180687)
            ·
              refine ⟨4408137851263645930771031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938758567509097287180687 4408137851263645930771031)
              ·
                refine ⟨6612206776895468896156547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408137851263645930771031 6612206776895468896156547)
                ·
                  refine ⟨9918310165343203344234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612206776895468896156547 9918310165343203344234821)
                  ·
                    refine ⟨1859683156001850627044029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9918310165343203344234821 1859683156001850627044029)
                    ·
                      refine ⟨697381183500693985141511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859683156001850627044029 697381183500693985141511)
                      ·
                        rfl

theorem cell23_1358145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1358145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358145 prefixEnd_1358145 := by exact prefixLift 1358145
  have htrace : WordTrace (prefixWord ++ tailWord_1358145) baseStart_1358145 baseEnd_1358145 := by
    simpa [prefixWord, tailWord_1358145, baseEnd_1358145] using wordTrace_append hprefix tailTrace_1358145
  have hstable : (prefixWord ++ tailWord_1358145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358145).length < 2 ^ (prefixWord ++ tailWord_1358145).sum := by decide
  have hdescent : baseEnd_1358145 < baseStart_1358145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358165 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 6]
def baseStart_1358165 : Nat := 118140960795 + 1358165 * 2 ^ 59
def prefixEnd_1358165 : Nat := 4983230072969 + 3 ^ 40 * 1358165 * 2
def baseEnd_1358165 : Nat := 77487939234864878543491

theorem tailTrace_1358165 : CollatzResearch.WordTrace tailWord_1358165 prefixEnd_1358165 77487939234864878543491 := by
  unfold tailWord_1358165
  simp only [CollatzResearch.WordTrace]
  refine ⟨49536347124607635960139949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33024231416405090640093299 49536347124607635960139949)
  ·
    refine ⟨18576130171727863485052481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49536347124607635960139949 18576130171727863485052481)
    ·
      refine ⟨13932097628795897613789361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18576130171727863485052481 13932097628795897613789361)
      ·
        refine ⟨10449073221596923210342021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13932097628795897613789361 10449073221596923210342021)
        ·
          refine ⟨1959201229049423101939129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10449073221596923210342021 1959201229049423101939129)
          ·
            refine ⟨1469400921787067326454347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959201229049423101939129 1469400921787067326454347)
            ·
              refine ⟨2204101382680600989681521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469400921787067326454347 2204101382680600989681521)
              ·
                refine ⟨1653076037010450742261141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204101382680600989681521 1653076037010450742261141)
                ·
                  refine ⟨77487939234864878543491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1653076037010450742261141 77487939234864878543491)
                  ·
                    rfl

theorem cell23_1358165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_1358165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358165 prefixEnd_1358165 := by exact prefixLift 1358165
  have htrace : WordTrace (prefixWord ++ tailWord_1358165) baseStart_1358165 baseEnd_1358165 := by
    simpa [prefixWord, tailWord_1358165, baseEnd_1358165] using wordTrace_append hprefix tailTrace_1358165
  have hstable : (prefixWord ++ tailWord_1358165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358165).length < 2 ^ (prefixWord ++ tailWord_1358165).sum := by decide
  have hdescent : baseEnd_1358165 < baseStart_1358165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358191 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 6]
def baseStart_1358191 : Nat := 118140960795 + 1358191 * 2 ^ 59
def prefixEnd_1358191 : Nat := 4983230072969 + 3 ^ 40 * 1358191 * 2
def baseEnd_1358191 : Nat := 232468267870266935055433

theorem tailTrace_1358191 : CollatzResearch.WordTrace tailWord_1358191 prefixEnd_1358191 232468267870266935055433 := by
  unfold tailWord_1358191
  simp only [CollatzResearch.WordTrace]
  refine ⟨49537295422513442400586427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33024863615008961600390951 49537295422513442400586427)
  ·
    refine ⟨74305943133770163600879641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49537295422513442400586427 74305943133770163600879641)
    ·
      refine ⟨55729457350327622700659731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74305943133770163600879641 55729457350327622700659731)
      ·
        refine ⟨83594186025491434050989597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55729457350327622700659731 83594186025491434050989597)
        ·
          refine ⟨31347819759559287769121099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83594186025491434050989597 31347819759559287769121099)
          ·
            refine ⟨47021729639338931653681649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31347819759559287769121099 47021729639338931653681649)
            ·
              refine ⟨35266297229504198740261237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47021729639338931653681649 35266297229504198740261237)
              ·
                refine ⟨3306215365266018631899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35266297229504198740261237 3306215365266018631899491)
                ·
                  refine ⟨4959323047899027947849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306215365266018631899491 4959323047899027947849237)
                  ·
                    refine ⟨232468267870266935055433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4959323047899027947849237 232468267870266935055433)
                    ·
                      rfl

theorem cell23_1358191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_1358191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358191 prefixEnd_1358191 := by exact prefixLift 1358191
  have htrace : WordTrace (prefixWord ++ tailWord_1358191) baseStart_1358191 baseEnd_1358191 := by
    simpa [prefixWord, tailWord_1358191, baseEnd_1358191] using wordTrace_append hprefix tailTrace_1358191
  have hstable : (prefixWord ++ tailWord_1358191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358191).length < 2 ^ (prefixWord ++ tailWord_1358191).sum := by decide
  have hdescent : baseEnd_1358191 < baseStart_1358191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358201 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1358201 : Nat := 118140960795 + 1358201 * 2 ^ 59
def prefixEnd_1358201 : Nat := 4983230072969 + 3 ^ 40 * 1358201 * 2
def baseEnd_1358201 : Nat := 697409938417345766041253

theorem tailTrace_1358201 : CollatzResearch.WordTrace tailWord_1358201 prefixEnd_1358201 697409938417345766041253 := by
  unfold tailWord_1358201
  simp only [CollatzResearch.WordTrace]
  refine ⟨49537660152477214108450457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33025106768318142738966971 49537660152477214108450457)
  ·
    refine ⟨37153245114357910581337843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49537660152477214108450457 37153245114357910581337843)
    ·
      refine ⟨55729867671536865872006765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37153245114357910581337843 55729867671536865872006765)
      ·
        refine ⟨20898700376826324702002537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55729867671536865872006765 20898700376826324702002537)
        ·
          refine ⟨15674025282619743526501903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20898700376826324702002537 15674025282619743526501903)
          ·
            refine ⟨23511037923929615289752855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15674025282619743526501903 23511037923929615289752855)
            ·
              refine ⟨35266556885894422934629283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23511037923929615289752855 35266556885894422934629283)
              ·
                refine ⟨52899835328841634401943925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35266556885894422934629283 52899835328841634401943925)
                ·
                  refine ⟨4959359562078903225182243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52899835328841634401943925 4959359562078903225182243)
                  ·
                    refine ⟨7439039343118354837773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959359562078903225182243 7439039343118354837773365)
                    ·
                      refine ⟨697409938417345766041253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7439039343118354837773365 697409938417345766041253)
                      ·
                        rfl

theorem cell23_1358201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1358201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358201 prefixEnd_1358201 := by exact prefixLift 1358201
  have htrace : WordTrace (prefixWord ++ tailWord_1358201) baseStart_1358201 baseEnd_1358201 := by
    simpa [prefixWord, tailWord_1358201, baseEnd_1358201] using wordTrace_append hprefix tailTrace_1358201
  have hstable : (prefixWord ++ tailWord_1358201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358201).length < 2 ^ (prefixWord ++ tailWord_1358201).sum := by decide
  have hdescent : baseEnd_1358201 < baseStart_1358201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358209 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1358209 : Nat := 118140960795 + 1358209 * 2 ^ 59
def prefixEnd_1358209 : Nat := 4983230072969 + 3 ^ 40 * 1358209 * 2
def baseEnd_1358209 : Nat := 697414046262581734741217

theorem tailTrace_1358209 : CollatzResearch.WordTrace tailWord_1358209 prefixEnd_1358209 697414046262581734741217 := by
  unfold tailWord_1358209
  simp only [CollatzResearch.WordTrace]
  refine ⟨49537951936448231474741681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33025301290965487649827787 49537951936448231474741681)
  ·
    refine ⟨37153463952336173606056261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49537951936448231474741681 37153463952336173606056261)
    ·
      refine ⟨6966274491063032551135549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37153463952336173606056261 6966274491063032551135549)
      ·
        refine ⟨2612352934148637206675831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6966274491063032551135549 2612352934148637206675831)
        ·
          refine ⟨3918529401222955810013747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612352934148637206675831 3918529401222955810013747)
          ·
            refine ⟨5877794101834433715020621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918529401222955810013747 5877794101834433715020621)
            ·
              refine ⟨2204172788187912643132733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5877794101834433715020621 2204172788187912643132733)
              ·
                refine ⟨826564795570467241174775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204172788187912643132733 826564795570467241174775)
                ·
                  refine ⟨1239847193355700861762163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826564795570467241174775 1239847193355700861762163)
                  ·
                    refine ⟨1859770790033551292643245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239847193355700861762163 1859770790033551292643245)
                    ·
                      refine ⟨697414046262581734741217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859770790033551292643245 697414046262581734741217)
                      ·
                        rfl

theorem cell23_1358209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1358209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358209 prefixEnd_1358209 := by exact prefixLift 1358209
  have htrace : WordTrace (prefixWord ++ tailWord_1358209) baseStart_1358209 baseEnd_1358209 := by
    simpa [prefixWord, tailWord_1358209, baseEnd_1358209] using wordTrace_append hprefix tailTrace_1358209
  have hstable : (prefixWord ++ tailWord_1358209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358209).length < 2 ^ (prefixWord ++ tailWord_1358209).sum := by decide
  have hdescent : baseEnd_1358209 < baseStart_1358209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358265 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1358265 : Nat := 118140960795 + 1358265 * 2 ^ 59
def prefixEnd_1358265 : Nat := 4983230072969 + 3 ^ 40 * 1358265 * 2
def baseEnd_1358265 : Nat := 697442801179233515640959

theorem tailTrace_1358265 : CollatzResearch.WordTrace tailWord_1358265 prefixEnd_1358265 697442801179233515640959 := by
  unfold tailWord_1358265
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539994424245353038780249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33026662949496902025853499 49539994424245353038780249)
  ·
    refine ⟨37154995818184014779085187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49539994424245353038780249 37154995818184014779085187)
    ·
      refine ⟨55732493727276022168627781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37154995818184014779085187 55732493727276022168627781)
      ·
        refine ⟨10449842573864254156617709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55732493727276022168627781 10449842573864254156617709)
        ·
          refine ⟨3918690965199095308731641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10449842573864254156617709 3918690965199095308731641)
          ·
            refine ⟨2939018223899321481548731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3918690965199095308731641 2939018223899321481548731)
            ·
              refine ⟨4408527335848982222323097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939018223899321481548731 4408527335848982222323097)
              ·
                refine ⟨3306395501886736666742323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408527335848982222323097 3306395501886736666742323)
                ·
                  refine ⟨4959593252830105000113485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306395501886736666742323 4959593252830105000113485)
                  ·
                    refine ⟨1859847469811289375042557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4959593252830105000113485 1859847469811289375042557)
                    ·
                      refine ⟨697442801179233515640959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859847469811289375042557 697442801179233515640959)
                      ·
                        rfl

theorem cell23_1358265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1358265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358265 prefixEnd_1358265 := by exact prefixLift 1358265
  have htrace : WordTrace (prefixWord ++ tailWord_1358265) baseStart_1358265 baseEnd_1358265 := by
    simpa [prefixWord, tailWord_1358265, baseEnd_1358265] using wordTrace_append hprefix tailTrace_1358265
  have hstable : (prefixWord ++ tailWord_1358265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358265).length < 2 ^ (prefixWord ++ tailWord_1358265).sum := by decide
  have hdescent : baseEnd_1358265 < baseStart_1358265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358282 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1358282 : Nat := 118140960795 + 1358282 * 2 ^ 59
def prefixEnd_1358282 : Nat := 4983230072969 + 3 ^ 40 * 1358282 * 2
def baseEnd_1358282 : Nat := 697451530350359949128381

theorem tailTrace_1358282 : CollatzResearch.WordTrace tailWord_1358282 prefixEnd_1358282 697451530350359949128381 := by
  unfold tailWord_1358282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385153616295941235537275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33027076310122509961432733 12385153616295941235537275)
  ·
    refine ⟨18577730424443911853305913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385153616295941235537275 18577730424443911853305913)
    ·
      refine ⟨13933297818332933889979435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18577730424443911853305913 13933297818332933889979435)
      ·
        refine ⟨20899946727499400834969153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13933297818332933889979435 20899946727499400834969153)
        ·
          refine ⟨15674960045624550626226865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20899946727499400834969153 15674960045624550626226865)
          ·
            refine ⟨11756220034218412969670149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15674960045624550626226865 11756220034218412969670149)
            ·
              refine ⟨2204291256415952431813153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11756220034218412969670149 2204291256415952431813153)
              ·
                refine ⟨1653218442311964323859865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204291256415952431813153 1653218442311964323859865)
                ·
                  refine ⟨1239913831733973242894899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653218442311964323859865 1239913831733973242894899)
                  ·
                    refine ⟨1859870747600959864342349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239913831733973242894899 1859870747600959864342349)
                    ·
                      refine ⟨697451530350359949128381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1859870747600959864342349 697451530350359949128381)
                      ·
                        rfl

theorem cell23_1358282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1358282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358282 prefixEnd_1358282 := by exact prefixLift 1358282
  have htrace : WordTrace (prefixWord ++ tailWord_1358282) baseStart_1358282 baseEnd_1358282 := by
    simpa [prefixWord, tailWord_1358282, baseEnd_1358282] using wordTrace_append hprefix tailTrace_1358282
  have hstable : (prefixWord ++ tailWord_1358282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358282).length < 2 ^ (prefixWord ++ tailWord_1358282).sum := by decide
  have hdescent : baseEnd_1358282 < baseStart_1358282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358292 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1358292 : Nat := 118140960795 + 1358292 * 2 ^ 59
def prefixEnd_1358292 : Nat := 4983230072969 + 3 ^ 40 * 1358292 * 2
def baseEnd_1358292 : Nat := 697456665156904910003335

theorem tailTrace_1358292 : CollatzResearch.WordTrace tailWord_1358292 prefixEnd_1358292 697456665156904910003335 := by
  unfold tailWord_1358292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770489597573768325006565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33027319463431691100008753 24770489597573768325006565)
  ·
    refine ⟨4644466799545081560938731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24770489597573768325006565 4644466799545081560938731)
    ·
      refine ⟨6966700199317622341408097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4644466799545081560938731 6966700199317622341408097)
      ·
        refine ⟨5225025149488216756056073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6966700199317622341408097 5225025149488216756056073)
        ·
          refine ⟨3918768862116162567042055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5225025149488216756056073 3918768862116162567042055)
          ·
            refine ⟨5878153293174243850563083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918768862116162567042055 5878153293174243850563083)
            ·
              refine ⟨8817229939761365775844625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878153293174243850563083 8817229939761365775844625)
              ·
                refine ⟨6612922454821024331883469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8817229939761365775844625 6612922454821024331883469)
                ·
                  refine ⟨2479845920557884124456301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6612922454821024331883469 2479845920557884124456301)
                  ·
                    refine ⟨929942220209206546671113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479845920557884124456301 929942220209206546671113)
                    ·
                      refine ⟨697456665156904910003335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929942220209206546671113 697456665156904910003335)
                      ·
                        rfl

theorem cell23_1358292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1358292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358292 prefixEnd_1358292 := by exact prefixLift 1358292
  have htrace : WordTrace (prefixWord ++ tailWord_1358292) baseStart_1358292 baseEnd_1358292 := by
    simpa [prefixWord, tailWord_1358292, baseEnd_1358292] using wordTrace_append hprefix tailTrace_1358292
  have hstable : (prefixWord ++ tailWord_1358292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358292).length < 2 ^ (prefixWord ++ tailWord_1358292).sum := by decide
  have hdescent : baseEnd_1358292 < baseStart_1358292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358298 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_1358298 : Nat := 118140960795 + 1358298 * 2 ^ 59
def prefixEnd_1358298 : Nat := 4983230072969 + 3 ^ 40 * 1358298 * 2
def baseEnd_1358298 : Nat := 232486582013610628842769

theorem tailTrace_1358298 : CollatzResearch.WordTrace tailWord_1358298 prefixEnd_1358298 232486582013610628842769 := by
  unfold tailWord_1358298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385299508281449918682887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33027465355417199783154365 12385299508281449918682887)
  ·
    refine ⟨18577949262422174878024331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385299508281449918682887 18577949262422174878024331)
    ·
      refine ⟨27866923893633262317036497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18577949262422174878024331 27866923893633262317036497)
      ·
        refine ⟨20900192920224946737777373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27866923893633262317036497 20900192920224946737777373)
        ·
          refine ⟨7837572345084355026666515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20900192920224946737777373 7837572345084355026666515)
          ·
            refine ⟨11756358517626532539999773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837572345084355026666515 11756358517626532539999773)
            ·
              refine ⟨4408634444109949702499915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11756358517626532539999773 4408634444109949702499915)
              ·
                refine ⟨6612951666164924553749873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408634444109949702499915 6612951666164924553749873)
                ·
                  refine ⟨4959713749623693415312405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612951666164924553749873 4959713749623693415312405)
                  ·
                    refine ⟨232486582013610628842769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4959713749623693415312405 232486582013610628842769)
                    ·
                      rfl

theorem cell23_1358298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_1358298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358298 prefixEnd_1358298 := by exact prefixLift 1358298
  have htrace : WordTrace (prefixWord ++ tailWord_1358298) baseStart_1358298 baseEnd_1358298 := by
    simpa [prefixWord, tailWord_1358298, baseEnd_1358298] using wordTrace_append hprefix tailTrace_1358298
  have hstable : (prefixWord ++ tailWord_1358298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358298).length < 2 ^ (prefixWord ++ tailWord_1358298).sum := by decide
  have hdescent : baseEnd_1358298 < baseStart_1358298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358356 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1358356 : Nat := 118140960795 + 1358356 * 2 ^ 59
def prefixEnd_1358356 : Nat := 4983230072969 + 3 ^ 40 * 1358356 * 2
def baseEnd_1358356 : Nat := 697489527918792659603041

theorem tailTrace_1358356 : CollatzResearch.WordTrace tailWord_1358356 prefixEnd_1358356 697489527918792659603041 := by
  unfold tailWord_1358356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771656733457837790171461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33028875644610450386895281 24771656733457837790171461)
  ·
    refine ⟨4644685637523344585657149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24771656733457837790171461 4644685637523344585657149)
    ·
      refine ⟨1741757114071254219621431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4644685637523344585657149 1741757114071254219621431)
      ·
        refine ⟨2612635671106881329432147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741757114071254219621431 2612635671106881329432147)
        ·
          refine ⟨3918953506660321994148221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612635671106881329432147 3918953506660321994148221)
          ·
            refine ⟨1469607564997620747805583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3918953506660321994148221 1469607564997620747805583)
            ·
              refine ⟨2204411347496431121708375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469607564997620747805583 2204411347496431121708375)
              ·
                refine ⟨3306617021244646682562563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204411347496431121708375 3306617021244646682562563)
                ·
                  refine ⟨4959925531866970023843845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306617021244646682562563 4959925531866970023843845)
                  ·
                    refine ⟨929986037225056879470721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959925531866970023843845 929986037225056879470721)
                    ·
                      refine ⟨697489527918792659603041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 929986037225056879470721 697489527918792659603041)
                      ·
                        rfl

theorem cell23_1358356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1358356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358356 prefixEnd_1358356 := by exact prefixLift 1358356
  have htrace : WordTrace (prefixWord ++ tailWord_1358356) baseStart_1358356 baseEnd_1358356 := by
    simpa [prefixWord, tailWord_1358356, baseEnd_1358356] using wordTrace_append hprefix tailTrace_1358356
  have hstable : (prefixWord ++ tailWord_1358356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358356).length < 2 ^ (prefixWord ++ tailWord_1358356).sum := by decide
  have hdescent : baseEnd_1358356 < baseStart_1358356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358408 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1358408 : Nat := 118140960795 + 1358408 * 2 ^ 59
def prefixEnd_1358408 : Nat := 4983230072969 + 3 ^ 40 * 1358408 * 2
def baseEnd_1358408 : Nat := 697516228912826456152801

theorem tailTrace_1358408 : CollatzResearch.WordTrace tailWord_1358408 prefixEnd_1358408 697516228912826456152801 := by
  unfold tailWord_1358408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24772605031363644230617939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33030140041818192307490585 24772605031363644230617939)
  ·
    refine ⟨37158907547045466345926909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24772605031363644230617939 37158907547045466345926909)
    ·
      refine ⟨13934590330142049879722591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37158907547045466345926909 13934590330142049879722591)
      ·
        refine ⟨20901885495213074819583887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13934590330142049879722591 20901885495213074819583887)
        ·
          refine ⟨31352828242819612229375831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20901885495213074819583887 31352828242819612229375831)
          ·
            refine ⟨47029242364229418344063747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31352828242819612229375831 47029242364229418344063747)
            ·
              refine ⟨70543863546344127516095621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47029242364229418344063747 70543863546344127516095621)
              ·
                refine ⟨13226974414939523909267929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70543863546344127516095621 13226974414939523909267929)
                ·
                  refine ⟨9920230811204642931950947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13226974414939523909267929 9920230811204642931950947)
                  ·
                    refine ⟨14880346216806964397926421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9920230811204642931950947 14880346216806964397926421)
                    ·
                      refine ⟨697516228912826456152801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14880346216806964397926421 697516228912826456152801)
                      ·
                        rfl

theorem cell23_1358408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1358408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358408 prefixEnd_1358408 := by exact prefixLift 1358408
  have htrace : WordTrace (prefixWord ++ tailWord_1358408) baseStart_1358408 baseEnd_1358408 := by
    simpa [prefixWord, tailWord_1358408, baseEnd_1358408] using wordTrace_append hprefix tailTrace_1358408
  have hstable : (prefixWord ++ tailWord_1358408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358408).length < 2 ^ (prefixWord ++ tailWord_1358408).sum := by decide
  have hdescent : baseEnd_1358408 < baseStart_1358408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358465 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1358465 : Nat := 118140960795 + 1358465 * 2 ^ 59
def prefixEnd_1358465 : Nat := 4983230072969 + 3 ^ 40 * 1358465 * 2
def baseEnd_1358465 : Nat := 232515165770044244380013

theorem tailTrace_1358465 : CollatzResearch.WordTrace tailWord_1358465 prefixEnd_1358465 232515165770044244380013 := by
  unfold tailWord_1358465
  simp only [CollatzResearch.WordTrace]
  refine ⟨49547289023520787196060849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33031526015680524797373899 49547289023520787196060849)
  ·
    refine ⟨37160466767640590397045637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49547289023520787196060849 37160466767640590397045637)
    ·
      refine ⟨6967587518932610699446057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37160466767640590397045637 6967587518932610699446057)
      ·
        refine ⟨5225690639199458024584543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6967587518932610699446057 5225690639199458024584543)
        ·
          refine ⟨7838535958799187036876815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225690639199458024584543 7838535958799187036876815)
          ·
            refine ⟨11757803938198780555315223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838535958799187036876815 11757803938198780555315223)
            ·
              refine ⟨17636705907298170832972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757803938198780555315223 17636705907298170832972835)
              ·
                refine ⟨26455058860947256249459253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17636705907298170832972835 26455058860947256249459253)
                ·
                  refine ⟨2480161768213805273386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26455058860947256249459253 2480161768213805273386805)
                  ·
                    refine ⟨232515165770044244380013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2480161768213805273386805 232515165770044244380013)
                    ·
                      rfl

theorem cell23_1358465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1358465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358465 prefixEnd_1358465 := by exact prefixLift 1358465
  have htrace : WordTrace (prefixWord ++ tailWord_1358465) baseStart_1358465 baseEnd_1358465 := by
    simpa [prefixWord, tailWord_1358465, baseEnd_1358465] using wordTrace_append hprefix tailTrace_1358465
  have hstable : (prefixWord ++ tailWord_1358465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358465).length < 2 ^ (prefixWord ++ tailWord_1358465).sum := by decide
  have hdescent : baseEnd_1358465 < baseStart_1358465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358482 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1358482 : Nat := 118140960795 + 1358482 * 2 ^ 59
def prefixEnd_1358482 : Nat := 4983230072969 + 3 ^ 40 * 1358482 * 2
def baseEnd_1358482 : Nat := 232518075493753055542487

theorem tailTrace_1358482 : CollatzResearch.WordTrace tailWord_1358482 prefixEnd_1358482 232518075493753055542487 := by
  unfold tailWord_1358482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386977266114799774857425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33031939376306132732953133 12386977266114799774857425)
  ·
    refine ⟨9290232949586099831143069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12386977266114799774857425 9290232949586099831143069)
    ·
      refine ⟨3483837356094787436678651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9290232949586099831143069 3483837356094787436678651)
      ·
        refine ⟨5225756034142181155017977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483837356094787436678651 5225756034142181155017977)
        ·
          refine ⟨3919317025606635866263483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5225756034142181155017977 3919317025606635866263483)
          ·
            refine ⟨5878975538409953799395225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919317025606635866263483 5878975538409953799395225)
            ·
              refine ⟨4409231653807465349546419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878975538409953799395225 4409231653807465349546419)
              ·
                refine ⟨6613847480711198024319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409231653807465349546419 6613847480711198024319629)
                ·
                  refine ⟨2480192805266699259119861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6613847480711198024319629 2480192805266699259119861)
                  ·
                    refine ⟨232518075493753055542487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2480192805266699259119861 232518075493753055542487)
                    ·
                      rfl

theorem cell23_1358482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1358482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358482 prefixEnd_1358482 := by exact prefixLift 1358482
  have htrace : WordTrace (prefixWord ++ tailWord_1358482) baseStart_1358482 baseEnd_1358482 := by
    simpa [prefixWord, tailWord_1358482, baseEnd_1358482] using wordTrace_append hprefix tailTrace_1358482
  have hstable : (prefixWord ++ tailWord_1358482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358482).length < 2 ^ (prefixWord ++ tailWord_1358482).sum := by decide
  have hdescent : baseEnd_1358482 < baseStart_1358482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358532 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1358532 : Nat := 118140960795 + 1358532 * 2 ^ 59
def prefixEnd_1358532 : Nat := 4983230072969 + 3 ^ 40 * 1358532 * 2
def baseEnd_1358532 : Nat := 697579900513983971002231

theorem tailTrace_1358532 : CollatzResearch.WordTrace tailWord_1358532 prefixEnd_1358532 697579900513983971002231 := by
  unfold tailWord_1358532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774866357139028819374925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33033155142852038425833233 24774866357139028819374925)
  ·
    refine ⟨9290574883927135807265597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24774866357139028819374925 9290574883927135807265597)
    ·
      refine ⟨3483965581472675927724599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9290574883927135807265597 3483965581472675927724599)
      ·
        refine ⟨5225948372209013891586899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483965581472675927724599 5225948372209013891586899)
        ·
          refine ⟨7838922558313520837380349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225948372209013891586899 7838922558313520837380349)
          ·
            refine ⟨2939595959367570314017631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7838922558313520837380349 2939595959367570314017631)
            ·
              refine ⟨4409393939051355471026447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939595959367570314017631 4409393939051355471026447)
              ·
                refine ⟨6614090908577033206539671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409393939051355471026447 6614090908577033206539671)
                ·
                  refine ⟨9921136362865549809809507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614090908577033206539671 9921136362865549809809507)
                  ·
                    refine ⟨14881704544298324714714261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9921136362865549809809507 14881704544298324714714261)
                    ·
                      refine ⟨697579900513983971002231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14881704544298324714714261 697579900513983971002231)
                      ·
                        rfl

theorem cell23_1358532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1358532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358532 prefixEnd_1358532 := by exact prefixLift 1358532
  have htrace : WordTrace (prefixWord ++ tailWord_1358532) baseStart_1358532 baseEnd_1358532 := by
    simpa [prefixWord, tailWord_1358532, baseEnd_1358532] using wordTrace_append hprefix tailTrace_1358532
  have hstable : (prefixWord ++ tailWord_1358532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358532).length < 2 ^ (prefixWord ++ tailWord_1358532).sum := by decide
  have hdescent : baseEnd_1358532 < baseStart_1358532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358542 : List Nat := [4, 1, 1, 1, 3, 2, 4, 7]
def baseStart_1358542 : Nat := 118140960795 + 1358542 * 2 ^ 59
def prefixEnd_1358542 : Nat := 4983230072969 + 3 ^ 40 * 1358542 * 2
def baseEnd_1358542 : Nat := 25836482789649219699155

theorem tailTrace_1358542 : CollatzResearch.WordTrace tailWord_1358542 prefixEnd_1358542 25836482789649219699155 := by
  unfold tailWord_1358542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193762180530228668326735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33033398296161219564409253 6193762180530228668326735)
  ·
    refine ⟨9290643270795343002490103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6193762180530228668326735 9290643270795343002490103)
    ·
      refine ⟨13935964906193014503735155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9290643270795343002490103 13935964906193014503735155)
      ·
        refine ⟨20903947359289521755602733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935964906193014503735155 20903947359289521755602733)
        ·
          refine ⟨7838980259733570658351025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20903947359289521755602733 7838980259733570658351025)
          ·
            refine ⟨5879235194800177993763269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7838980259733570658351025 5879235194800177993763269)
            ·
              refine ⟨1102356599025033373830613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5879235194800177993763269 1102356599025033373830613)
              ·
                refine ⟨25836482789649219699155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1102356599025033373830613 25836482789649219699155)
                ·
                  rfl

theorem cell23_1358542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_1358542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358542 prefixEnd_1358542 := by exact prefixLift 1358542
  have htrace : WordTrace (prefixWord ++ tailWord_1358542) baseStart_1358542 baseEnd_1358542 := by
    simpa [prefixWord, tailWord_1358542, baseEnd_1358542] using wordTrace_append hprefix tailTrace_1358542
  have hstable : (prefixWord ++ tailWord_1358542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358542).length < 2 ^ (prefixWord ++ tailWord_1358542).sum := by decide
  have hdescent : baseEnd_1358542 < baseStart_1358542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358556 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1358556 : Nat := 118140960795 + 1358556 * 2 ^ 59
def prefixEnd_1358556 : Nat := 4983230072969 + 3 ^ 40 * 1358556 * 2
def baseEnd_1358556 : Nat := 697592224049691877102121

theorem tailTrace_1358556 : CollatzResearch.WordTrace tailWord_1358556 prefixEnd_1358556 697592224049691877102121 := by
  unfold tailWord_1358556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24775304033095554868811761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33033738710794073158415681 24775304033095554868811761)
  ·
    refine ⟨18581478024821666151608821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24775304033095554868811761 18581478024821666151608821)
    ·
      refine ⟨1742013564827031201713327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18581478024821666151608821 1742013564827031201713327)
      ·
        refine ⟨2613020347240546802569991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742013564827031201713327 2613020347240546802569991)
        ·
          refine ⟨3919530520860820203854987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613020347240546802569991 3919530520860820203854987)
          ·
            refine ⟨5879295781291230305782481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919530520860820203854987 5879295781291230305782481)
            ·
              refine ⟨4409471835968422729336861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879295781291230305782481 4409471835968422729336861)
              ·
                refine ⟨1653551938488158523501323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4409471835968422729336861 1653551938488158523501323)
                ·
                  refine ⟨2480327907732237785251985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653551938488158523501323 2480327907732237785251985)
                  ·
                    refine ⟨1860245930799178338938989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2480327907732237785251985 1860245930799178338938989)
                    ·
                      refine ⟨697592224049691877102121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860245930799178338938989 697592224049691877102121)
                      ·
                        rfl

theorem cell23_1358556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1358556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358556 prefixEnd_1358556 := by exact prefixLift 1358556
  have htrace : WordTrace (prefixWord ++ tailWord_1358556) baseStart_1358556 baseEnd_1358556 := by
    simpa [prefixWord, tailWord_1358556, baseEnd_1358556] using wordTrace_append hprefix tailTrace_1358556
  have hstable : (prefixWord ++ tailWord_1358556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358556).length < 2 ^ (prefixWord ++ tailWord_1358556).sum := by decide
  have hdescent : baseEnd_1358556 < baseStart_1358556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358585 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_1358585 : Nat := 118140960795 + 1358585 * 2 ^ 59
def prefixEnd_1358585 : Nat := 4983230072969 + 3 ^ 40 * 1358585 * 2
def baseEnd_1358585 : Nat := 232535704996224087879829

theorem tailTrace_1358585 : CollatzResearch.WordTrace tailWord_1358585 prefixEnd_1358585 232535704996224087879829 := by
  unfold tailWord_1358585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49551665783086047690429209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33034443855390698460286139 49551665783086047690429209)
  ·
    refine ⟨37163749337314535767821907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49551665783086047690429209 37163749337314535767821907)
    ·
      refine ⟨55745624005971803651732861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37163749337314535767821907 55745624005971803651732861)
      ·
        refine ⟨20904609002239426369399823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55745624005971803651732861 20904609002239426369399823)
        ·
          refine ⟨31356913503359139554099735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20904609002239426369399823 31356913503359139554099735)
          ·
            refine ⟨47035370255038709331149603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31356913503359139554099735 47035370255038709331149603)
            ·
              refine ⟨70553055382558063996724405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47035370255038709331149603 70553055382558063996724405)
              ·
                refine ⟨6614348942114818499692913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70553055382558063996724405 6614348942114818499692913)
                ·
                  refine ⟨4960761706586113874769685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6614348942114818499692913 4960761706586113874769685)
                  ·
                    refine ⟨232535704996224087879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4960761706586113874769685 232535704996224087879829)
                    ·
                      rfl

theorem cell23_1358585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_1358585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358585 prefixEnd_1358585 := by exact prefixLift 1358585
  have htrace : WordTrace (prefixWord ++ tailWord_1358585) baseStart_1358585 baseEnd_1358585 := by
    simpa [prefixWord, tailWord_1358585, baseEnd_1358585] using wordTrace_append hprefix tailTrace_1358585
  have hstable : (prefixWord ++ tailWord_1358585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358585).length < 2 ^ (prefixWord ++ tailWord_1358585).sum := by decide
  have hdescent : baseEnd_1358585 < baseStart_1358585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358586 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_1358586 : Nat := 118140960795 + 1358586 * 2 ^ 59
def prefixEnd_1358586 : Nat := 4983230072969 + 3 ^ 40 * 1358586 * 2
def baseEnd_1358586 : Nat := 697607628469326759726983

theorem tailTrace_1358586 : CollatzResearch.WordTrace tailWord_1358586 prefixEnd_1358586 697607628469326759726983 := by
  unfold tailWord_1358586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387925564020606215303903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33034468170721616574143741 12387925564020606215303903)
  ·
    refine ⟨18581888346030909322955855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387925564020606215303903 18581888346030909322955855)
    ·
      refine ⟨27872832519046363984433783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18581888346030909322955855 27872832519046363984433783)
      ·
        refine ⟨41809248778569545976650675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27872832519046363984433783 41809248778569545976650675)
        ·
          refine ⟨62713873167854318964976013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41809248778569545976650675 62713873167854318964976013)
          ·
            refine ⟨23517702437945369611866005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62713873167854318964976013 23517702437945369611866005)
            ·
              refine ⟨1102392301778689200556219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23517702437945369611866005 1102392301778689200556219)
              ·
                refine ⟨1653588452668033800834329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102392301778689200556219 1653588452668033800834329)
                ·
                  refine ⟨1240191339501025350625747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653588452668033800834329 1240191339501025350625747)
                  ·
                    refine ⟨1860287009251538025938621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240191339501025350625747 1860287009251538025938621)
                    ·
                      refine ⟨697607628469326759726983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860287009251538025938621 697607628469326759726983)
                      ·
                        rfl

theorem cell23_1358586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_1358586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358586 prefixEnd_1358586 := by exact prefixLift 1358586
  have htrace : WordTrace (prefixWord ++ tailWord_1358586) baseStart_1358586 baseEnd_1358586 := by
    simpa [prefixWord, tailWord_1358586, baseEnd_1358586] using wordTrace_append hprefix tailTrace_1358586
  have hstable : (prefixWord ++ tailWord_1358586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358586).length < 2 ^ (prefixWord ++ tailWord_1358586).sum := by decide
  have hdescent : baseEnd_1358586 < baseStart_1358586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358609 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_1358609 : Nat := 118140960795 + 1358609 * 2 ^ 59
def prefixEnd_1358609 : Nat := 4983230072969 + 3 ^ 40 * 1358609 * 2
def baseEnd_1358609 : Nat := 697619438524380169739377

theorem tailTrace_1358609 : CollatzResearch.WordTrace tailWord_1358609 prefixEnd_1358609 697619438524380169739377 := by
  unfold tailWord_1358609
  simp only [CollatzResearch.WordTrace]
  refine ⟨49552541134999099789302881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33035027423332733192868587 49552541134999099789302881)
  ·
    refine ⟨37164405851249324841977161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49552541134999099789302881 37164405851249324841977161)
    ·
      refine ⟨27873304388436993631482871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37164405851249324841977161 27873304388436993631482871)
      ·
        refine ⟨41809956582655490447224307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27873304388436993631482871 41809956582655490447224307)
        ·
          refine ⟨62714934873983235670836461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41809956582655490447224307 62714934873983235670836461)
          ·
            refine ⟨23518100577743713376563673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62714934873983235670836461 23518100577743713376563673)
            ·
              refine ⟨17638575433307785032422755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23518100577743713376563673 17638575433307785032422755)
              ·
                refine ⟨26457863149961677548634133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17638575433307785032422755 26457863149961677548634133)
                ·
                  refine ⟨1240212335154453635092225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26457863149961677548634133 1240212335154453635092225)
                  ·
                    refine ⟨930159251365840226319169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240212335154453635092225 930159251365840226319169)
                    ·
                      refine ⟨697619438524380169739377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930159251365840226319169 697619438524380169739377)
                      ·
                        rfl

theorem cell23_1358609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_1358609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358609 prefixEnd_1358609 := by exact prefixLift 1358609
  have htrace : WordTrace (prefixWord ++ tailWord_1358609) baseStart_1358609 baseEnd_1358609 := by
    simpa [prefixWord, tailWord_1358609, baseEnd_1358609] using wordTrace_append hprefix tailTrace_1358609
  have hstable : (prefixWord ++ tailWord_1358609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358609).length < 2 ^ (prefixWord ++ tailWord_1358609).sum := by decide
  have hdescent : baseEnd_1358609 < baseStart_1358609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358632 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 7]
def baseStart_1358632 : Nat := 118140960795 + 1358632 * 2 ^ 59
def prefixEnd_1358632 : Nat := 4983230072969 + 3 ^ 40 * 1358632 * 2
def baseEnd_1358632 : Nat := 77514583175492619972419

theorem tailTrace_1358632 : CollatzResearch.WordTrace tailWord_1358632 prefixEnd_1358632 77514583175492619972419 := by
  unfold tailWord_1358632
  simp only [CollatzResearch.WordTrace]
  refine ⟨24776690006957887358695075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33035586675943849811593433 24776690006957887358695075)
  ·
    refine ⟨37165035010436831038042613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24776690006957887358695075 37165035010436831038042613)
    ·
      refine ⟨3484222032228452909816495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37165035010436831038042613 3484222032228452909816495)
      ·
        refine ⟨5226333048342679364724743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484222032228452909816495 5226333048342679364724743)
        ·
          refine ⟨7839499572514019047087115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226333048342679364724743 7839499572514019047087115)
          ·
            refine ⟨11759249358771028570630673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7839499572514019047087115 11759249358771028570630673)
            ·
              refine ⟨8819437019078271427973005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759249358771028570630673 8819437019078271427973005)
              ·
                refine ⟨3307288882154351785489877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8819437019078271427973005 3307288882154351785489877)
                ·
                  refine ⟨77514583175492619972419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3307288882154351785489877 77514583175492619972419)
                  ·
                    rfl

theorem cell23_1358632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_1358632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358632 prefixEnd_1358632 := by exact prefixLift 1358632
  have htrace : WordTrace (prefixWord ++ tailWord_1358632) baseStart_1358632 baseEnd_1358632 := by
    simpa [prefixWord, tailWord_1358632, baseEnd_1358632] using wordTrace_append hprefix tailTrace_1358632
  have hstable : (prefixWord ++ tailWord_1358632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358632).length < 2 ^ (prefixWord ++ tailWord_1358632).sum := by decide
  have hdescent : baseEnd_1358632 < baseStart_1358632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358675 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 10]
def baseStart_1358675 : Nat := 118140960795 + 1358675 * 2 ^ 59
def prefixEnd_1358675 : Nat := 4983230072969 + 3 ^ 40 * 1358675 * 2
def baseEnd_1358675 : Nat := 232551109415858970504691

theorem tailTrace_1358675 : CollatzResearch.WordTrace tailWord_1358675 prefixEnd_1358675 232551109415858970504691 := by
  unfold tailWord_1358675
  simp only [CollatzResearch.WordTrace]
  refine ⟨49554948352759993061205479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33036632235173328707470319 49554948352759993061205479)
  ·
    refine ⟨74332422529139989591808219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49554948352759993061205479 74332422529139989591808219)
    ·
      refine ⟨111498633793709984387712329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74332422529139989591808219 111498633793709984387712329)
      ·
        refine ⟨83623975345282488290784247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111498633793709984387712329 83623975345282488290784247)
        ·
          refine ⟨125435963017923732436176371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83623975345282488290784247 125435963017923732436176371)
          ·
            refine ⟨188153944526885598654264557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125435963017923732436176371 188153944526885598654264557)
            ·
              refine ⟨70557729197582099495349209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188153944526885598654264557 70557729197582099495349209)
              ·
                refine ⟨52918296898186574621511907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70557729197582099495349209 52918296898186574621511907)
                ·
                  refine ⟨79377445347279861932267861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52918296898186574621511907 79377445347279861932267861)
                  ·
                    refine ⟨232551109415858970504691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 79377445347279861932267861 232551109415858970504691)
                    ·
                      rfl

theorem cell23_1358675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_1358675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358675 prefixEnd_1358675 := by exact prefixLift 1358675
  have htrace : WordTrace (prefixWord ++ tailWord_1358675) baseStart_1358675 baseEnd_1358675 := by
    simpa [prefixWord, tailWord_1358675, baseEnd_1358675] using wordTrace_append hprefix tailTrace_1358675
  have hstable : (prefixWord ++ tailWord_1358675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358675).length < 2 ^ (prefixWord ++ tailWord_1358675).sum := by decide
  have hdescent : baseEnd_1358675 < baseStart_1358675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358699 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 4, 2]
def baseStart_1358699 : Nat := 118140960795 + 1358699 * 2 ^ 59
def prefixEnd_1358699 : Nat := 4983230072969 + 3 ^ 40 * 1358699 * 2
def baseEnd_1358699 : Nat := 697665651783284817613963

theorem tailTrace_1358699 : CollatzResearch.WordTrace tailWord_1358699 prefixEnd_1358699 697665651783284817613963 := by
  unfold tailWord_1358699
  simp only [CollatzResearch.WordTrace]
  refine ⟨49555823704673045160079151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33037215803115363440052767 49555823704673045160079151)
  ·
    refine ⟨74333735557009567740118727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49555823704673045160079151 74333735557009567740118727)
    ·
      refine ⟨111500603335514351610178091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74333735557009567740118727 111500603335514351610178091)
      ·
        refine ⟨167250905003271527415267137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111500603335514351610178091 167250905003271527415267137)
        ·
          refine ⟨125438178752453645561450353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167250905003271527415267137 125438178752453645561450353)
          ·
            refine ⟨94078634064340234171087765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125438178752453645561450353 94078634064340234171087765)
            ·
              refine ⟨4409935971765948476769739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94078634064340234171087765 4409935971765948476769739)
              ·
                refine ⟨6614903957648922715154609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409935971765948476769739 6614903957648922715154609)
                ·
                  refine ⟨4961177968236692036365957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6614903957648922715154609 4961177968236692036365957)
                  ·
                    refine ⟨930220869044379756818617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961177968236692036365957 930220869044379756818617)
                    ·
                      refine ⟨697665651783284817613963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930220869044379756818617 697665651783284817613963)
                      ·
                        rfl

theorem cell23_1358699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4, 2].length) (baseStart_1358699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358699 prefixEnd_1358699 := by exact prefixLift 1358699
  have htrace : WordTrace (prefixWord ++ tailWord_1358699) baseStart_1358699 baseEnd_1358699 := by
    simpa [prefixWord, tailWord_1358699, baseEnd_1358699] using wordTrace_append hprefix tailTrace_1358699
  have hstable : (prefixWord ++ tailWord_1358699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358699).length < 2 ^ (prefixWord ++ tailWord_1358699).sum := by decide
  have hdescent : baseEnd_1358699 < baseStart_1358699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358743 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 1, 4]
def baseStart_1358743 : Nat := 118140960795 + 1358743 * 2 ^ 59
def prefixEnd_1358743 : Nat := 4983230072969 + 3 ^ 40 * 1358743 * 2
def baseEnd_1358743 : Nat := 232562748310694215154587

theorem tailTrace_1358743 : CollatzResearch.WordTrace tailWord_1358743 prefixEnd_1358743 232562748310694215154587 := by
  unfold tailWord_1358743
  simp only [CollatzResearch.WordTrace]
  refine ⟨49557428516513640674680883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33038285677675760449787255 49557428516513640674680883)
  ·
    refine ⟨74336142774770461012021325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49557428516513640674680883 74336142774770461012021325)
    ·
      refine ⟨27876053540538922879507997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74336142774770461012021325 27876053540538922879507997)
      ·
        refine ⟨10453520077702096079815499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27876053540538922879507997 10453520077702096079815499)
        ·
          refine ⟨15680280116553144119723249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10453520077702096079815499 15680280116553144119723249)
          ·
            refine ⟨11760210087414858089792437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15680280116553144119723249 11760210087414858089792437)
            ·
              refine ⟨1102519695695142945918041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11760210087414858089792437 1102519695695142945918041)
              ·
                refine ⟨826889771771357209438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102519695695142945918041 826889771771357209438531)
                ·
                  refine ⟨1240334657657035814157797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826889771771357209438531 1240334657657035814157797)
                  ·
                    refine ⟨232562748310694215154587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240334657657035814157797 232562748310694215154587)
                    ·
                      rfl

theorem cell23_1358743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_1358743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358743 prefixEnd_1358743 := by exact prefixLift 1358743
  have htrace : WordTrace (prefixWord ++ tailWord_1358743) baseStart_1358743 baseEnd_1358743 := by
    simpa [prefixWord, tailWord_1358743, baseEnd_1358743] using wordTrace_append hprefix tailTrace_1358743
  have hstable : (prefixWord ++ tailWord_1358743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358743).length < 2 ^ (prefixWord ++ tailWord_1358743).sum := by decide
  have hdescent : baseEnd_1358743 < baseStart_1358743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358776 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_1358776 : Nat := 118140960795 + 1358776 * 2 ^ 59
def prefixEnd_1358776 : Nat := 4983230072969 + 3 ^ 40 * 1358776 * 2
def baseEnd_1358776 : Nat := 697705189793681016351109

theorem tailTrace_1358776 : CollatzResearch.WordTrace tailWord_1358776 prefixEnd_1358776 697705189793681016351109 := by
  unfold tailWord_1358776
  simp only [CollatzResearch.WordTrace]
  refine ⟨24779316062697043655316091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33039088083596058207088121 24779316062697043655316091)
  ·
    refine ⟨37168974094045565482974137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24779316062697043655316091 37168974094045565482974137)
    ·
      refine ⟨27876730570534174112230603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37168974094045565482974137 27876730570534174112230603)
      ·
        refine ⟨41815095855801261168345905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27876730570534174112230603 41815095855801261168345905)
        ·
          refine ⟨31361321891850945876259429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41815095855801261168345905 31361321891850945876259429)
          ·
            refine ⟨5880247854722052351798643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31361321891850945876259429 5880247854722052351798643)
            ·
              refine ⟨8820371782083078527697965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880247854722052351798643 8820371782083078527697965)
              ·
                refine ⟨3307639418281154447886737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8820371782083078527697965 3307639418281154447886737)
                ·
                  refine ⟨2480729563710865835915053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307639418281154447886737 2480729563710865835915053)
                  ·
                    refine ⟨930273586391574688468145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480729563710865835915053 930273586391574688468145)
                    ·
                      refine ⟨697705189793681016351109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930273586391574688468145 697705189793681016351109)
                      ·
                        rfl

theorem cell23_1358776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_1358776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358776 prefixEnd_1358776 := by exact prefixLift 1358776
  have htrace : WordTrace (prefixWord ++ tailWord_1358776) baseStart_1358776 baseEnd_1358776 := by
    simpa [prefixWord, tailWord_1358776, baseEnd_1358776] using wordTrace_append hprefix tailTrace_1358776
  have hstable : (prefixWord ++ tailWord_1358776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358776).length < 2 ^ (prefixWord ++ tailWord_1358776).sum := by decide
  have hdescent : baseEnd_1358776 < baseStart_1358776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358789 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_1358789 : Nat := 118140960795 + 1358789 * 2 ^ 59
def prefixEnd_1358789 : Nat := 4983230072969 + 3 ^ 40 * 1358789 * 2
def baseEnd_1358789 : Nat := 697711865042189465488549

theorem tailTrace_1358789 : CollatzResearch.WordTrace tailWord_1358789 prefixEnd_1358789 697711865042189465488549 := by
  unfold tailWord_1358789
  simp only [CollatzResearch.WordTrace]
  refine ⟨49559106274346990530855421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33039404182897993687236947 49559106274346990530855421)
  ·
    refine ⟨18584664852880121449070783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49559106274346990530855421 18584664852880121449070783)
    ·
      refine ⟨27876997279320182173606175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18584664852880121449070783 27876997279320182173606175)
      ·
        refine ⟨41815495918980273260409263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27876997279320182173606175 41815495918980273260409263)
        ·
          refine ⟨62723243878470409890613895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41815495918980273260409263 62723243878470409890613895)
          ·
            refine ⟨94084865817705614835920843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62723243878470409890613895 94084865817705614835920843)
            ·
              refine ⟨141127298726558422253881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94084865817705614835920843 141127298726558422253881265)
              ·
                refine ⟨105845474044918816690410949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141127298726558422253881265 105845474044918816690410949)
                ·
                  refine ⟨19846026383422278129452053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105845474044918816690410949 19846026383422278129452053)
                  ·
                    refine ⟨930282486722919287318065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19846026383422278129452053 930282486722919287318065)
                    ·
                      refine ⟨697711865042189465488549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930282486722919287318065 697711865042189465488549)
                      ·
                        rfl

theorem cell23_1358789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_1358789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358789 prefixEnd_1358789 := by exact prefixLift 1358789
  have htrace : WordTrace (prefixWord ++ tailWord_1358789) baseStart_1358789 baseEnd_1358789 := by
    simpa [prefixWord, tailWord_1358789, baseEnd_1358789] using wordTrace_append hprefix tailTrace_1358789
  have hstable : (prefixWord ++ tailWord_1358789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358789).length < 2 ^ (prefixWord ++ tailWord_1358789).sum := by decide
  have hdescent : baseEnd_1358789 < baseStart_1358789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358823 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1358823 : Nat := 118140960795 + 1358823 * 2 ^ 59
def prefixEnd_1358823 : Nat := 4983230072969 + 3 ^ 40 * 1358823 * 2
def baseEnd_1358823 : Nat := 697729323384442332463393

theorem tailTrace_1358823 : CollatzResearch.WordTrace tailWord_1358823 prefixEnd_1358823 697729323384442332463393 := by
  unfold tailWord_1358823
  simp only [CollatzResearch.WordTrace]
  refine ⟨49560346356223814337593123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33040230904149209558395415 49560346356223814337593123)
  ·
    refine ⟨74340519534335721506389685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49560346356223814337593123 74340519534335721506389685)
    ·
      refine ⟨6969423706343973891224033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74340519534335721506389685 6969423706343973891224033)
      ·
        refine ⟨5227067779757980418418025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969423706343973891224033 5227067779757980418418025)
        ·
          refine ⟨3920300834818485313813519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227067779757980418418025 3920300834818485313813519)
          ·
            refine ⟨5880451252227727970720279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920300834818485313813519 5880451252227727970720279)
            ·
              refine ⟨8820676878341591956080419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880451252227727970720279 8820676878341591956080419)
              ·
                refine ⟨13231015317512387934120629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8820676878341591956080419 13231015317512387934120629)
                ·
                  refine ⟨1240407686016786368823809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13231015317512387934120629 1240407686016786368823809)
                  ·
                    refine ⟨930305764512589776617857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240407686016786368823809 930305764512589776617857)
                    ·
                      refine ⟨697729323384442332463393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930305764512589776617857 697729323384442332463393)
                      ·
                        rfl

theorem cell23_1358823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1358823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358823 prefixEnd_1358823 := by exact prefixLift 1358823
  have htrace : WordTrace (prefixWord ++ tailWord_1358823) baseStart_1358823 baseEnd_1358823 := by
    simpa [prefixWord, tailWord_1358823, baseEnd_1358823] using wordTrace_append hprefix tailTrace_1358823
  have hstable : (prefixWord ++ tailWord_1358823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358823).length < 2 ^ (prefixWord ++ tailWord_1358823).sum := by decide
  have hdescent : baseEnd_1358823 < baseStart_1358823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358826 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1358826 : Nat := 118140960795 + 1358826 * 2 ^ 59
def prefixEnd_1358826 : Nat := 4983230072969 + 3 ^ 40 * 1358826 * 2
def baseEnd_1358826 : Nat := 697730863826405820725879

theorem tailTrace_1358826 : CollatzResearch.WordTrace tailWord_1358826 prefixEnd_1358826 697730863826405820725879 := by
  unfold tailWord_1358826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390113943803236462488083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33040303850141963899968221 12390113943803236462488083)
  ·
    refine ⟨18585170915704854693732125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12390113943803236462488083 18585170915704854693732125)
    ·
      refine ⟨6969439093389320510149547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18585170915704854693732125 6969439093389320510149547)
      ·
        refine ⟨10454158640083980765224321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6969439093389320510149547 10454158640083980765224321)
        ·
          refine ⟨7840618980062985573918241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10454158640083980765224321 7840618980062985573918241)
          ·
            refine ⟨5880464235047239180438681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7840618980062985573918241 5880464235047239180438681)
            ·
              refine ⟨4410348176285429385329011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5880464235047239180438681 4410348176285429385329011)
              ·
                refine ⟨6615522264428144077993517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410348176285429385329011 6615522264428144077993517)
                ·
                  refine ⟨2480820849160554029247569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6615522264428144077993517 2480820849160554029247569)
                  ·
                    refine ⟨1860615636870415521935677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2480820849160554029247569 1860615636870415521935677)
                    ·
                      refine ⟨697730863826405820725879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860615636870415521935677 697730863826405820725879)
                      ·
                        rfl

theorem cell23_1358826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1358826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358826 prefixEnd_1358826 := by exact prefixLift 1358826
  have htrace : WordTrace (prefixWord ++ tailWord_1358826) baseStart_1358826 baseEnd_1358826 := by
    simpa [prefixWord, tailWord_1358826, baseEnd_1358826] using wordTrace_append hprefix tailTrace_1358826
  have hstable : (prefixWord ++ tailWord_1358826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358826).length < 2 ^ (prefixWord ++ tailWord_1358826).sum := by decide
  have hdescent : baseEnd_1358826 < baseStart_1358826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358837 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1358837 : Nat := 118140960795 + 1358837 * 2 ^ 59
def prefixEnd_1358837 : Nat := 4983230072969 + 3 ^ 40 * 1358837 * 2
def baseEnd_1358837 : Nat := 232578837371201759229443

theorem tailTrace_1358837 : CollatzResearch.WordTrace tailWord_1358837 prefixEnd_1358837 232578837371201759229443 := by
  unfold tailWord_1358837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49560856978173094728602765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33040571318782063152401843 49560856978173094728602765)
  ·
    refine ⟨18585321366814910523226037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49560856978173094728602765 18585321366814910523226037)
    ·
      refine ⟨1742373878138897861552441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18585321366814910523226037 1742373878138897861552441)
      ·
        refine ⟨1306780408604173396164331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742373878138897861552441 1306780408604173396164331)
        ·
          refine ⟨1960170612906260094246497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306780408604173396164331 1960170612906260094246497)
          ·
            refine ⟨1470127959679695070684873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960170612906260094246497 1470127959679695070684873)
            ·
              refine ⟨1102595969759771303013655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470127959679695070684873 1102595969759771303013655)
              ·
                refine ⟨1653893954639656954520483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102595969759771303013655 1653893954639656954520483)
                ·
                  refine ⟨2480840931959485431780725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653893954639656954520483 2480840931959485431780725)
                  ·
                    refine ⟨232578837371201759229443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2480840931959485431780725 232578837371201759229443)
                    ·
                      rfl

theorem cell23_1358837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1358837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358837 prefixEnd_1358837 := by exact prefixLift 1358837
  have htrace : WordTrace (prefixWord ++ tailWord_1358837) baseStart_1358837 baseEnd_1358837 := by
    simpa [prefixWord, tailWord_1358837, baseEnd_1358837] using wordTrace_append hprefix tailTrace_1358837
  have hstable : (prefixWord ++ tailWord_1358837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358837).length < 2 ^ (prefixWord ++ tailWord_1358837).sum := by decide
  have hdescent : baseEnd_1358837 < baseStart_1358837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358846 : List Nat := [4, 2, 2, 2, 2, 1, 10]
def baseStart_1358846 : Nat := 118140960795 + 1358846 * 2 ^ 59
def prefixEnd_1358846 : Nat := 4983230072969 + 3 ^ 40 * 1358846 * 2
def baseEnd_1358846 : Nat := 8614088067154268425627

theorem tailTrace_1358846 : CollatzResearch.WordTrace tailWord_1358846 prefixEnd_1358846 8614088067154268425627 := by
  unfold tailWord_1358846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195148154392561158210049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33040790156760326177120261 6195148154392561158210049)
  ·
    refine ⟨4646361115794420868657537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6195148154392561158210049 4646361115794420868657537)
    ·
      refine ⟨3484770836845815651493153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646361115794420868657537 3484770836845815651493153)
      ·
        refine ⟨2613578127634361738619865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484770836845815651493153 2613578127634361738619865)
        ·
          refine ⟨1960183595725771303964899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613578127634361738619865 1960183595725771303964899)
          ·
            refine ⟨2940275393588656955947349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960183595725771303964899 2940275393588656955947349)
            ·
              refine ⟨8614088067154268425627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2940275393588656955947349 8614088067154268425627)
              ·
                rfl

theorem cell23_1358846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 10].length) (baseStart_1358846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358846 prefixEnd_1358846 := by exact prefixLift 1358846
  have htrace : WordTrace (prefixWord ++ tailWord_1358846) baseStart_1358846 baseEnd_1358846 := by
    simpa [prefixWord, tailWord_1358846, baseEnd_1358846] using wordTrace_append hprefix tailTrace_1358846
  have hstable : (prefixWord ++ tailWord_1358846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358846).length < 2 ^ (prefixWord ++ tailWord_1358846).sum := by decide
  have hdescent : baseEnd_1358846 < baseStart_1358846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358850 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1358850 : Nat := 118140960795 + 1358850 * 2 ^ 59
def prefixEnd_1358850 : Nat := 4983230072969 + 3 ^ 40 * 1358850 * 2
def baseEnd_1358850 : Nat := 232581062454037908941923

theorem tailTrace_1358850 : CollatzResearch.WordTrace tailWord_1358850 prefixEnd_1358850 232581062454037908941923 := by
  unfold tailWord_1358850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390332781781499487206501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33040887418083998632550669 12390332781781499487206501)
  ·
    refine ⟨2323187396584031153851219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12390332781781499487206501 2323187396584031153851219)
    ·
      refine ⟨3484781094876046730776829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323187396584031153851219 3484781094876046730776829)
      ·
        refine ⟨1306792910578517524041311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3484781094876046730776829 1306792910578517524041311)
        ·
          refine ⟨1960189365867776286061967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306792910578517524041311 1960189365867776286061967)
          ·
            refine ⟨2940284048801664429092951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960189365867776286061967 2940284048801664429092951)
            ·
              refine ⟨4410426073202496643639427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940284048801664429092951 4410426073202496643639427)
              ·
                refine ⟨6615639109803744965459141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410426073202496643639427 6615639109803744965459141)
                ·
                  refine ⟨1240432333088202181023589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6615639109803744965459141 1240432333088202181023589)
                  ·
                    refine ⟨232581062454037908941923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240432333088202181023589 232581062454037908941923)
                    ·
                      rfl

theorem cell23_1358850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1358850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358850 prefixEnd_1358850 := by exact prefixLift 1358850
  have htrace : WordTrace (prefixWord ++ tailWord_1358850) baseStart_1358850 baseEnd_1358850 := by
    simpa [prefixWord, tailWord_1358850, baseEnd_1358850] using wordTrace_append hprefix tailTrace_1358850
  have hstable : (prefixWord ++ tailWord_1358850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358850).length < 2 ^ (prefixWord ++ tailWord_1358850).sum := by decide
  have hdescent : baseEnd_1358850 < baseStart_1358850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358880 : List Nat := [2, 1, 1, 7, 2, 1, 2, 7]
def baseStart_1358880 : Nat := 118140960795 + 1358880 * 2 ^ 59
def prefixEnd_1358880 : Nat := 4983230072969 + 3 ^ 40 * 1358880 * 2
def baseEnd_1358880 : Nat := 25842910806731429979653

theorem tailTrace_1358880 : CollatzResearch.WordTrace tailWord_1358880 prefixEnd_1358880 25842910806731429979653 := by
  unfold tailWord_1358880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781212658508656536209047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33041616878011542048278729 24781212658508656536209047)
  ·
    refine ⟨37171818987762984804313571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781212658508656536209047 37171818987762984804313571)
    ·
      refine ⟨55757728481644477206470357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37171818987762984804313571 55757728481644477206470357)
      ·
        refine ⟨1306821761288542434526649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 55757728481644477206470357 1306821761288542434526649)
        ·
          refine ⟨980116320966406825894987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306821761288542434526649 980116320966406825894987)
          ·
            refine ⟨1470174481449610238842481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980116320966406825894987 1470174481449610238842481)
            ·
              refine ⟨1102630861087207679131861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470174481449610238842481 1102630861087207679131861)
              ·
                refine ⟨25842910806731429979653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1102630861087207679131861 25842910806731429979653)
                ·
                  rfl

theorem cell23_1358880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 7].length) (baseStart_1358880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358880 prefixEnd_1358880 := by exact prefixLift 1358880
  have htrace : WordTrace (prefixWord ++ tailWord_1358880) baseStart_1358880 baseEnd_1358880 := by
    simpa [prefixWord, tailWord_1358880, baseEnd_1358880] using wordTrace_append hprefix tailTrace_1358880
  have hstable : (prefixWord ++ tailWord_1358880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358880).length < 2 ^ (prefixWord ++ tailWord_1358880).sum := by decide
  have hdescent : baseEnd_1358880 < baseStart_1358880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358883 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 1, 3, 2]
def baseStart_1358883 : Nat := 118140960795 + 1358883 * 2 ^ 59
def prefixEnd_1358883 : Nat := 4983230072969 + 3 ^ 40 * 1358883 * 2
def baseEnd_1358883 : Nat := 697760132223712097713117

theorem tailTrace_1358883 : CollatzResearch.WordTrace tailWord_1358883 prefixEnd_1358883 697760132223712097713117 := by
  unfold tailWord_1358883
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562534736006444584777303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33041689824004296389851535 49562534736006444584777303)
  ·
    refine ⟨74343802104009666877165955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49562534736006444584777303 74343802104009666877165955)
    ·
      refine ⟨111515703156014500315748933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74343802104009666877165955 111515703156014500315748933)
      ·
        refine ⟨20909194341752718809202925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111515703156014500315748933 20909194341752718809202925)
        ·
          refine ⟨7840947878157269553451097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20909194341752718809202925 7840947878157269553451097)
          ·
            refine ⟨5880710908617952165088323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7840947878157269553451097 5880710908617952165088323)
            ·
              refine ⟨8821066362926928247632485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880710908617952165088323 8821066362926928247632485)
              ·
                refine ⟨1653949943048799046431091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8821066362926928247632485 1653949943048799046431091)
                ·
                  refine ⟨2480924914573198569646637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653949943048799046431091 2480924914573198569646637)
                  ·
                    refine ⟨930346842964949463617489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480924914573198569646637 930346842964949463617489)
                    ·
                      refine ⟨697760132223712097713117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930346842964949463617489 697760132223712097713117)
                      ·
                        rfl

theorem cell23_1358883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_1358883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358883 prefixEnd_1358883 := by exact prefixLift 1358883
  have htrace : WordTrace (prefixWord ++ tailWord_1358883) baseStart_1358883 baseEnd_1358883 := by
    simpa [prefixWord, tailWord_1358883, baseEnd_1358883] using wordTrace_append hprefix tailTrace_1358883
  have hstable : (prefixWord ++ tailWord_1358883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358883).length < 2 ^ (prefixWord ++ tailWord_1358883).sum := by decide
  have hdescent : baseEnd_1358883 < baseStart_1358883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358896 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2]
def baseStart_1358896 : Nat := 118140960795 + 1358896 * 2 ^ 59
def prefixEnd_1358896 : Nat := 4983230072969 + 3 ^ 40 * 1358896 * 2
def baseEnd_1358896 : Nat := 697766807472220546850557

theorem tailTrace_1358896 : CollatzResearch.WordTrace tailWord_1358896 prefixEnd_1358896 697766807472220546850557 := by
  unfold tailWord_1358896
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781504442479673902500271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33042005923306231870000361 24781504442479673902500271)
  ·
    refine ⟨37172256663719510853750407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781504442479673902500271 37172256663719510853750407)
    ·
      refine ⟨55758384995579266280625611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37172256663719510853750407 55758384995579266280625611)
      ·
        refine ⟨83637577493368899420938417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55758384995579266280625611 83637577493368899420938417)
        ·
          refine ⟨62728183120026674565703813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83637577493368899420938417 62728183120026674565703813)
          ·
            refine ⟨11761534335005001481069465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62728183120026674565703813 11761534335005001481069465)
            ·
              refine ⟨8821150751253751110802099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11761534335005001481069465 8821150751253751110802099)
              ·
                refine ⟨13231726126880626666203149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821150751253751110802099 13231726126880626666203149)
                ·
                  refine ⟨4961897297580234999826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13231726126880626666203149 4961897297580234999826181)
                  ·
                    refine ⟨930355743296294062467409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961897297580234999826181 930355743296294062467409)
                    ·
                      refine ⟨697766807472220546850557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930355743296294062467409 697766807472220546850557)
                      ·
                        rfl

theorem cell23_1358896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 4, 2].length) (baseStart_1358896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358896 prefixEnd_1358896 := by exact prefixLift 1358896
  have htrace : WordTrace (prefixWord ++ tailWord_1358896) baseStart_1358896 baseEnd_1358896 := by
    simpa [prefixWord, tailWord_1358896, baseEnd_1358896] using wordTrace_append hprefix tailTrace_1358896
  have hstable : (prefixWord ++ tailWord_1358896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358896).length < 2 ^ (prefixWord ++ tailWord_1358896).sum := by decide
  have hdescent : baseEnd_1358896 < baseStart_1358896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358899 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3]
def baseStart_1358899 : Nat := 118140960795 + 1358899 * 2 ^ 59
def prefixEnd_1358899 : Nat := 4983230072969 + 3 ^ 40 * 1358899 * 2
def baseEnd_1358899 : Nat := 697768347914184035113043

theorem tailTrace_1358899 : CollatzResearch.WordTrace tailWord_1358899 prefixEnd_1358899 697768347914184035113043 := by
  unfold tailWord_1358899
  simp only [CollatzResearch.WordTrace]
  refine ⟨49563118303948479317359751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33042078869298986211573167 49563118303948479317359751)
  ·
    refine ⟨74344677455922718976039627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49563118303948479317359751 74344677455922718976039627)
    ·
      refine ⟨111517016183884078464059441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74344677455922718976039627 111517016183884078464059441)
      ·
        refine ⟨83637762137913058848044581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111517016183884078464059441 83637762137913058848044581)
        ·
          refine ⟨15682080400858698534008359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83637762137913058848044581 15682080400858698534008359)
          ·
            refine ⟨23523120601288047801012539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15682080400858698534008359 23523120601288047801012539)
            ·
              refine ⟨35284680901932071701518809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23523120601288047801012539 35284680901932071701518809)
              ·
                refine ⟨26463510676449053776139107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35284680901932071701518809 26463510676449053776139107)
                ·
                  refine ⟨39695266014673580664208661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26463510676449053776139107 39695266014673580664208661)
                  ·
                    refine ⟨1860715594437824093634781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39695266014673580664208661 1860715594437824093634781)
                    ·
                      refine ⟨697768347914184035113043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860715594437824093634781 697768347914184035113043)
                      ·
                        rfl

theorem cell23_1358899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_1358899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358899 prefixEnd_1358899 := by exact prefixLift 1358899
  have htrace : WordTrace (prefixWord ++ tailWord_1358899) baseStart_1358899 baseEnd_1358899 := by
    simpa [prefixWord, tailWord_1358899, baseEnd_1358899] using wordTrace_append hprefix tailTrace_1358899
  have hstable : (prefixWord ++ tailWord_1358899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358899).length < 2 ^ (prefixWord ++ tailWord_1358899).sum := by decide
  have hdescent : baseEnd_1358899 < baseStart_1358899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358959 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_1358959 : Nat := 118140960795 + 1358959 * 2 ^ 59
def prefixEnd_1358959 : Nat := 4983230072969 + 3 ^ 40 * 1358959 * 2
def baseEnd_1358959 : Nat := 697799156753453800362767

theorem tailTrace_1358959 : CollatzResearch.WordTrace tailWord_1358959 prefixEnd_1358959 697799156753453800362767 := by
  unfold tailWord_1358959
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565306683731109564543931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33043537789154073043029287 49565306683731109564543931)
  ·
    refine ⟨74347960025596664346815897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49565306683731109564543931 74347960025596664346815897)
    ·
      refine ⟨55760970019197498260111923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74347960025596664346815897 55760970019197498260111923)
      ·
        refine ⟨83641455028796247390167885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55760970019197498260111923 83641455028796247390167885)
        ·
          refine ⟨31365545635798592771312957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83641455028796247390167885 31365545635798592771312957)
          ·
            refine ⟨11762079613424472289242359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31365545635798592771312957 11762079613424472289242359)
            ·
              refine ⟨17643119420136708433863539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11762079613424472289242359 17643119420136708433863539)
              ·
                refine ⟨26464679130205062650795309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17643119420136708433863539 26464679130205062650795309)
                ·
                  refine ⟨9924254673826898494048241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26464679130205062650795309 9924254673826898494048241)
                  ·
                    refine ⟨7443191005370173870536181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9924254673826898494048241 7443191005370173870536181)
                    ·
                      refine ⟨697799156753453800362767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7443191005370173870536181 697799156753453800362767)
                      ·
                        rfl

theorem cell23_1358959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_1358959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358959 prefixEnd_1358959 := by exact prefixLift 1358959
  have htrace : WordTrace (prefixWord ++ tailWord_1358959) baseStart_1358959 baseEnd_1358959 := by
    simpa [prefixWord, tailWord_1358959, baseEnd_1358959] using wordTrace_append hprefix tailTrace_1358959
  have hstable : (prefixWord ++ tailWord_1358959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358959).length < 2 ^ (prefixWord ++ tailWord_1358959).sum := by decide
  have hdescent : baseEnd_1358959 < baseStart_1358959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358986 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1358986 : Nat := 118140960795 + 1358986 * 2 ^ 59
def prefixEnd_1358986 : Nat := 4983230072969 + 3 ^ 40 * 1358986 * 2
def baseEnd_1358986 : Nat := 697813020731125194725143

theorem tailTrace_1358986 : CollatzResearch.WordTrace tailWord_1358986 prefixEnd_1358986 697813020731125194725143 := by
  unfold tailWord_1358986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391572863658323293944203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33044194303088862117184541 12391572863658323293944203)
  ·
    refine ⟨18587359295487484940916305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12391572863658323293944203 18587359295487484940916305)
    ·
      refine ⟨13940519471615613705687229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18587359295487484940916305 13940519471615613705687229)
      ·
        refine ⟨5227694801855855139632711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13940519471615613705687229 5227694801855855139632711)
        ·
          refine ⟨7841542202783782709449067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227694801855855139632711 7841542202783782709449067)
          ·
            refine ⟨11762313304175674064173601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841542202783782709449067 11762313304175674064173601)
            ·
              refine ⟨8821734978131755548130201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11762313304175674064173601 8821734978131755548130201)
              ·
                refine ⟨6616301233598816661097651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8821734978131755548130201 6616301233598816661097651)
                ·
                  refine ⟨9924451850398224991646477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616301233598816661097651 9924451850398224991646477)
                  ·
                    refine ⟨3721669443899334371867429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9924451850398224991646477 3721669443899334371867429)
                    ·
                      refine ⟨697813020731125194725143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3721669443899334371867429 697813020731125194725143)
                      ·
                        rfl

theorem cell23_1358986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1358986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1358986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1358986 prefixEnd_1358986 := by exact prefixLift 1358986
  have htrace : WordTrace (prefixWord ++ tailWord_1358986) baseStart_1358986 baseEnd_1358986 := by
    simpa [prefixWord, tailWord_1358986, baseEnd_1358986] using wordTrace_append hprefix tailTrace_1358986
  have hstable : (prefixWord ++ tailWord_1358986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358986).length < 2 ^ (prefixWord ++ tailWord_1358986).sum := by decide
  have hdescent : baseEnd_1358986 < baseStart_1358986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359026 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_1359026 : Nat := 118140960795 + 1359026 * 2 ^ 59
def prefixEnd_1359026 : Nat := 4983230072969 + 3 ^ 40 * 1359026 * 2
def baseEnd_1359026 : Nat := 77537062217478337580551

theorem tailTrace_1359026 : CollatzResearch.WordTrace tailWord_1359026 prefixEnd_1359026 77537062217478337580551 := by
  unfold tailWord_1359026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391937593622095001808233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33045166916325586671488621 12391937593622095001808233)
  ·
    refine ⟨9293953195216571251356175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12391937593622095001808233 9293953195216571251356175)
    ·
      refine ⟨13940929792824856877034263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9293953195216571251356175 13940929792824856877034263)
      ·
        refine ⟨20911394689237285315551395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940929792824856877034263 20911394689237285315551395)
        ·
          refine ⟨31367092033855927973327093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20911394689237285315551395 31367092033855927973327093)
          ·
            refine ⟨2940664878173993247499415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31367092033855927973327093 2940664878173993247499415)
            ·
              refine ⟨4410997317260989871249123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940664878173993247499415 4410997317260989871249123)
              ·
                refine ⟨6616495975891484806873685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410997317260989871249123 6616495975891484806873685)
                ·
                  refine ⟨77537062217478337580551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6616495975891484806873685 77537062217478337580551)
                  ·
                    rfl

theorem cell23_1359026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_1359026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359026 prefixEnd_1359026 := by exact prefixLift 1359026
  have htrace : WordTrace (prefixWord ++ tailWord_1359026) baseStart_1359026 baseEnd_1359026 := by
    simpa [prefixWord, tailWord_1359026, baseEnd_1359026] using wordTrace_append hprefix tailTrace_1359026
  have hstable : (prefixWord ++ tailWord_1359026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359026).length < 2 ^ (prefixWord ++ tailWord_1359026).sum := by decide
  have hdescent : baseEnd_1359026 < baseStart_1359026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359063 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_1359063 : Nat := 118140960795 + 1359063 * 2 ^ 59
def prefixEnd_1359063 : Nat := 4983230072969 + 3 ^ 40 * 1359063 * 2
def baseEnd_1359063 : Nat := 697852558741521393462289

theorem tailTrace_1359063 : CollatzResearch.WordTrace tailWord_1359063 prefixEnd_1359063 697852558741521393462289 := by
  unfold tailWord_1359063
  simp only [CollatzResearch.WordTrace]
  refine ⟨49569099875354335326329843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33046066583569556884219895 49569099875354335326329843)
  ·
    refine ⟨74353649813031502989494765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49569099875354335326329843 74353649813031502989494765)
    ·
      refine ⟨27882618679886813621060537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74353649813031502989494765 27882618679886813621060537)
      ·
        refine ⟨20911964009915110215795403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27882618679886813621060537 20911964009915110215795403)
        ·
          refine ⟨31367946014872665323693105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20911964009915110215795403 31367946014872665323693105)
          ·
            refine ⟨23525959511154498992769829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31367946014872665323693105 23525959511154498992769829)
            ·
              refine ⟨4411117408341468561144343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23525959511154498992769829 4411117408341468561144343)
              ·
                refine ⟨6616676112512202841716515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411117408341468561144343 6616676112512202841716515)
                ·
                  refine ⟨9925014168768304262574773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616676112512202841716515 9925014168768304262574773)
                  ·
                    refine ⟨930470078322028524616385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9925014168768304262574773 930470078322028524616385)
                    ·
                      refine ⟨697852558741521393462289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930470078322028524616385 697852558741521393462289)
                      ·
                        rfl

theorem cell23_1359063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_1359063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359063 prefixEnd_1359063 := by exact prefixLift 1359063
  have htrace : WordTrace (prefixWord ++ tailWord_1359063) baseStart_1359063 baseEnd_1359063 := by
    simpa [prefixWord, tailWord_1359063, baseEnd_1359063] using wordTrace_append hprefix tailTrace_1359063
  have hstable : (prefixWord ++ tailWord_1359063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359063).length < 2 ^ (prefixWord ++ tailWord_1359063).sum := by decide
  have hdescent : baseEnd_1359063 < baseStart_1359063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359064 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 1, 4]
def baseStart_1359064 : Nat := 118140960795 + 1359064 * 2 ^ 59
def prefixEnd_1359064 : Nat := 4983230072969 + 3 ^ 40 * 1359064 * 2
def baseEnd_1359064 : Nat := 232617690740725296516595

theorem tailTrace_1359064 : CollatzResearch.WordTrace tailWord_1359064 prefixEnd_1359064 232617690740725296516595 := by
  unfold tailWord_1359064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24784568174175356248558123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33046090898900474998077497 24784568174175356248558123)
  ·
    refine ⟨37176852261263034372837185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24784568174175356248558123 37176852261263034372837185)
    ·
      refine ⟨27882639195947275779627889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37176852261263034372837185 27882639195947275779627889)
      ·
        refine ⟨20911979396960456834720917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27882639195947275779627889 20911979396960456834720917)
        ·
          refine ⟨980249034232521414127543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20911979396960456834720917 980249034232521414127543)
          ·
            refine ⟨1470373551348782121191315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980249034232521414127543 1470373551348782121191315)
            ·
              refine ⟨2205560327023173181786973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470373551348782121191315 2205560327023173181786973)
              ·
                refine ⟨827085122633689943170115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205560327023173181786973 827085122633689943170115)
                ·
                  refine ⟨1240627683950534914755173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827085122633689943170115 1240627683950534914755173)
                  ·
                    refine ⟨232617690740725296516595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1240627683950534914755173 232617690740725296516595)
                    ·
                      rfl

theorem cell23_1359064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_1359064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359064 prefixEnd_1359064 := by exact prefixLift 1359064
  have htrace : WordTrace (prefixWord ++ tailWord_1359064) baseStart_1359064 baseEnd_1359064 := by
    simpa [prefixWord, tailWord_1359064, baseEnd_1359064] using wordTrace_append hprefix tailTrace_1359064
  have hstable : (prefixWord ++ tailWord_1359064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359064).length < 2 ^ (prefixWord ++ tailWord_1359064).sum := by decide
  have hdescent : baseEnd_1359064 < baseStart_1359064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359073 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1359073 : Nat := 118140960795 + 1359073 * 2 ^ 59
def prefixEnd_1359073 : Nat := 4983230072969 + 3 ^ 40 * 1359073 * 2
def baseEnd_1359073 : Nat := 232619231182688784779081

theorem tailTrace_1359073 : CollatzResearch.WordTrace tailWord_1359073 prefixEnd_1359073 232619231182688784779081 := by
  unfold tailWord_1359073
  simp only [CollatzResearch.WordTrace]
  refine ⟨49569464605318107034193873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33046309736878738022795915 49569464605318107034193873)
  ·
    refine ⟨37177098453988580275645405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49569464605318107034193873 37177098453988580275645405)
    ·
      refine ⟨13941411920245717603367027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37177098453988580275645405 13941411920245717603367027)
      ·
        refine ⟨20912117880368576405050541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13941411920245717603367027 20912117880368576405050541)
        ·
          refine ⟨7842044205138216151893953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20912117880368576405050541 7842044205138216151893953)
          ·
            refine ⟨5881533153853662113920465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7842044205138216151893953 5881533153853662113920465)
            ·
              refine ⟨4411149865390246585440349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881533153853662113920465 4411149865390246585440349)
              ·
                refine ⟨1654181199521342469540131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4411149865390246585440349 1654181199521342469540131)
                ·
                  refine ⟨2481271799282013704310197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654181199521342469540131 2481271799282013704310197)
                  ·
                    refine ⟨232619231182688784779081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2481271799282013704310197 232619231182688784779081)
                    ·
                      rfl

theorem cell23_1359073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1359073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359073 prefixEnd_1359073 := by exact prefixLift 1359073
  have htrace : WordTrace (prefixWord ++ tailWord_1359073) baseStart_1359073 baseEnd_1359073 := by
    simpa [prefixWord, tailWord_1359073, baseEnd_1359073] using wordTrace_append hprefix tailTrace_1359073
  have hstable : (prefixWord ++ tailWord_1359073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359073).length < 2 ^ (prefixWord ++ tailWord_1359073).sum := by decide
  have hdescent : baseEnd_1359073 < baseStart_1359073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359080 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1359080 : Nat := 118140960795 + 1359080 * 2 ^ 59
def prefixEnd_1359080 : Nat := 4983230072969 + 3 ^ 40 * 1359080 * 2
def baseEnd_1359080 : Nat := 697861287912647826949711

theorem tailTrace_1359080 : CollatzResearch.WordTrace tailWord_1359080 prefixEnd_1359080 697861287912647826949711 := by
  unfold tailWord_1359080
  simp only [CollatzResearch.WordTrace]
  refine ⟨24784859958146373614849347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33046479944195164819799129 24784859958146373614849347)
  ·
    refine ⟨37177289937219560422274021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24784859958146373614849347 37177289937219560422274021)
    ·
      refine ⟨6970741863228667579176379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37177289937219560422274021 6970741863228667579176379)
      ·
        refine ⟨10456112794843001368764569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6970741863228667579176379 10456112794843001368764569)
        ·
          refine ⟨7842084596132251026573427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10456112794843001368764569 7842084596132251026573427)
          ·
            refine ⟨11763126894198376539860141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842084596132251026573427 11763126894198376539860141)
            ·
              refine ⟨4411172585324391202447553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11763126894198376539860141 4411172585324391202447553)
              ·
                refine ⟨3308379438993293401835665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411172585324391202447553 3308379438993293401835665)
                ·
                  refine ⟨2481284579244970051376749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308379438993293401835665 2481284579244970051376749)
                  ·
                    refine ⟨930481717216863769266281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481284579244970051376749 930481717216863769266281)
                    ·
                      refine ⟨697861287912647826949711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930481717216863769266281 697861287912647826949711)
                      ·
                        rfl

theorem cell23_1359080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1359080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359080 prefixEnd_1359080 := by exact prefixLift 1359080
  have htrace : WordTrace (prefixWord ++ tailWord_1359080) baseStart_1359080 baseEnd_1359080 := by
    simpa [prefixWord, tailWord_1359080, baseEnd_1359080] using wordTrace_append hprefix tailTrace_1359080
  have hstable : (prefixWord ++ tailWord_1359080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359080).length < 2 ^ (prefixWord ++ tailWord_1359080).sum := by decide
  have hdescent : baseEnd_1359080 < baseStart_1359080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359087 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_1359087 : Nat := 118140960795 + 1359087 * 2 ^ 59
def prefixEnd_1359087 : Nat := 4983230072969 + 3 ^ 40 * 1359087 * 2
def baseEnd_1359087 : Nat := 697864882277229299562179

theorem tailTrace_1359087 : CollatzResearch.WordTrace tailWord_1359087 prefixEnd_1359087 697864882277229299562179 := by
  unfold tailWord_1359087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49569975227267387425203515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33046650151511591616802343 49569975227267387425203515)
  ·
    refine ⟨74354962840901081137805273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49569975227267387425203515 74354962840901081137805273)
    ·
      refine ⟨55766222130675810853353955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74354962840901081137805273 55766222130675810853353955)
      ·
        refine ⟨83649333196013716280030933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55766222130675810853353955 83649333196013716280030933)
        ·
          refine ⟨1960531246781571475313225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83649333196013716280030933 1960531246781571475313225)
          ·
            refine ⟨1470398435086178606484919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960531246781571475313225 1470398435086178606484919)
            ·
              refine ⟨2205597652629267909727379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470398435086178606484919 2205597652629267909727379)
              ·
                refine ⟨3308396478943901864591069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205597652629267909727379 3308396478943901864591069)
                ·
                  refine ⟨1240648679603963199221651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3308396478943901864591069 1240648679603963199221651)
                  ·
                    refine ⟨1860973019405944798832477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240648679603963199221651 1860973019405944798832477)
                    ·
                      refine ⟨697864882277229299562179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860973019405944798832477 697864882277229299562179)
                      ·
                        rfl

theorem cell23_1359087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_1359087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359087 prefixEnd_1359087 := by exact prefixLift 1359087
  have htrace : WordTrace (prefixWord ++ tailWord_1359087) baseStart_1359087 baseEnd_1359087 := by
    simpa [prefixWord, tailWord_1359087, baseEnd_1359087] using wordTrace_append hprefix tailTrace_1359087
  have hstable : (prefixWord ++ tailWord_1359087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359087).length < 2 ^ (prefixWord ++ tailWord_1359087).sum := by decide
  have hdescent : baseEnd_1359087 < baseStart_1359087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359096 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_1359096 : Nat := 118140960795 + 1359096 * 2 ^ 59
def prefixEnd_1359096 : Nat := 4983230072969 + 3 ^ 40 * 1359096 * 2
def baseEnd_1359096 : Nat := 697869503603119764349637

theorem tailTrace_1359096 : CollatzResearch.WordTrace tailWord_1359096 prefixEnd_1359096 697869503603119764349637 := by
  unfold tailWord_1359096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785151742117390981140571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33046868989489854641520761 24785151742117390981140571)
  ·
    refine ⟨37177727613176086471710857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24785151742117390981140571 37177727613176086471710857)
    ·
      refine ⟨27883295709882064853783143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37177727613176086471710857 27883295709882064853783143)
      ·
        refine ⟨41824943564823097280674715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27883295709882064853783143 41824943564823097280674715)
        ·
          refine ⟨62737415347234645921012073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41824943564823097280674715 62737415347234645921012073)
          ·
            refine ⟨47053061510425984440759055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62737415347234645921012073 47053061510425984440759055)
            ·
              refine ⟨70579592265638976661138583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47053061510425984440759055 70579592265638976661138583)
              ·
                refine ⟨105869388398458464991707875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70579592265638976661138583 105869388398458464991707875)
                ·
                  refine ⟨158804082597687697487561813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105869388398458464991707875 158804082597687697487561813)
                  ·
                    refine ⟨1860985342941652704932365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 158804082597687697487561813 1860985342941652704932365)
                    ·
                      refine ⟨697869503603119764349637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1860985342941652704932365 697869503603119764349637)
                      ·
                        rfl

theorem cell23_1359096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_1359096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359096 prefixEnd_1359096 := by exact prefixLift 1359096
  have htrace : WordTrace (prefixWord ++ tailWord_1359096) baseStart_1359096 baseEnd_1359096 := by
    simpa [prefixWord, tailWord_1359096, baseEnd_1359096] using wordTrace_append hprefix tailTrace_1359096
  have hstable : (prefixWord ++ tailWord_1359096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359096).length < 2 ^ (prefixWord ++ tailWord_1359096).sum := by decide
  have hdescent : baseEnd_1359096 < baseStart_1359096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359113 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_1359113 : Nat := 118140960795 + 1359113 * 2 ^ 59
def prefixEnd_1359113 : Nat := 4983230072969 + 3 ^ 40 * 1359113 * 2
def baseEnd_1359113 : Nat := 697878232774246197837059

theorem tailTrace_1359113 : CollatzResearch.WordTrace tailWord_1359113 prefixEnd_1359113 697878232774246197837059 := by
  unfold tailWord_1359113
  simp only [CollatzResearch.WordTrace]
  refine ⟨49570923525173193865649993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33047282350115462577099995 49570923525173193865649993)
  ·
    refine ⟨37178192643879895399237495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49570923525173193865649993 37178192643879895399237495)
    ·
      refine ⟨55767288965819843098856243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37178192643879895399237495 55767288965819843098856243)
      ·
        refine ⟨83650933448729764648284365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55767288965819843098856243 83650933448729764648284365)
        ·
          refine ⟨31369100043273661743106637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83650933448729764648284365 31369100043273661743106637)
          ·
            refine ⟨11763412516227623153664989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31369100043273661743106637 11763412516227623153664989)
            ·
              refine ⟨4411279693585358682624371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11763412516227623153664989 4411279693585358682624371)
              ·
                refine ⟨6616919540378038023936557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411279693585358682624371 6616919540378038023936557)
                ·
                  refine ⟨2481344827641764258976209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6616919540378038023936557 2481344827641764258976209)
                  ·
                    refine ⟨1861008620731323194232157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2481344827641764258976209 1861008620731323194232157)
                    ·
                      refine ⟨697878232774246197837059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1861008620731323194232157 697878232774246197837059)
                      ·
                        rfl

theorem cell23_1359113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_1359113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359113 prefixEnd_1359113 := by exact prefixLift 1359113
  have htrace : WordTrace (prefixWord ++ tailWord_1359113) baseStart_1359113 baseEnd_1359113 := by
    simpa [prefixWord, tailWord_1359113, baseEnd_1359113] using wordTrace_append hprefix tailTrace_1359113
  have hstable : (prefixWord ++ tailWord_1359113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359113).length < 2 ^ (prefixWord ++ tailWord_1359113).sum := by decide
  have hdescent : baseEnd_1359113 < baseStart_1359113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359116 : List Nat := [2, 2, 1, 2, 2, 3, 2, 9]
def baseStart_1359116 : Nat := 118140960795 + 1359116 * 2 ^ 59
def prefixEnd_1359116 : Nat := 4983230072969 + 3 ^ 40 * 1359116 * 2
def baseEnd_1359116 : Nat := 25847399008007766151835

theorem tailTrace_1359116 : CollatzResearch.WordTrace tailWord_1359116 prefixEnd_1359116 25847399008007766151835 := by
  unfold tailWord_1359116
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785516472081162689004601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33047355296108216918672801 24785516472081162689004601)
  ·
    refine ⟨18589137354060872016753451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24785516472081162689004601 18589137354060872016753451)
    ·
      refine ⟨27883706031091308025130177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18589137354060872016753451 27883706031091308025130177)
      ·
        refine ⟨20912779523318481018847633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27883706031091308025130177 20912779523318481018847633)
        ·
          refine ⟨15684584642488860764135725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20912779523318481018847633 15684584642488860764135725)
          ·
            refine ⟨5881719240933322786550897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15684584642488860764135725 5881719240933322786550897)
            ·
              refine ⟨4411289430699992089913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881719240933322786550897 4411289430699992089913173)
              ·
                refine ⟨25847399008007766151835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4411289430699992089913173 25847399008007766151835)
                ·
                  rfl

theorem cell23_1359116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 9].length) (baseStart_1359116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359116 prefixEnd_1359116 := by exact prefixLift 1359116
  have htrace : WordTrace (prefixWord ++ tailWord_1359116) baseStart_1359116 baseEnd_1359116 := by
    simpa [prefixWord, tailWord_1359116, baseEnd_1359116] using wordTrace_append hprefix tailTrace_1359116
  have hstable : (prefixWord ++ tailWord_1359116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359116).length < 2 ^ (prefixWord ++ tailWord_1359116).sum := by decide
  have hdescent : baseEnd_1359116 < baseStart_1359116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359130 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1359130 : Nat := 118140960795 + 1359130 * 2 ^ 59
def prefixEnd_1359130 : Nat := 4983230072969 + 3 ^ 40 * 1359130 * 2
def baseEnd_1359130 : Nat := 697886961945372631324481

theorem tailTrace_1359130 : CollatzResearch.WordTrace tailWord_1359130 prefixEnd_1359130 697886961945372631324481 := by
  unfold tailWord_1359130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12392885891527901442254711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33047695710741070512679229 12392885891527901442254711)
  ·
    refine ⟨18589328837291852163382067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12392885891527901442254711 18589328837291852163382067)
    ·
      refine ⟨27883993255937778245073101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18589328837291852163382067 27883993255937778245073101)
      ·
        refine ⟨10456497470976666841902413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27883993255937778245073101 10456497470976666841902413)
        ·
          refine ⟨3921186551616250065713405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10456497470976666841902413 3921186551616250065713405)
          ·
            refine ⟨1470444956856093774642527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3921186551616250065713405 1470444956856093774642527)
            ·
              refine ⟨2205667435284140661963791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470444956856093774642527 2205667435284140661963791)
              ·
                refine ⟨3308501152926210992945687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205667435284140661963791 3308501152926210992945687)
                ·
                  refine ⟨4962751729389316489418531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308501152926210992945687 4962751729389316489418531)
                  ·
                    refine ⟨7444127594083974734127797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962751729389316489418531 7444127594083974734127797)
                    ·
                      refine ⟨697886961945372631324481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7444127594083974734127797 697886961945372631324481)
                      ·
                        rfl

theorem cell23_1359130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1359130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359130 prefixEnd_1359130 := by exact prefixLift 1359130
  have htrace : WordTrace (prefixWord ++ tailWord_1359130) baseStart_1359130 baseEnd_1359130 := by
    simpa [prefixWord, tailWord_1359130, baseEnd_1359130] using wordTrace_append hprefix tailTrace_1359130
  have hstable : (prefixWord ++ tailWord_1359130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359130).length < 2 ^ (prefixWord ++ tailWord_1359130).sum := by decide
  have hdescent : baseEnd_1359130 < baseStart_1359130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359138 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_1359138 : Nat := 118140960795 + 1359138 * 2 ^ 59
def prefixEnd_1359138 : Nat := 4983230072969 + 3 ^ 40 * 1359138 * 2
def baseEnd_1359138 : Nat := 697891069790608600024445

theorem tailTrace_1359138 : CollatzResearch.WordTrace tailWord_1359138 prefixEnd_1359138 697891069790608600024445 := by
  unfold tailWord_1359138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12392958837520655783827517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33047890233388415423540045 12392958837520655783827517)
  ·
    refine ⟨4647359564070245918935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12392958837520655783827517 4647359564070245918935319)
    ·
      refine ⟨6971039346105368878402979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647359564070245918935319 6971039346105368878402979)
      ·
        refine ⟨10456559019158053317604469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971039346105368878402979 10456559019158053317604469)
        ·
          refine ⟨980302408046067498525419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10456559019158053317604469 980302408046067498525419)
          ·
            refine ⟨1470453612069101247788129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980302408046067498525419 1470453612069101247788129)
            ·
              refine ⟨1102840209051825935841097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470453612069101247788129 1102840209051825935841097)
              ·
                refine ⟨827130156788869451880823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102840209051825935841097 827130156788869451880823)
                ·
                  refine ⟨1240695235183304177821235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827130156788869451880823 1240695235183304177821235)
                  ·
                    refine ⟨1861042852774956266731853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240695235183304177821235 1861042852774956266731853)
                    ·
                      refine ⟨697891069790608600024445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1861042852774956266731853 697891069790608600024445)
                      ·
                        rfl

theorem cell23_1359138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_1359138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359138 prefixEnd_1359138 := by exact prefixLift 1359138
  have htrace : WordTrace (prefixWord ++ tailWord_1359138) baseStart_1359138 baseEnd_1359138 := by
    simpa [prefixWord, tailWord_1359138, baseEnd_1359138] using wordTrace_append hprefix tailTrace_1359138
  have hstable : (prefixWord ++ tailWord_1359138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359138).length < 2 ^ (prefixWord ++ tailWord_1359138).sum := by decide
  have hdescent : baseEnd_1359138 < baseStart_1359138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359176 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1359176 : Nat := 118140960795 + 1359176 * 2 ^ 59
def prefixEnd_1359176 : Nat := 4983230072969 + 3 ^ 40 * 1359176 * 2
def baseEnd_1359176 : Nat := 232636860685159817116423

theorem tailTrace_1359176 : CollatzResearch.WordTrace tailWord_1359176 prefixEnd_1359176 232636860685159817116423 := by
  unfold tailWord_1359176
  simp only [CollatzResearch.WordTrace]
  refine ⟨24786610661972477812596691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33048814215963303750128921 24786610661972477812596691)
  ·
    refine ⟨37179915992958716718895037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24786610661972477812596691 37179915992958716718895037)
    ·
      refine ⟨13942468497359518769585639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37179915992958716718895037 13942468497359518769585639)
      ·
        refine ⟨20913702746039278154378459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13942468497359518769585639 20913702746039278154378459)
        ·
          refine ⟨31370554119058917231567689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20913702746039278154378459 31370554119058917231567689)
          ·
            refine ⟨23527915589294187923675767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31370554119058917231567689 23527915589294187923675767)
            ·
              refine ⟨35291873383941281885513651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23527915589294187923675767 35291873383941281885513651)
              ·
                refine ⟨52937810075911922828270477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35291873383941281885513651 52937810075911922828270477)
                ·
                  refine ⟨19851678778466971060601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52937810075911922828270477 19851678778466971060601429)
                  ·
                    refine ⟨232636860685159817116423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19851678778466971060601429 232636860685159817116423)
                    ·
                      rfl

theorem cell23_1359176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1359176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359176 prefixEnd_1359176 := by exact prefixLift 1359176
  have htrace : WordTrace (prefixWord ++ tailWord_1359176) baseStart_1359176 baseEnd_1359176 := by
    simpa [prefixWord, tailWord_1359176, baseEnd_1359176] using wordTrace_append hprefix tailTrace_1359176
  have hstable : (prefixWord ++ tailWord_1359176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359176).length < 2 ^ (prefixWord ++ tailWord_1359176).sum := by decide
  have hdescent : baseEnd_1359176 < baseStart_1359176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359183 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 8, 2]
def baseStart_1359183 : Nat := 118140960795 + 1359183 * 2 ^ 59
def prefixEnd_1359183 : Nat := 4983230072969 + 3 ^ 40 * 1359183 * 2
def baseEnd_1359183 : Nat := 697914176420060923961737

theorem tailTrace_1359183 : CollatzResearch.WordTrace tailWord_1359183 prefixEnd_1359183 697914176420060923961737 := by
  unfold tailWord_1359183
  simp only [CollatzResearch.WordTrace]
  refine ⟨49573476634919595820698203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33048984423279730547132135 49573476634919595820698203)
  ·
    refine ⟨74360214952379393731047305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49573476634919595820698203 74360214952379393731047305)
    ·
      refine ⟨55770161214284545298285479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74360214952379393731047305 55770161214284545298285479)
      ·
        refine ⟨83655241821426817947428219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55770161214284545298285479 83655241821426817947428219)
        ·
          refine ⟨125482862732140226921142329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83655241821426817947428219 125482862732140226921142329)
          ·
            refine ⟨94112147049105170190856747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125482862732140226921142329 94112147049105170190856747)
            ·
              refine ⟨141168220573657755286285121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94112147049105170190856747 141168220573657755286285121)
              ·
                refine ⟨105876165430243316464713841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141168220573657755286285121 105876165430243316464713841)
                ·
                  refine ⟨79407124072682487348535381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105876165430243316464713841 79407124072682487348535381)
                  ·
                    refine ⟨930552235226747898615649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79407124072682487348535381 930552235226747898615649)
                    ·
                      refine ⟨697914176420060923961737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930552235226747898615649 697914176420060923961737)
                      ·
                        rfl

theorem cell23_1359183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8, 2].length) (baseStart_1359183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359183 prefixEnd_1359183 := by exact prefixLift 1359183
  have htrace : WordTrace (prefixWord ++ tailWord_1359183) baseStart_1359183 baseEnd_1359183 := by
    simpa [prefixWord, tailWord_1359183, baseEnd_1359183] using wordTrace_append hprefix tailTrace_1359183
  have hstable : (prefixWord ++ tailWord_1359183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359183).length < 2 ^ (prefixWord ++ tailWord_1359183).sum := by decide
  have hdescent : baseEnd_1359183 < baseStart_1359183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359217 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_1359217 : Nat := 118140960795 + 1359217 * 2 ^ 59
def prefixEnd_1359217 : Nat := 4983230072969 + 3 ^ 40 * 1359217 * 2
def baseEnd_1359217 : Nat := 697931634762313790936581

theorem tailTrace_1359217 : CollatzResearch.WordTrace tailWord_1359217 prefixEnd_1359217 697931634762313790936581 := by
  unfold tailWord_1359217
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574716716796419627435905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33049811144530946418290603 49574716716796419627435905)
  ·
    refine ⟨37181037537597314720576929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49574716716796419627435905 37181037537597314720576929)
    ·
      refine ⟨27885778153197986040432697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37181037537597314720576929 27885778153197986040432697)
      ·
        refine ⟨20914333614898489530324523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27885778153197986040432697 20914333614898489530324523)
        ·
          refine ⟨31371500422347734295486785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914333614898489530324523 31371500422347734295486785)
          ·
            refine ⟨23528625316760800721615089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31371500422347734295486785 23528625316760800721615089)
            ·
              refine ⟨17646468987570600541211317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23528625316760800721615089 17646468987570600541211317)
              ·
                refine ⟨1654356467584743800738561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17646468987570600541211317 1654356467584743800738561)
                ·
                  refine ⟨1240767350688557850553921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654356467584743800738561 1240767350688557850553921)
                  ·
                    refine ⟨930575513016418387915441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240767350688557850553921 930575513016418387915441)
                    ·
                      refine ⟨697931634762313790936581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930575513016418387915441 697931634762313790936581)
                      ·
                        rfl

theorem cell23_1359217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_1359217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359217 prefixEnd_1359217 := by exact prefixLift 1359217
  have htrace : WordTrace (prefixWord ++ tailWord_1359217) baseStart_1359217 baseEnd_1359217 := by
    simpa [prefixWord, tailWord_1359217, baseEnd_1359217] using wordTrace_append hprefix tailTrace_1359217
  have hstable : (prefixWord ++ tailWord_1359217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359217).length < 2 ^ (prefixWord ++ tailWord_1359217).sum := by decide
  have hdescent : baseEnd_1359217 < baseStart_1359217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359253 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1359253 : Nat := 118140960795 + 1359253 * 2 ^ 59
def prefixEnd_1359253 : Nat := 4983230072969 + 3 ^ 40 * 1359253 * 2
def baseEnd_1359253 : Nat := 232650040021958550028805

theorem tailTrace_1359253 : CollatzResearch.WordTrace tailWord_1359253 prefixEnd_1359253 232650040021958550028805 := by
  unfold tailWord_1359253
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576029744665997775746413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33050686496443998517164275 49576029744665997775746413)
  ·
    refine ⟨18591011154249749165904905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49576029744665997775746413 18591011154249749165904905)
    ·
      refine ⟨13943258365687311874428679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18591011154249749165904905 13943258365687311874428679)
      ·
        refine ⟨20914887548530967811643019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13943258365687311874428679 20914887548530967811643019)
        ·
          refine ⟨31372331322796451717464529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914887548530967811643019 31372331322796451717464529)
          ·
            refine ⟨23529248492097338788098397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31372331322796451717464529 23529248492097338788098397)
            ·
              refine ⟨8823468184536502045536899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23529248492097338788098397 8823468184536502045536899)
              ·
                refine ⟨13235202276804753068305349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823468184536502045536899 13235202276804753068305349)
                ·
                  refine ⟨2481600426900891200307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13235202276804753068305349 2481600426900891200307253)
                  ·
                    refine ⟨232650040021958550028805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2481600426900891200307253 232650040021958550028805)
                    ·
                      rfl

theorem cell23_1359253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1359253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359253 prefixEnd_1359253 := by exact prefixLift 1359253
  have htrace : WordTrace (prefixWord ++ tailWord_1359253) baseStart_1359253 baseEnd_1359253 := by
    simpa [prefixWord, tailWord_1359253, baseEnd_1359253] using wordTrace_append hprefix tailTrace_1359253
  have hstable : (prefixWord ++ tailWord_1359253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359253).length < 2 ^ (prefixWord ++ tailWord_1359253).sum := by decide
  have hdescent : baseEnd_1359253 < baseStart_1359253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359257 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 5]
def baseStart_1359257 : Nat := 118140960795 + 1359257 * 2 ^ 59
def prefixEnd_1359257 : Nat := 4983230072969 + 3 ^ 40 * 1359257 * 2
def baseEnd_1359257 : Nat := 77550241554277070492933

theorem tailTrace_1359257 : CollatzResearch.WordTrace tailWord_1359257 prefixEnd_1359257 77550241554277070492933 := by
  unfold tailWord_1359257
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576175636651506458892025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33050783757767670972594683 49576175636651506458892025)
  ·
    refine ⟨37182131727488629844169019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49576175636651506458892025 37182131727488629844169019)
    ·
      refine ⟨55773197591232944766253529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37182131727488629844169019 55773197591232944766253529)
      ·
        refine ⟨41829898193424708574690147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55773197591232944766253529 41829898193424708574690147)
        ·
          refine ⟨62744847290137062862035221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41829898193424708574690147 62744847290137062862035221)
          ·
            refine ⟨2941164716725174821657901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62744847290137062862035221 2941164716725174821657901)
            ·
              refine ⟨1102936768771940558121713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2941164716725174821657901 1102936768771940558121713)
              ·
                refine ⟨827202576578955418591285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102936768771940558121713 827202576578955418591285)
                ·
                  refine ⟨77550241554277070492933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 827202576578955418591285 77550241554277070492933)
                  ·
                    rfl

theorem cell23_1359257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 5].length) (baseStart_1359257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359257 prefixEnd_1359257 := by exact prefixLift 1359257
  have htrace : WordTrace (prefixWord ++ tailWord_1359257) baseStart_1359257 baseEnd_1359257 := by
    simpa [prefixWord, tailWord_1359257, baseEnd_1359257] using wordTrace_append hprefix tailTrace_1359257
  have hstable : (prefixWord ++ tailWord_1359257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359257).length < 2 ^ (prefixWord ++ tailWord_1359257).sum := by decide
  have hdescent : baseEnd_1359257 < baseStart_1359257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359263 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1359263 : Nat := 118140960795 + 1359263 * 2 ^ 59
def prefixEnd_1359263 : Nat := 4983230072969 + 3 ^ 40 * 1359263 * 2
def baseEnd_1359263 : Nat := 697955254872420610961369

theorem tailTrace_1359263 : CollatzResearch.WordTrace tailWord_1359263 prefixEnd_1359263 697955254872420610961369 := by
  unfold tailWord_1359263
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576394474629769483610443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33050929649753179655740295 49576394474629769483610443)
  ·
    refine ⟨74364591711944654225415665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49576394474629769483610443 74364591711944654225415665)
    ·
      refine ⟨55773443783958490669061749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74364591711944654225415665 55773443783958490669061749)
      ·
        refine ⟨5228760354746108500224539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55773443783958490669061749 5228760354746108500224539)
        ·
          refine ⟨7843140532119162750336809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228760354746108500224539 7843140532119162750336809)
          ·
            refine ⟨5882355399089372062752607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843140532119162750336809 5882355399089372062752607)
            ·
              refine ⟨8823533098634058094128911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882355399089372062752607 8823533098634058094128911)
              ·
                refine ⟨13235299647951087141193367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823533098634058094128911 13235299647951087141193367)
                ·
                  refine ⟨19852949471926630711790051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13235299647951087141193367 19852949471926630711790051)
                  ·
                    refine ⟨29779424207889946067685077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19852949471926630711790051 29779424207889946067685077)
                    ·
                      refine ⟨697955254872420610961369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29779424207889946067685077 697955254872420610961369)
                      ·
                        rfl

theorem cell23_1359263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1359263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359263 prefixEnd_1359263 := by exact prefixLift 1359263
  have htrace : WordTrace (prefixWord ++ tailWord_1359263) baseStart_1359263 baseEnd_1359263 := by
    simpa [prefixWord, tailWord_1359263, baseEnd_1359263] using wordTrace_append hprefix tailTrace_1359263
  have hstable : (prefixWord ++ tailWord_1359263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359263).length < 2 ^ (prefixWord ++ tailWord_1359263).sum := by decide
  have hdescent : baseEnd_1359263 < baseStart_1359263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359290 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_1359290 : Nat := 118140960795 + 1359290 * 2 ^ 59
def prefixEnd_1359290 : Nat := 4983230072969 + 3 ^ 40 * 1359290 * 2
def baseEnd_1359290 : Nat := 697969118850092005323745

theorem tailTrace_1359290 : CollatzResearch.WordTrace tailWord_1359290 prefixEnd_1359290 697969118850092005323745 := by
  unfold tailWord_1359290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394344811382988273710831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33051586163687968729895549 12394344811382988273710831)
  ·
    refine ⟨18591517217074482410566247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12394344811382988273710831 18591517217074482410566247)
    ·
      refine ⟨27887275825611723615849371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18591517217074482410566247 27887275825611723615849371)
      ·
        refine ⟨41830913738417585423774057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27887275825611723615849371 41830913738417585423774057)
        ·
          refine ⟨31373185303813189067830543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41830913738417585423774057 31373185303813189067830543)
          ·
            refine ⟨47059777955719783601745815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31373185303813189067830543 47059777955719783601745815)
            ·
              refine ⟨70589666933579675402618723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47059777955719783601745815 70589666933579675402618723)
              ·
                refine ⟨105884500400369513103928085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70589666933579675402618723 105884500400369513103928085)
                ·
                  refine ⟨4963335956267320926746629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105884500400369513103928085 4963335956267320926746629)
                  ·
                    refine ⟨930625491800122673764993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963335956267320926746629 930625491800122673764993)
                    ·
                      refine ⟨697969118850092005323745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930625491800122673764993 697969118850092005323745)
                      ·
                        rfl

theorem cell23_1359290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_1359290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359290 prefixEnd_1359290 := by exact prefixLift 1359290
  have htrace : WordTrace (prefixWord ++ tailWord_1359290) baseStart_1359290 baseEnd_1359290 := by
    simpa [prefixWord, tailWord_1359290, baseEnd_1359290] using wordTrace_append hprefix tailTrace_1359290
  have hstable : (prefixWord ++ tailWord_1359290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359290).length < 2 ^ (prefixWord ++ tailWord_1359290).sum := by decide
  have hdescent : baseEnd_1359290 < baseStart_1359290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359303 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1359303 : Nat := 118140960795 + 1359303 * 2 ^ 59
def prefixEnd_1359303 : Nat := 4983230072969 + 3 ^ 40 * 1359303 * 2
def baseEnd_1359303 : Nat := 697975794098600454461185

theorem tailTrace_1359303 : CollatzResearch.WordTrace tailWord_1359303 prefixEnd_1359303 697975794098600454461185 := by
  unfold tailWord_1359303
  simp only [CollatzResearch.WordTrace]
  refine ⟨49577853394484856315066563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33051902262989904210044375 49577853394484856315066563)
  ·
    refine ⟨74366780091727284472599845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49577853394484856315066563 74366780091727284472599845)
    ·
      refine ⟨13943771267198865838612471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74366780091727284472599845 13943771267198865838612471)
      ·
        refine ⟨20915656900798298757918707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13943771267198865838612471 20915656900798298757918707)
        ·
          refine ⟨31373485351197448136878061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20915656900798298757918707 31373485351197448136878061)
          ·
            refine ⟨11765057006699043051329273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31373485351197448136878061 11765057006699043051329273)
            ·
              refine ⟨8823792755024282288496955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11765057006699043051329273 8823792755024282288496955)
              ·
                refine ⟨13235689132536423432745433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823792755024282288496955 13235689132536423432745433)
                ·
                  refine ⟨9926766849402317574559075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13235689132536423432745433 9926766849402317574559075)
                  ·
                    refine ⟨14890150274103476361838613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9926766849402317574559075 14890150274103476361838613)
                    ·
                      refine ⟨697975794098600454461185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14890150274103476361838613 697975794098600454461185)
                      ·
                        rfl

theorem cell23_1359303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1359303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359303 prefixEnd_1359303 := by exact prefixLift 1359303
  have htrace : WordTrace (prefixWord ++ tailWord_1359303) baseStart_1359303 baseEnd_1359303 := by
    simpa [prefixWord, tailWord_1359303, baseEnd_1359303] using wordTrace_append hprefix tailTrace_1359303
  have hstable : (prefixWord ++ tailWord_1359303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359303).length < 2 ^ (prefixWord ++ tailWord_1359303).sum := by decide
  have hdescent : baseEnd_1359303 < baseStart_1359303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359341 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1359341 : Nat := 118140960795 + 1359341 * 2 ^ 59
def prefixEnd_1359341 : Nat := 4983230072969 + 3 ^ 40 * 1359341 * 2
def baseEnd_1359341 : Nat := 697995306363471305786011

theorem tailTrace_1359341 : CollatzResearch.WordTrace tailWord_1359341 prefixEnd_1359341 697995306363471305786011 := by
  unfold tailWord_1359341
  simp only [CollatzResearch.WordTrace]
  refine ⟨49579239368347188804949877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33052826245564792536633251 49579239368347188804949877)
  ·
    refine ⟨4648053690782548950464051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49579239368347188804949877 4648053690782548950464051)
    ·
      refine ⟨6972080536173823425696077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648053690782548950464051 6972080536173823425696077)
      ·
        refine ⟨2614530201065183784636029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6972080536173823425696077 2614530201065183784636029)
        ·
          refine ⟨980448825399443919238511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2614530201065183784636029 980448825399443919238511)
          ·
            refine ⟨1470673238099165878857767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980448825399443919238511 1470673238099165878857767)
            ·
              refine ⟨2206009857148748818286651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470673238099165878857767 2206009857148748818286651)
              ·
                refine ⟨3309014785723123227429977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206009857148748818286651 3309014785723123227429977)
                ·
                  refine ⟨2481761089292342420572483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309014785723123227429977 2481761089292342420572483)
                  ·
                    refine ⟨3722641633938513630858725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481761089292342420572483 3722641633938513630858725)
                    ·
                      refine ⟨697995306363471305786011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3722641633938513630858725 697995306363471305786011)
                      ·
                        rfl

theorem cell23_1359341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1359341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359341 prefixEnd_1359341 := by exact prefixLift 1359341
  have htrace : WordTrace (prefixWord ++ tailWord_1359341) baseStart_1359341 baseEnd_1359341 := by
    simpa [prefixWord, tailWord_1359341, baseEnd_1359341] using wordTrace_append hprefix tailTrace_1359341
  have hstable : (prefixWord ++ tailWord_1359341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359341).length < 2 ^ (prefixWord ++ tailWord_1359341).sum := by decide
  have hdescent : baseEnd_1359341 < baseStart_1359341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359353 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1359353 : Nat := 118140960795 + 1359353 * 2 ^ 59
def prefixEnd_1359353 : Nat := 4983230072969 + 3 ^ 40 * 1359353 * 2
def baseEnd_1359353 : Nat := 698001468131325258835955

theorem tailTrace_1359353 : CollatzResearch.WordTrace tailWord_1359353 prefixEnd_1359353 698001468131325258835955 := by
  unfold tailWord_1359353
  simp only [CollatzResearch.WordTrace]
  refine ⟨49579677044303714854386713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33053118029535809902924475 49579677044303714854386713)
  ·
    refine ⟨37184757783227786140790035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49579677044303714854386713 37184757783227786140790035)
    ·
      refine ⟨55777136674841679211185053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37184757783227786140790035 55777136674841679211185053)
      ·
        refine ⟨20916426253065629704194395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55777136674841679211185053 20916426253065629704194395)
        ·
          refine ⟨31374639379598444556291593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20916426253065629704194395 31374639379598444556291593)
          ·
            refine ⟨23530979534698833417218695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31374639379598444556291593 23530979534698833417218695)
            ·
              refine ⟨35296469302048250125828043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23530979534698833417218695 35296469302048250125828043)
              ·
                refine ⟨52944703953072375188742065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35296469302048250125828043 52944703953072375188742065)
                ·
                  refine ⟨39708527964804281391556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52944703953072375188742065 39708527964804281391556549)
                  ·
                    refine ⟨7445348993400802760916853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39708527964804281391556549 7445348993400802760916853)
                    ·
                      refine ⟨698001468131325258835955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7445348993400802760916853 698001468131325258835955)
                      ·
                        rfl

theorem cell23_1359353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1359353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359353 prefixEnd_1359353 := by exact prefixLift 1359353
  have htrace : WordTrace (prefixWord ++ tailWord_1359353) baseStart_1359353 baseEnd_1359353 := by
    simpa [prefixWord, tailWord_1359353, baseEnd_1359353] using wordTrace_append hprefix tailTrace_1359353
  have hstable : (prefixWord ++ tailWord_1359353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359353).length < 2 ^ (prefixWord ++ tailWord_1359353).sum := by decide
  have hdescent : baseEnd_1359353 < baseStart_1359353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359364 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1359364 : Nat := 118140960795 + 1359364 * 2 ^ 59
def prefixEnd_1359364 : Nat := 4983230072969 + 3 ^ 40 * 1359364 * 2
def baseEnd_1359364 : Nat := 77556346268724968422045

theorem tailTrace_1359364 : CollatzResearch.WordTrace tailWord_1359364 prefixEnd_1359364 77556346268724968422045 := by
  unfold tailWord_1359364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790039123631931866518573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33053385498175909155358097 24790039123631931866518573)
  ·
    refine ⟨9296264671361974449944465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24790039123631931866518573 9296264671361974449944465)
    ·
      refine ⟨6972198503521480837458349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9296264671361974449944465 6972198503521480837458349)
      ·
        refine ⟨2614574438820555314046881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6972198503521480837458349 2614574438820555314046881)
        ·
          refine ⟨1960930829115416485535161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614574438820555314046881 1960930829115416485535161)
          ·
            refine ⟨1470698121836562364151371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960930829115416485535161 1470698121836562364151371)
            ·
              refine ⟨2206047182754843546227057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470698121836562364151371 2206047182754843546227057)
              ·
                refine ⟨1654535387066132659670293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206047182754843546227057 1654535387066132659670293)
                ·
                  refine ⟨77556346268724968422045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1654535387066132659670293 77556346268724968422045)
                  ·
                    rfl

theorem cell23_1359364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1359364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359364 prefixEnd_1359364 := by exact prefixLift 1359364
  have htrace : WordTrace (prefixWord ++ tailWord_1359364) baseStart_1359364 baseEnd_1359364 := by
    simpa [prefixWord, tailWord_1359364, baseEnd_1359364] using wordTrace_append hprefix tailTrace_1359364
  have hstable : (prefixWord ++ tailWord_1359364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359364).length < 2 ^ (prefixWord ++ tailWord_1359364).sum := by decide
  have hdescent : baseEnd_1359364 < baseStart_1359364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359410 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1359410 : Nat := 118140960795 + 1359410 * 2 ^ 59
def prefixEnd_1359410 : Nat := 4983230072969 + 3 ^ 40 * 1359410 * 2
def baseEnd_1359410 : Nat := 698030736528631535823193

theorem tailTrace_1359410 : CollatzResearch.WordTrace tailWord_1359410 prefixEnd_1359410 698030736528631535823193 := by
  unfold tailWord_1359410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395439001274303397302921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33054504003398142392807789 12395439001274303397302921)
  ·
    refine ⟨9296579250955727547977191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12395439001274303397302921 9296579250955727547977191)
    ·
      refine ⟨13944868876433591321965787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9296579250955727547977191 13944868876433591321965787)
      ·
        refine ⟨20917303314650386982948681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13944868876433591321965787 20917303314650386982948681)
        ·
          refine ⟨15687977485987790237211511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20917303314650386982948681 15687977485987790237211511)
          ·
            refine ⟨23531966228981685355817267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15687977485987790237211511 23531966228981685355817267)
            ·
              refine ⟨35297949343472528033725901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23531966228981685355817267 35297949343472528033725901)
              ·
                refine ⟨13236731003802198012647213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35297949343472528033725901 13236731003802198012647213)
                ·
                  refine ⟨4963774126425824254742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13236731003802198012647213 4963774126425824254742705)
                  ·
                    refine ⟨3722830594819368191057029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963774126425824254742705 3722830594819368191057029)
                    ·
                      refine ⟨698030736528631535823193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3722830594819368191057029 698030736528631535823193)
                      ·
                        rfl

theorem cell23_1359410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1359410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359410 prefixEnd_1359410 := by exact prefixLift 1359410
  have htrace : WordTrace (prefixWord ++ tailWord_1359410) baseStart_1359410 baseEnd_1359410 := by
    simpa [prefixWord, tailWord_1359410, baseEnd_1359410] using wordTrace_append hprefix tailTrace_1359410
  have hstable : (prefixWord ++ tailWord_1359410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359410).length < 2 ^ (prefixWord ++ tailWord_1359410).sum := by decide
  have hdescent : baseEnd_1359410 < baseStart_1359410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359417 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1359417 : Nat := 118140960795 + 1359417 * 2 ^ 59
def prefixEnd_1359417 : Nat := 4983230072969 + 3 ^ 40 * 1359417 * 2
def baseEnd_1359417 : Nat := 698034330893213008435661

theorem tailTrace_1359417 : CollatzResearch.WordTrace tailWord_1359417 prefixEnd_1359417 698034330893213008435661 := by
  unfold tailWord_1359417
  simp only [CollatzResearch.WordTrace]
  refine ⟨49582011316071853784716505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33054674210714569189811003 49582011316071853784716505)
  ·
    refine ⟨37186508487053890338537379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49582011316071853784716505 37186508487053890338537379)
    ·
      refine ⟨55779762730580835507806069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37186508487053890338537379 55779762730580835507806069)
      ·
        refine ⟨5229352755991953328856819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55779762730580835507806069 5229352755991953328856819)
        ·
          refine ⟨7844029133987929993285229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229352755991953328856819 7844029133987929993285229)
          ·
            refine ⟨2941510925245473747481961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7844029133987929993285229 2941510925245473747481961)
            ·
              refine ⟨2206133193934105310611471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2941510925245473747481961 2206133193934105310611471)
              ·
                refine ⟨3309199790901157965917207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206133193934105310611471 3309199790901157965917207)
                ·
                  refine ⟨4963799686351736948875811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309199790901157965917207 4963799686351736948875811)
                  ·
                    refine ⟨7445699529527605423313717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4963799686351736948875811 7445699529527605423313717)
                    ·
                      refine ⟨698034330893213008435661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7445699529527605423313717 698034330893213008435661)
                      ·
                        rfl

theorem cell23_1359417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1359417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359417 prefixEnd_1359417 := by exact prefixLift 1359417
  have htrace : WordTrace (prefixWord ++ tailWord_1359417) baseStart_1359417 baseEnd_1359417 := by
    simpa [prefixWord, tailWord_1359417, baseEnd_1359417] using wordTrace_append hprefix tailTrace_1359417
  have hstable : (prefixWord ++ tailWord_1359417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359417).length < 2 ^ (prefixWord ++ tailWord_1359417).sum := by decide
  have hdescent : baseEnd_1359417 < baseStart_1359417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359464 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1359464 : Nat := 118140960795 + 1359464 * 2 ^ 59
def prefixEnd_1359464 : Nat := 4983230072969 + 3 ^ 40 * 1359464 * 2
def baseEnd_1359464 : Nat := 698058464483974324547945

theorem tailTrace_1359464 : CollatzResearch.WordTrace tailWord_1359464 prefixEnd_1359464 698058464483974324547945 := by
  unfold tailWord_1359464
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791862773450790405838723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33055817031267720541118297 24791862773450790405838723)
  ·
    refine ⟨37187794160176185608758085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24791862773450790405838723 37187794160176185608758085)
    ·
      refine ⟨6972711405033034801642141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37187794160176185608758085 6972711405033034801642141)
      ·
        refine ⟨2614766776887388050615803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6972711405033034801642141 2614766776887388050615803)
        ·
          refine ⟨3922150165331082075923705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614766776887388050615803 3922150165331082075923705)
          ·
            refine ⟨2941612623998311556942779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922150165331082075923705 2941612623998311556942779)
            ·
              refine ⟨4412418935997467335414169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941612623998311556942779 4412418935997467335414169)
              ·
                refine ⟨3309314201998100501560627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412418935997467335414169 3309314201998100501560627)
                ·
                  refine ⟨4963971302997150752340941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309314201998100501560627 4963971302997150752340941)
                  ·
                    refine ⟨1861489238623931532127853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4963971302997150752340941 1861489238623931532127853)
                    ·
                      refine ⟨698058464483974324547945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1861489238623931532127853 698058464483974324547945)
                      ·
                        rfl

theorem cell23_1359464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1359464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359464 prefixEnd_1359464 := by exact prefixLift 1359464
  have htrace : WordTrace (prefixWord ++ tailWord_1359464) baseStart_1359464 baseEnd_1359464 := by
    simpa [prefixWord, tailWord_1359464, baseEnd_1359464] using wordTrace_append hprefix tailTrace_1359464
  have hstable : (prefixWord ++ tailWord_1359464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359464).length < 2 ^ (prefixWord ++ tailWord_1359464).sum := by decide
  have hdescent : baseEnd_1359464 < baseStart_1359464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359547 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 7, 2]
def baseStart_1359547 : Nat := 118140960795 + 1359547 * 2 ^ 59
def prefixEnd_1359547 : Nat := 4983230072969 + 3 ^ 40 * 1359547 * 2
def baseEnd_1359547 : Nat := 698101083378297499810063

theorem tailTrace_1359547 : CollatzResearch.WordTrace tailWord_1359547 prefixEnd_1359547 698101083378297499810063 := by
  unfold tailWord_1359547
  simp only [CollatzResearch.WordTrace]
  refine ⟨49586752805600885986948895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33057835203733923991299263 49586752805600885986948895)
  ·
    refine ⟨74380129208401328980423343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49586752805600885986948895 74380129208401328980423343)
    ·
      refine ⟨111570193812601993470635015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74380129208401328980423343 111570193812601993470635015)
      ·
        refine ⟨167355290718902990205952523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111570193812601993470635015 167355290718902990205952523)
        ·
          refine ⟨251032936078354485308928785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167355290718902990205952523 251032936078354485308928785)
          ·
            refine ⟨188274702058765863981696589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251032936078354485308928785 188274702058765863981696589)
            ·
              refine ⟨70603013272037198993136221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188274702058765863981696589 70603013272037198993136221)
              ·
                refine ⟨26476129977013949622426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70603013272037198993136221 26476129977013949622426083)
                ·
                  refine ⟨39714194965520924433639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26476129977013949622426083 39714194965520924433639125)
                  ·
                    refine ⟨930801444504396666413417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39714194965520924433639125 930801444504396666413417)
                    ·
                      refine ⟨698101083378297499810063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930801444504396666413417 698101083378297499810063)
                      ·
                        rfl

theorem cell23_1359547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7, 2].length) (baseStart_1359547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359547 prefixEnd_1359547 := by exact prefixLift 1359547
  have htrace : WordTrace (prefixWord ++ tailWord_1359547) baseStart_1359547 baseEnd_1359547 := by
    simpa [prefixWord, tailWord_1359547, baseEnd_1359547] using wordTrace_append hprefix tailTrace_1359547
  have hstable : (prefixWord ++ tailWord_1359547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359547).length < 2 ^ (prefixWord ++ tailWord_1359547).sum := by decide
  have hdescent : baseEnd_1359547 < baseStart_1359547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359577 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1359577 : Nat := 118140960795 + 1359577 * 2 ^ 59
def prefixEnd_1359577 : Nat := 4983230072969 + 3 ^ 40 * 1359577 * 2
def baseEnd_1359577 : Nat := 698116487797932382434925

theorem tailTrace_1359577 : CollatzResearch.WordTrace tailWord_1359577 prefixEnd_1359577 698116487797932382434925 := by
  unfold tailWord_1359577
  simp only [CollatzResearch.WordTrace]
  refine ⟨49587846995492201110540985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33058564663661467407027323 49587846995492201110540985)
  ·
    refine ⟨37190885246619150832905739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49587846995492201110540985 37190885246619150832905739)
    ·
      refine ⟨55786327869928726249358609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37190885246619150832905739 55786327869928726249358609)
      ·
        refine ⟨41839745902446544687018957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55786327869928726249358609 41839745902446544687018957)
        ·
          refine ⟨15689904713417454257632109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41839745902446544687018957 15689904713417454257632109)
          ·
            refine ⟨5883714267531545346612041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15689904713417454257632109 5883714267531545346612041)
            ·
              refine ⟨4412785700648659009959031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5883714267531545346612041 4412785700648659009959031)
              ·
                refine ⟨6619178550972988514938547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412785700648659009959031 6619178550972988514938547)
                ·
                  refine ⟨9928767826459482772407821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619178550972988514938547 9928767826459482772407821)
                  ·
                    refine ⟨3723287934922306039652933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9928767826459482772407821 3723287934922306039652933)
                    ·
                      refine ⟨698116487797932382434925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3723287934922306039652933 698116487797932382434925)
                      ·
                        rfl

theorem cell23_1359577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1359577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359577 prefixEnd_1359577 := by exact prefixLift 1359577
  have htrace : WordTrace (prefixWord ++ tailWord_1359577) baseStart_1359577 baseEnd_1359577 := by
    simpa [prefixWord, tailWord_1359577, baseEnd_1359577] using wordTrace_append hprefix tailTrace_1359577
  have hstable : (prefixWord ++ tailWord_1359577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359577).length < 2 ^ (prefixWord ++ tailWord_1359577).sum := by decide
  have hdescent : baseEnd_1359577 < baseStart_1359577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359591 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1359591 : Nat := 118140960795 + 1359591 * 2 ^ 59
def prefixEnd_1359591 : Nat := 4983230072969 + 3 ^ 40 * 1359591 * 2
def baseEnd_1359591 : Nat := 232707892175698442553287

theorem tailTrace_1359591 : CollatzResearch.WordTrace tailWord_1359591 prefixEnd_1359591 232707892175698442553287 := by
  unfold tailWord_1359591
  simp only [CollatzResearch.WordTrace]
  refine ⟨49588357617441481501550627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33058905078294321001033751 49588357617441481501550627)
  ·
    refine ⟨74382536426162222252325941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49588357617441481501550627 74382536426162222252325941)
    ·
      refine ⟨6973362789952708336155557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74382536426162222252325941 6973362789952708336155557)
      ·
        refine ⟨1307505523116132813029167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6973362789952708336155557 1307505523116132813029167)
        ·
          refine ⟨1961258284674199219543751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307505523116132813029167 1961258284674199219543751)
          ·
            refine ⟨2941887427011298829315627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961258284674199219543751 2941887427011298829315627)
            ·
              refine ⟨4412831140516948243973441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941887427011298829315627 4412831140516948243973441)
              ·
                refine ⟨3309623355387711182980081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412831140516948243973441 3309623355387711182980081)
                ·
                  refine ⟨2482217516540783387235061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309623355387711182980081 2482217516540783387235061)
                  ·
                    refine ⟨232707892175698442553287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2482217516540783387235061 232707892175698442553287)
                    ·
                      rfl

theorem cell23_1359591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1359591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359591 prefixEnd_1359591 := by exact prefixLift 1359591
  have htrace : WordTrace (prefixWord ++ tailWord_1359591) baseStart_1359591 baseEnd_1359591 := by
    simpa [prefixWord, tailWord_1359591, baseEnd_1359591] using wordTrace_append hprefix tailTrace_1359591
  have hstable : (prefixWord ++ tailWord_1359591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359591).length < 2 ^ (prefixWord ++ tailWord_1359591).sum := by decide
  have hdescent : baseEnd_1359591 < baseStart_1359591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359594 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_1359594 : Nat := 118140960795 + 1359594 * 2 ^ 59
def prefixEnd_1359594 : Nat := 4983230072969 + 3 ^ 40 * 1359594 * 2
def baseEnd_1359594 : Nat := 698125216969058815922347

theorem tailTrace_1359594 : CollatzResearch.WordTrace tailWord_1359594 prefixEnd_1359594 698125216969058815922347 := by
  unfold tailWord_1359594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12397116759107653253477459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33058978024287075342606557 12397116759107653253477459)
  ·
    refine ⟨18595675138661479880216189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12397116759107653253477459 18595675138661479880216189)
    ·
      refine ⟨6973378176998054955081071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18595675138661479880216189 6973378176998054955081071)
      ·
        refine ⟨10460067265497082432621607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6973378176998054955081071 10460067265497082432621607)
        ·
          refine ⟨15690100898245623648932411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10460067265497082432621607 15690100898245623648932411)
          ·
            refine ⟨23535151347368435473398617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15690100898245623648932411 23535151347368435473398617)
            ·
              refine ⟨17651363510526326605048963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23535151347368435473398617 17651363510526326605048963)
              ·
                refine ⟨26477045265789489907573445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17651363510526326605048963 26477045265789489907573445)
                ·
                  refine ⟨4964445987335529357670021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26477045265789489907573445 4964445987335529357670021)
                  ·
                    refine ⟨930833622625411754563129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964445987335529357670021 930833622625411754563129)
                    ·
                      refine ⟨698125216969058815922347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930833622625411754563129 698125216969058815922347)
                      ·
                        rfl

theorem cell23_1359594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_1359594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359594 prefixEnd_1359594 := by exact prefixLift 1359594
  have htrace : WordTrace (prefixWord ++ tailWord_1359594) baseStart_1359594 baseEnd_1359594 := by
    simpa [prefixWord, tailWord_1359594, baseEnd_1359594] using wordTrace_append hprefix tailTrace_1359594
  have hstable : (prefixWord ++ tailWord_1359594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359594).length < 2 ^ (prefixWord ++ tailWord_1359594).sum := by decide
  have hdescent : baseEnd_1359594 < baseStart_1359594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359627 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3]
def baseStart_1359627 : Nat := 118140960795 + 1359627 * 2 ^ 59
def prefixEnd_1359627 : Nat := 4983230072969 + 3 ^ 40 * 1359627 * 2
def baseEnd_1359627 : Nat := 698142161830657186809695

theorem tailTrace_1359627 : CollatzResearch.WordTrace tailWord_1359627 prefixEnd_1359627 698142161830657186809695 := by
  unfold tailWord_1359627
  simp only [CollatzResearch.WordTrace]
  refine ⟨49589670645311059649861135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33059780430207373099907423 49589670645311059649861135)
  ·
    refine ⟨74384505967966589474791703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49589670645311059649861135 74384505967966589474791703)
    ·
      refine ⟨111576758951949884212187555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74384505967966589474791703 111576758951949884212187555)
      ·
        refine ⟨167365138427924826318281333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111576758951949884212187555 167365138427924826318281333)
        ·
          refine ⟨15690481727617952467338875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167365138427924826318281333 15690481727617952467338875)
          ·
            refine ⟨23535722591426928701008313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15690481727617952467338875 23535722591426928701008313)
            ·
              refine ⟨17651791943570196525756235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23535722591426928701008313 17651791943570196525756235)
              ·
                refine ⟨26477687915355294788634353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17651791943570196525756235 26477687915355294788634353)
                ·
                  refine ⟨19858265936516471091475765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26477687915355294788634353 19858265936516471091475765)
                  ·
                    refine ⟨1861712431548419164825853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19858265936516471091475765 1861712431548419164825853)
                    ·
                      refine ⟨698142161830657186809695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1861712431548419164825853 698142161830657186809695)
                      ·
                        rfl

theorem cell23_1359627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].length) (baseStart_1359627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359627 prefixEnd_1359627 := by exact prefixLift 1359627
  have htrace : WordTrace (prefixWord ++ tailWord_1359627) baseStart_1359627 baseEnd_1359627 := by
    simpa [prefixWord, tailWord_1359627, baseEnd_1359627] using wordTrace_append hprefix tailTrace_1359627
  have hstable : (prefixWord ++ tailWord_1359627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359627).length < 2 ^ (prefixWord ++ tailWord_1359627).sum := by decide
  have hdescent : baseEnd_1359627 < baseStart_1359627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359678 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1359678 : Nat := 118140960795 + 1359678 * 2 ^ 59
def prefixEnd_1359678 : Nat := 4983230072969 + 3 ^ 40 * 1359678 * 2
def baseEnd_1359678 : Nat := 698168349344036487271961

theorem tailTrace_1359678 : CollatzResearch.WordTrace tailWord_1359678 prefixEnd_1359678 698168349344036487271961 := by
  unfold tailWord_1359678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198941346015786919995961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33061020512084196906645125 6198941346015786919995961)
  ·
    refine ⟨4649206009511840189996971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6198941346015786919995961 4649206009511840189996971)
    ·
      refine ⟨6973809014267760284995457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4649206009511840189996971 6973809014267760284995457)
      ·
        refine ⟨5230356760700820213746593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6973809014267760284995457 5230356760700820213746593)
        ·
          refine ⟨3922767570525615160309945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230356760700820213746593 3922767570525615160309945)
          ·
            refine ⟨2942075677894211370232459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922767570525615160309945 2942075677894211370232459)
            ·
              refine ⟨4413113516841317055348689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942075677894211370232459 4413113516841317055348689)
              ·
                refine ⟨3309835137630987791511517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413113516841317055348689 3309835137630987791511517)
                ·
                  refine ⟨1241188176611620421816819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3309835137630987791511517 1241188176611620421816819)
                  ·
                    refine ⟨1861782264917430632725229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241188176611620421816819 1861782264917430632725229)
                    ·
                      refine ⟨698168349344036487271961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1861782264917430632725229 698168349344036487271961)
                      ·
                        rfl

theorem cell23_1359678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1359678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359678 prefixEnd_1359678 := by exact prefixLift 1359678
  have htrace : WordTrace (prefixWord ++ tailWord_1359678) baseStart_1359678 baseEnd_1359678 := by
    simpa [prefixWord, tailWord_1359678, baseEnd_1359678] using wordTrace_append hprefix tailTrace_1359678
  have hstable : (prefixWord ++ tailWord_1359678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359678).length < 2 ^ (prefixWord ++ tailWord_1359678).sum := by decide
  have hdescent : baseEnd_1359678 < baseStart_1359678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
