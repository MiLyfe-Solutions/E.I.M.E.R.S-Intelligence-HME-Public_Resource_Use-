import V185TrunkScan23Chunk0606

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3589141 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3589141 : Nat := 118140960795 + 3589141 * 2 ^ 59
def prefixEnd_3589141 : Nat := 4983230072969 + 3 ^ 40 * 3589141 * 2
def baseEnd_3589141 : Nat := 614318156586282401010449

theorem tailTrace_3589141 : CollatzResearch.WordTrace tailWord_3589141 prefixEnd_3589141 614318156586282401010449 := by
  unfold tailWord_3589141
  simp only [CollatzResearch.WordTrace]
  refine ⟨130906726690162608326359277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87271151126775072217572851 130906726690162608326359277)
  ·
    refine ⟨49090022508810978122384729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130906726690162608326359277 49090022508810978122384729)
    ·
      refine ⟨36817516881608233591788547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49090022508810978122384729 36817516881608233591788547)
      ·
        refine ⟨55226275322412350387682821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36817516881608233591788547 55226275322412350387682821)
        ·
          refine ⟨10354926622952315697690529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55226275322412350387682821 10354926622952315697690529)
          ·
            refine ⟨7766194967214236773267897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354926622952315697690529 7766194967214236773267897)
            ·
              refine ⟨5824646225410677579950923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7766194967214236773267897 5824646225410677579950923)
              ·
                refine ⟨8736969338116016369926385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824646225410677579950923 8736969338116016369926385)
                ·
                  refine ⟨6552727003587012277444789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8736969338116016369926385 6552727003587012277444789)
                  ·
                    refine ⟨614318156586282401010449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6552727003587012277444789 614318156586282401010449)
                    ·
                      rfl

theorem cell23_3589141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3589141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589141 prefixEnd_3589141 := by exact prefixLift 3589141
  have htrace : WordTrace (prefixWord ++ tailWord_3589141) baseStart_3589141 baseEnd_3589141 := by
    simpa [prefixWord, tailWord_3589141, baseEnd_3589141] using wordTrace_append hprefix tailTrace_3589141
  have hstable : (prefixWord ++ tailWord_3589141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589141).length < 2 ^ (prefixWord ++ tailWord_3589141).sum := by decide
  have hdescent : baseEnd_3589141 < baseStart_3589141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589162 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_3589162 : Nat := 118140960795 + 3589162 * 2 ^ 59
def prefixEnd_3589162 : Nat := 4983230072969 + 3 ^ 40 * 3589162 * 2
def baseEnd_3589162 : Nat := 204773916983621291207639

theorem tailTrace_3589162 : CollatzResearch.WordTrace tailWord_3589162 prefixEnd_3589162 204773916983621291207639 := by
  unfold tailWord_3589162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726873155771632228218435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87271661748724352608582493 32726873155771632228218435)
  ·
    refine ⟨49090309733657448342327653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726873155771632228218435 49090309733657448342327653)
    ·
      refine ⟨9204433075060771564186435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49090309733657448342327653 9204433075060771564186435)
      ·
        refine ⟨13806649612591157346279653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9204433075060771564186435 13806649612591157346279653)
        ·
          refine ⟨2588746802360842002427435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13806649612591157346279653 2588746802360842002427435)
          ·
            refine ⟨3883120203541263003641153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588746802360842002427435 3883120203541263003641153)
            ·
              refine ⟨2912340152655947252730865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883120203541263003641153 2912340152655947252730865)
              ·
                refine ⟨2184255114491960439548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912340152655947252730865 2184255114491960439548149)
                ·
                  refine ⟨204773916983621291207639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184255114491960439548149 204773916983621291207639)
                  ·
                    rfl

theorem cell23_3589162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_3589162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589162 prefixEnd_3589162 := by exact prefixLift 3589162
  have htrace : WordTrace (prefixWord ++ tailWord_3589162) baseStart_3589162 baseEnd_3589162 := by
    simpa [prefixWord, tailWord_3589162, baseEnd_3589162] using wordTrace_append hprefix tailTrace_3589162
  have hstable : (prefixWord ++ tailWord_3589162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589162).length < 2 ^ (prefixWord ++ tailWord_3589162).sum := by decide
  have hdescent : baseEnd_3589162 < baseStart_3589162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589167 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 12]
def baseStart_3589167 : Nat := 118140960795 + 3589167 * 2 ^ 59
def prefixEnd_3589167 : Nat := 4983230072969 + 3 ^ 40 * 3589167 * 2
def baseEnd_3589167 : Nat := 204774202250651566811803

theorem tailTrace_3589167 : CollatzResearch.WordTrace tailWord_3589167 prefixEnd_3589167 204774202250651566811803 := by
  unfold tailWord_3589167
  simp only [CollatzResearch.WordTrace]
  refine ⟨130907674988068414766805755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87271783325378943177870503 130907674988068414766805755)
  ·
    refine ⟨196361512482102622150208633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130907674988068414766805755 196361512482102622150208633)
    ·
      refine ⟨147271134361576966612656475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196361512482102622150208633 147271134361576966612656475)
      ·
        refine ⟨220906701542365449918984713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147271134361576966612656475 220906701542365449918984713)
        ·
          refine ⟨165680026156774087439238535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220906701542365449918984713 165680026156774087439238535)
          ·
            refine ⟨248520039235161131158857803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165680026156774087439238535 248520039235161131158857803)
            ·
              refine ⟨372780058852741696738286705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248520039235161131158857803 372780058852741696738286705)
              ·
                refine ⟨279585044139556272553715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372780058852741696738286705 279585044139556272553715029)
                ·
                  refine ⟨204774202250651566811803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 279585044139556272553715029 204774202250651566811803)
                  ·
                    rfl

theorem cell23_3589167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 12].length) (baseStart_3589167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589167 prefixEnd_3589167 := by exact prefixLift 3589167
  have htrace : WordTrace (prefixWord ++ tailWord_3589167) baseStart_3589167 baseEnd_3589167 := by
    simpa [prefixWord, tailWord_3589167, baseEnd_3589167] using wordTrace_append hprefix tailTrace_3589167
  have hstable : (prefixWord ++ tailWord_3589167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589167).length < 2 ^ (prefixWord ++ tailWord_3589167).sum := by decide
  have hdescent : baseEnd_3589167 < baseStart_3589167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589184 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 6]
def baseStart_3589184 : Nat := 118140960795 + 3589184 * 2 ^ 59
def prefixEnd_3589184 : Nat := 4983230072969 + 3 ^ 40 * 3589184 * 2
def baseEnd_3589184 : Nat := 204775172158554503865961

theorem tailTrace_3589184 : CollatzResearch.WordTrace tailWord_3589184 prefixEnd_3589184 204775172158554503865961 := by
  unfold tailWord_3589184
  simp only [CollatzResearch.WordTrace]
  refine ⟨65454147514503413335087303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87272196686004551113449737 65454147514503413335087303)
  ·
    refine ⟨98181221271755120002630955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65454147514503413335087303 98181221271755120002630955)
    ·
      refine ⟨147271831907632680003946433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98181221271755120002630955 147271831907632680003946433)
      ·
        refine ⟨110453873930724510002959825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147271831907632680003946433 110453873930724510002959825)
        ·
          refine ⟨82840405448043382502219869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110453873930724510002959825 82840405448043382502219869)
          ·
            refine ⟨31065152043016268438332451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82840405448043382502219869 31065152043016268438332451)
            ·
              refine ⟨46597728064524402657498677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31065152043016268438332451 46597728064524402657498677)
              ·
                refine ⟨4368537006049162749140501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46597728064524402657498677 4368537006049162749140501)
                ·
                  refine ⟨204775172158554503865961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4368537006049162749140501 204775172158554503865961)
                  ·
                    rfl

theorem cell23_3589184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_3589184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589184 prefixEnd_3589184 := by exact prefixLift 3589184
  have htrace : WordTrace (prefixWord ++ tailWord_3589184) baseStart_3589184 baseEnd_3589184 := by
    simpa [prefixWord, tailWord_3589184, baseEnd_3589184] using wordTrace_append hprefix tailTrace_3589184
  have hstable : (prefixWord ++ tailWord_3589184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589184).length < 2 ^ (prefixWord ++ tailWord_3589184).sum := by decide
  have hdescent : baseEnd_3589184 < baseStart_3589184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589218 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3589218 : Nat := 118140960795 + 3589218 * 2 ^ 59
def prefixEnd_3589218 : Nat := 4983230072969 + 3 ^ 40 * 3589218 * 2
def baseEnd_3589218 : Nat := 204777111974360377974277

theorem tailTrace_3589218 : CollatzResearch.WordTrace tailWord_3589218 prefixEnd_3589218 204777111974360377974277 := by
  unfold tailWord_3589218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727383777720912619228077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87273023407255766984608205 32727383777720912619228077)
  ·
    refine ⟨12272768916645342232210529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32727383777720912619228077 12272768916645342232210529)
    ·
      refine ⟨9204576687484006674157897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12272768916645342232210529 9204576687484006674157897)
      ·
        refine ⟨6903432515613005005618423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204576687484006674157897 6903432515613005005618423)
        ·
          refine ⟨10355148773419507508427635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903432515613005005618423 10355148773419507508427635)
          ·
            refine ⟨15532723160129261262641453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355148773419507508427635 15532723160129261262641453)
            ·
              refine ⟨5824771185048472973490545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15532723160129261262641453 5824771185048472973490545)
              ·
                refine ⟨4368578388786354730117909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824771185048472973490545 4368578388786354730117909)
                ·
                  refine ⟨204777111974360377974277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4368578388786354730117909 204777111974360377974277)
                  ·
                    rfl

theorem cell23_3589218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3589218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589218 prefixEnd_3589218 := by exact prefixLift 3589218
  have htrace : WordTrace (prefixWord ++ tailWord_3589218) baseStart_3589218 baseEnd_3589218 := by
    simpa [prefixWord, tailWord_3589218, baseEnd_3589218] using wordTrace_append hprefix tailTrace_3589218
  have hstable : (prefixWord ++ tailWord_3589218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589218).length < 2 ^ (prefixWord ++ tailWord_3589218).sum := by decide
  have hdescent : baseEnd_3589218 < baseStart_3589218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589228 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_3589228 : Nat := 118140960795 + 3589228 * 2 ^ 59
def prefixEnd_3589228 : Nat := 4983230072969 + 3 ^ 40 * 3589228 * 2
def baseEnd_3589228 : Nat := 1842999142575788362643447

theorem tailTrace_3589228 : CollatzResearch.WordTrace tailWord_3589228 prefixEnd_3589228 1842999142575788362643447 := by
  unfold tailWord_3589228
  simp only [CollatzResearch.WordTrace]
  refine ⟨65454949920423711092388169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87273266560564948123184225 65454949920423711092388169)
  ·
    refine ⟨49091212440317783319291127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65454949920423711092388169 49091212440317783319291127)
    ·
      refine ⟨73636818660476674978936691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49091212440317783319291127 73636818660476674978936691)
      ·
        refine ⟨110455227990715012468405037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73636818660476674978936691 110455227990715012468405037)
        ·
          refine ⟨41420710496518129675651889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110455227990715012468405037 41420710496518129675651889)
          ·
            refine ⟨31065532872388597256738917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41420710496518129675651889 31065532872388597256738917)
            ·
              refine ⟨5824787413572861985638547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31065532872388597256738917 5824787413572861985638547)
              ·
                refine ⟨8737181120359292978457821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824787413572861985638547 8737181120359292978457821)
                ·
                  refine ⟨3276442920134734866921683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8737181120359292978457821 3276442920134734866921683)
                  ·
                    refine ⟨4914664380202102300382525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276442920134734866921683 4914664380202102300382525)
                    ·
                      refine ⟨1842999142575788362643447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914664380202102300382525 1842999142575788362643447)
                      ·
                        rfl

theorem cell23_3589228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_3589228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589228 prefixEnd_3589228 := by exact prefixLift 3589228
  have htrace : WordTrace (prefixWord ++ tailWord_3589228) baseStart_3589228 baseEnd_3589228 := by
    simpa [prefixWord, tailWord_3589228, baseEnd_3589228] using wordTrace_append hprefix tailTrace_3589228
  have hstable : (prefixWord ++ tailWord_3589228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589228).length < 2 ^ (prefixWord ++ tailWord_3589228).sum := by decide
  have hdescent : baseEnd_3589228 < baseStart_3589228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589238 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3589238 : Nat := 118140960795 + 3589238 * 2 ^ 59
def prefixEnd_3589238 : Nat := 4983230072969 + 3 ^ 40 * 3589238 * 2
def baseEnd_3589238 : Nat := 1843004277382333323518401

theorem tailTrace_3589238 : CollatzResearch.WordTrace tailWord_3589238 prefixEnd_3589238 1843004277382333323518401 := by
  unfold tailWord_3589238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181891535675699618290023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87273509713874129261760245 8181891535675699618290023)
  ·
    refine ⟨12272837303513549427435035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8181891535675699618290023 12272837303513549427435035)
    ·
      refine ⟨18409255955270324141152553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12272837303513549427435035 18409255955270324141152553)
      ·
        refine ⟨13806941966452743105864415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18409255955270324141152553 13806941966452743105864415)
        ·
          refine ⟨20710412949679114658796623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13806941966452743105864415 20710412949679114658796623)
          ·
            refine ⟨31065619424518671988194935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20710412949679114658796623 31065619424518671988194935)
            ·
              refine ⟨46598429136778007982292403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31065619424518671988194935 46598429136778007982292403)
              ·
                refine ⟨69897643705167011973438605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46598429136778007982292403 69897643705167011973438605)
                ·
                  refine ⟨26211616389437629490039477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69897643705167011973438605 26211616389437629490039477)
                  ·
                    refine ⟨2457339036509777764691201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26211616389437629490039477 2457339036509777764691201)
                    ·
                      refine ⟨1843004277382333323518401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457339036509777764691201 1843004277382333323518401)
                      ·
                        rfl

theorem cell23_3589238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3589238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589238 prefixEnd_3589238 := by exact prefixLift 3589238
  have htrace : WordTrace (prefixWord ++ tailWord_3589238) baseStart_3589238 baseEnd_3589238 := by
    simpa [prefixWord, tailWord_3589238, baseEnd_3589238] using wordTrace_append hprefix tailTrace_3589238
  have hstable : (prefixWord ++ tailWord_3589238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589238).length < 2 ^ (prefixWord ++ tailWord_3589238).sum := by decide
  have hdescent : baseEnd_3589238 < baseStart_3589238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589251 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 6, 2]
def baseStart_3589251 : Nat := 118140960795 + 3589251 * 2 ^ 59
def prefixEnd_3589251 : Nat := 4983230072969 + 3 ^ 40 * 3589251 * 2
def baseEnd_3589251 : Nat := 1843010952630841772655841

theorem tailTrace_3589251 : CollatzResearch.WordTrace tailWord_3589251 prefixEnd_3589251 1843010952630841772655841 := by
  unfold tailWord_3589251
  simp only [CollatzResearch.WordTrace]
  refine ⟨130910738719764097112863607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87273825813176064741909071 130910738719764097112863607)
  ·
    refine ⟨196366108079646145669295411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130910738719764097112863607 196366108079646145669295411)
    ·
      refine ⟨294549162119469218503943117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196366108079646145669295411 294549162119469218503943117)
      ·
        refine ⟨110455935794800956938978669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294549162119469218503943117 110455935794800956938978669)
        ·
          refine ⟨41420975923050358852117001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110455935794800956938978669 41420975923050358852117001)
          ·
            refine ⟨31065731942287769139087751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41420975923050358852117001 31065731942287769139087751)
            ·
              refine ⟨46598597913431653708631627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31065731942287769139087751 46598597913431653708631627)
              ·
                refine ⟨69897896870147480562947441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46598597913431653708631627 69897896870147480562947441)
                ·
                  refine ⟨52423422652610610422210581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69897896870147480562947441 52423422652610610422210581)
                  ·
                    refine ⟨2457347936841122363541121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52423422652610610422210581 2457347936841122363541121)
                    ·
                      refine ⟨1843010952630841772655841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457347936841122363541121 1843010952630841772655841)
                      ·
                        rfl

theorem cell23_3589251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_3589251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589251 prefixEnd_3589251 := by exact prefixLift 3589251
  have htrace : WordTrace (prefixWord ++ tailWord_3589251) baseStart_3589251 baseEnd_3589251 := by
    simpa [prefixWord, tailWord_3589251, baseEnd_3589251] using wordTrace_append hprefix tailTrace_3589251
  have hstable : (prefixWord ++ tailWord_3589251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589251).length < 2 ^ (prefixWord ++ tailWord_3589251).sum := by decide
  have hdescent : baseEnd_3589251 < baseStart_3589251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589262 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3589262 : Nat := 118140960795 + 3589262 * 2 ^ 59
def prefixEnd_3589262 : Nat := 4983230072969 + 3 ^ 40 * 3589262 * 2
def baseEnd_3589262 : Nat := 1843016600918041229618291

theorem tailTrace_3589262 : CollatzResearch.WordTrace tailWord_3589262 prefixEnd_3589262 1843016600918041229618291 := by
  unfold tailWord_3589262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363892490340530748939255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87274093281816163994342693 16363892490340530748939255)
  ·
    refine ⟨24545838735510796123408883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363892490340530748939255 24545838735510796123408883)
    ·
      refine ⟨36818758103266194185113325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24545838735510796123408883 36818758103266194185113325)
      ·
        refine ⟨13807034288724822819417497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36818758103266194185113325 13807034288724822819417497)
        ·
          refine ⟨10355275716543617114563123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13807034288724822819417497 10355275716543617114563123)
          ·
            refine ⟨15532913574815425671844685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355275716543617114563123 15532913574815425671844685)
            ·
              refine ⟨5824842590555784626941757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15532913574815425671844685 5824842590555784626941757)
              ·
                refine ⟨2184315971458419235103159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5824842590555784626941757 2184315971458419235103159)
                ·
                  refine ⟨3276473957187628852654739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184315971458419235103159 3276473957187628852654739)
                  ·
                    refine ⟨4914710935781443278982109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276473957187628852654739 4914710935781443278982109)
                    ·
                      refine ⟨1843016600918041229618291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914710935781443278982109 1843016600918041229618291)
                      ·
                        rfl

theorem cell23_3589262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3589262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589262 prefixEnd_3589262 := by exact prefixLift 3589262
  have htrace : WordTrace (prefixWord ++ tailWord_3589262) baseStart_3589262 baseEnd_3589262 := by
    simpa [prefixWord, tailWord_3589262, baseEnd_3589262] using wordTrace_append hprefix tailTrace_3589262
  have hstable : (prefixWord ++ tailWord_3589262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589262).length < 2 ^ (prefixWord ++ tailWord_3589262).sum := by decide
  have hdescent : baseEnd_3589262 < baseStart_3589262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589271 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3589271 : Nat := 118140960795 + 3589271 * 2 ^ 59
def prefixEnd_3589271 : Nat := 4983230072969 + 3 ^ 40 * 3589271 * 2
def baseEnd_3589271 : Nat := 1843021222243931694405749

theorem tailTrace_3589271 : CollatzResearch.WordTrace tailWord_3589271 prefixEnd_3589271 1843021222243931694405749 := by
  unfold tailWord_3589271
  simp only [CollatzResearch.WordTrace]
  refine ⟨130911468179691640528591667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87274312119794427019061111 130911468179691640528591667)
  ·
    refine ⟨196367202269537460792887501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130911468179691640528591667 196367202269537460792887501)
    ·
      refine ⟨73637700851076547797332813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196367202269537460792887501 73637700851076547797332813)
      ·
        refine ⟨27614137819153705423999805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73637700851076547797332813 27614137819153705423999805)
        ·
          refine ⟨10355301682182639533999927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27614137819153705423999805 10355301682182639533999927)
          ·
            refine ⟨15532952523273959300999891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355301682182639533999927 15532952523273959300999891)
            ·
              refine ⟨23299428784910938951499837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15532952523273959300999891 23299428784910938951499837)
              ·
                refine ⟨8737285794341602106812439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23299428784910938951499837 8737285794341602106812439)
                ·
                  refine ⟨13105928691512403160218659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737285794341602106812439 13105928691512403160218659)
                  ·
                    refine ⟨19658893037268604740327989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13105928691512403160218659 19658893037268604740327989)
                    ·
                      refine ⟨1843021222243931694405749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19658893037268604740327989 1843021222243931694405749)
                      ·
                        rfl

theorem cell23_3589271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3589271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589271 prefixEnd_3589271 := by exact prefixLift 3589271
  have htrace : WordTrace (prefixWord ++ tailWord_3589271) baseStart_3589271 baseEnd_3589271 := by
    simpa [prefixWord, tailWord_3589271, baseEnd_3589271] using wordTrace_append hprefix tailTrace_3589271
  have hstable : (prefixWord ++ tailWord_3589271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589271).length < 2 ^ (prefixWord ++ tailWord_3589271).sum := by decide
  have hdescent : baseEnd_3589271 < baseStart_3589271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589279 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3589279 : Nat := 118140960795 + 3589279 * 2 ^ 59
def prefixEnd_3589279 : Nat := 4983230072969 + 3 ^ 40 * 3589279 * 2
def baseEnd_3589279 : Nat := 1843025330089167663105713

theorem tailTrace_3589279 : CollatzResearch.WordTrace tailWord_3589279 prefixEnd_3589279 1843025330089167663105713 := by
  unfold tailWord_3589279
  simp only [CollatzResearch.WordTrace]
  refine ⟨130911759963662657894882891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87274506642441771929921927 130911759963662657894882891)
  ·
    refine ⟨196367639945493986842324337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130911759963662657894882891 196367639945493986842324337)
    ·
      refine ⟨147275729959120490131743253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196367639945493986842324337 147275729959120490131743253)
      ·
        refine ⟨6903549841833772974925465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147275729959120490131743253 6903549841833772974925465)
        ·
          refine ⟨5177662381375329731194099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903549841833772974925465 5177662381375329731194099)
          ·
            refine ⟨7766493572062994596791149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177662381375329731194099 7766493572062994596791149)
            ·
              refine ⟨2912435089523622973796681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7766493572062994596791149 2912435089523622973796681)
              ·
                refine ⟨2184326317142717230347511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912435089523622973796681 2184326317142717230347511)
                ·
                  refine ⟨3276489475714075845521267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184326317142717230347511 3276489475714075845521267)
                  ·
                    refine ⟨4914734213571113768281901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276489475714075845521267 4914734213571113768281901)
                    ·
                      refine ⟨1843025330089167663105713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914734213571113768281901 1843025330089167663105713)
                      ·
                        rfl

theorem cell23_3589279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3589279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589279 prefixEnd_3589279 := by exact prefixLift 3589279
  have htrace : WordTrace (prefixWord ++ tailWord_3589279) baseStart_3589279 baseEnd_3589279 := by
    simpa [prefixWord, tailWord_3589279, baseEnd_3589279] using wordTrace_append hprefix tailTrace_3589279
  have hstable : (prefixWord ++ tailWord_3589279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589279).length < 2 ^ (prefixWord ++ tailWord_3589279).sum := by decide
  have hdescent : baseEnd_3589279 < baseStart_3589279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589285 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_3589285 : Nat := 118140960795 + 3589285 * 2 ^ 59
def prefixEnd_3589285 : Nat := 4983230072969 + 3 ^ 40 * 3589285 * 2
def baseEnd_3589285 : Nat := 1843028410973094639630685

theorem tailTrace_3589285 : CollatzResearch.WordTrace tailWord_3589285 prefixEnd_3589285 1843028410973094639630685 := by
  unfold tailWord_3589285
  simp only [CollatzResearch.WordTrace]
  refine ⟨130911978801640920919601309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87274652534427280613067539 130911978801640920919601309)
  ·
    refine ⟨49091992050615345344850491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130911978801640920919601309 49091992050615345344850491)
    ·
      refine ⟨73637988075923018017275737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49091992050615345344850491 73637988075923018017275737)
      ·
        refine ⟨55228491056942263512956803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73637988075923018017275737 55228491056942263512956803)
        ·
          refine ⟨82842736585413395269435205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55228491056942263512956803 82842736585413395269435205)
          ·
            refine ⟨15533013109765011613019101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82842736585413395269435205 15533013109765011613019101)
            ·
              refine ⟨5824879916161879354882163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15533013109765011613019101 5824879916161879354882163)
              ·
                refine ⟨8737319874242819032323245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824879916161879354882163 8737319874242819032323245)
                ·
                  refine ⟨3276494952841057137121217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8737319874242819032323245 3276494952841057137121217)
                  ·
                    refine ⟨2457371214630792852840913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276494952841057137121217 2457371214630792852840913)
                    ·
                      refine ⟨1843028410973094639630685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457371214630792852840913 1843028410973094639630685)
                      ·
                        rfl

theorem cell23_3589285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_3589285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589285 prefixEnd_3589285 := by exact prefixLift 3589285
  have htrace : WordTrace (prefixWord ++ tailWord_3589285) baseStart_3589285 baseEnd_3589285 := by
    simpa [prefixWord, tailWord_3589285, baseEnd_3589285] using wordTrace_append hprefix tailTrace_3589285
  have hstable : (prefixWord ++ tailWord_3589285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589285).length < 2 ^ (prefixWord ++ tailWord_3589285).sum := by decide
  have hdescent : baseEnd_3589285 < baseStart_3589285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589302 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3589302 : Nat := 118140960795 + 3589302 * 2 ^ 59
def prefixEnd_3589302 : Nat := 4983230072969 + 3 ^ 40 * 3589302 * 2
def baseEnd_3589302 : Nat := 1843037140144221073118107

theorem tailTrace_3589302 : CollatzResearch.WordTrace tailWord_3589302 prefixEnd_3589302 1843037140144221073118107 := by
  unfold tailWord_3589302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182037427661208301435635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87275065895052888548646773 8182037427661208301435635)
  ·
    refine ⟨12273056141491812452153453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182037427661208301435635 12273056141491812452153453)
    ·
      refine ⟨4602396053059429669557545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12273056141491812452153453 4602396053059429669557545)
      ·
        refine ⟨3451797039794572252168159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4602396053059429669557545 3451797039794572252168159)
        ·
          refine ⟨5177695559691858378252239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451797039794572252168159 5177695559691858378252239)
          ·
            refine ⟨7766543339537787567378359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177695559691858378252239 7766543339537787567378359)
            ·
              refine ⟨11649815009306681351067539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766543339537787567378359 11649815009306681351067539)
              ·
                refine ⟨17474722513960022026601309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649815009306681351067539 17474722513960022026601309)
                ·
                  refine ⟨6553020942735008259975491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17474722513960022026601309 6553020942735008259975491)
                  ·
                    refine ⟨9829531414102512389963237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553020942735008259975491 9829531414102512389963237)
                    ·
                      refine ⟨1843037140144221073118107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9829531414102512389963237 1843037140144221073118107)
                      ·
                        rfl

theorem cell23_3589302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3589302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589302 prefixEnd_3589302 := by exact prefixLift 3589302
  have htrace : WordTrace (prefixWord ++ tailWord_3589302) baseStart_3589302 baseEnd_3589302 := by
    simpa [prefixWord, tailWord_3589302, baseEnd_3589302] using wordTrace_append hprefix tailTrace_3589302
  have hstable : (prefixWord ++ tailWord_3589302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589302).length < 2 ^ (prefixWord ++ tailWord_3589302).sum := by decide
  have hdescent : baseEnd_3589302 < baseStart_3589302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589304 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_3589304 : Nat := 118140960795 + 3589304 * 2 ^ 59
def prefixEnd_3589304 : Nat := 4983230072969 + 3 ^ 40 * 3589304 * 2
def baseEnd_3589304 : Nat := 614346055701843355097699

theorem tailTrace_3589304 : CollatzResearch.WordTrace tailWord_3589304 prefixEnd_3589304 614346055701843355097699 := by
  unfold tailWord_3589304
  simp only [CollatzResearch.WordTrace]
  refine ⟨65456335894286043582271483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87275114525714724776361977 65456335894286043582271483)
  ·
    refine ⟨98184503841429065373407225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65456335894286043582271483 98184503841429065373407225)
    ·
      refine ⟨73638377881071799030055419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98184503841429065373407225 73638377881071799030055419)
      ·
        refine ⟨110457566821607698545083129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73638377881071799030055419 110457566821607698545083129)
        ·
          refine ⟨82843175116205773908812347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110457566821607698545083129 82843175116205773908812347)
          ·
            refine ⟨124264762674308660863218521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82843175116205773908812347 124264762674308660863218521)
            ·
              refine ⟨93198572005731495647413891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124264762674308660863218521 93198572005731495647413891)
              ·
                refine ⟨139797858008597243471120837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93198572005731495647413891 139797858008597243471120837)
                ·
                  refine ⟨26212098376611983150835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139797858008597243471120837 26212098376611983150835157)
                  ·
                    refine ⟨614346055701843355097699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26212098376611983150835157 614346055701843355097699)
                    ·
                      rfl

theorem cell23_3589304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_3589304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589304 prefixEnd_3589304 := by exact prefixLift 3589304
  have htrace : WordTrace (prefixWord ++ tailWord_3589304) baseStart_3589304 baseEnd_3589304 := by
    simpa [prefixWord, tailWord_3589304, baseEnd_3589304] using wordTrace_append hprefix tailTrace_3589304
  have hstable : (prefixWord ++ tailWord_3589304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589304).length < 2 ^ (prefixWord ++ tailWord_3589304).sum := by decide
  have hdescent : baseEnd_3589304 < baseStart_3589304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589305 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3589305 : Nat := 118140960795 + 3589305 * 2 ^ 59
def prefixEnd_3589305 : Nat := 4983230072969 + 3 ^ 40 * 3589305 * 2
def baseEnd_3589305 : Nat := 1843038680586184561380593

theorem tailTrace_3589305 : CollatzResearch.WordTrace tailWord_3589305 prefixEnd_3589305 1843038680586184561380593 := by
  unfold tailWord_3589305
  simp only [CollatzResearch.WordTrace]
  refine ⟨130912708261568464335329369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87275138841045642890219579 130912708261568464335329369)
  ·
    refine ⟨98184531196176348251497027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130912708261568464335329369 98184531196176348251497027)
    ·
      refine ⟨147276796794264522377245541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98184531196176348251497027 147276796794264522377245541)
      ·
        refine ⟨27614399398924597945733539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147276796794264522377245541 27614399398924597945733539)
        ·
          refine ⟨41421599098386896918600309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27614399398924597945733539 41421599098386896918600309)
          ·
            refine ⟨3883274915473771586118779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41421599098386896918600309 3883274915473771586118779)
            ·
              refine ⟨5824912373210657379178169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883274915473771586118779 5824912373210657379178169)
              ·
                refine ⟨4368684279907993034383627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824912373210657379178169 4368684279907993034383627)
                ·
                  refine ⟨6553026419861989551575441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368684279907993034383627 6553026419861989551575441)
                  ·
                    refine ⟨4914769814896492163681581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6553026419861989551575441 4914769814896492163681581)
                    ·
                      refine ⟨1843038680586184561380593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914769814896492163681581 1843038680586184561380593)
                      ·
                        rfl

theorem cell23_3589305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3589305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589305 prefixEnd_3589305 := by exact prefixLift 3589305
  have htrace : WordTrace (prefixWord ++ tailWord_3589305) baseStart_3589305 baseEnd_3589305 := by
    simpa [prefixWord, tailWord_3589305, baseEnd_3589305] using wordTrace_append hprefix tailTrace_3589305
  have hstable : (prefixWord ++ tailWord_3589305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589305).length < 2 ^ (prefixWord ++ tailWord_3589305).sum := by decide
  have hdescent : baseEnd_3589305 < baseStart_3589305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589325 : List Nat := [1, 6, 2, 2, 2, 10]
def baseStart_3589325 : Nat := 118140960795 + 3589325 * 2 ^ 59
def prefixEnd_3589325 : Nat := 4983230072969 + 3 ^ 40 * 3589325 * 2
def baseEnd_3589325 : Nat := 7584563581066973181607

theorem tailTrace_3589325 : CollatzResearch.WordTrace tailWord_3589325 prefixEnd_3589325 7584563581066973181607 := by
  unfold tailWord_3589325
  simp only [CollatzResearch.WordTrace]
  refine ⟨130913437721496007751057429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87275625147664005167371619 130913437721496007751057429)
  ·
    refine ⟨6136567393195125363330817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130913437721496007751057429 6136567393195125363330817)
    ·
      refine ⟨4602425544896344022498113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136567393195125363330817 4602425544896344022498113)
      ·
        refine ⟨3451819158672258016873585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4602425544896344022498113 3451819158672258016873585)
        ·
          refine ⟨2588864369004193512655189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3451819158672258016873585 2588864369004193512655189)
          ·
            refine ⟨7584563581066973181607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2588864369004193512655189 7584563581066973181607)
            ·
              rfl

theorem cell23_3589325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 10].length) (baseStart_3589325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589325 prefixEnd_3589325 := by exact prefixLift 3589325
  have htrace : WordTrace (prefixWord ++ tailWord_3589325) baseStart_3589325 baseEnd_3589325 := by
    simpa [prefixWord, tailWord_3589325, baseEnd_3589325] using wordTrace_append hprefix tailTrace_3589325
  have hstable : (prefixWord ++ tailWord_3589325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589325).length < 2 ^ (prefixWord ++ tailWord_3589325).sum := by decide
  have hdescent : baseEnd_3589325 < baseStart_3589325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589336 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_3589336 : Nat := 118140960795 + 3589336 * 2 ^ 59
def prefixEnd_3589336 : Nat := 4983230072969 + 3 ^ 40 * 3589336 * 2
def baseEnd_3589336 : Nat := 1843054598486473940092951

theorem tailTrace_3589336 : CollatzResearch.WordTrace tailWord_3589336 prefixEnd_3589336 1843054598486473940092951 := by
  unfold tailWord_3589336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65456919462228078314853931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87275892616304104419805241 65456919462228078314853931)
  ·
    refine ⟨98185379193342117472280897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65456919462228078314853931 98185379193342117472280897)
    ·
      refine ⟨73639034395006588104210673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98185379193342117472280897 73639034395006588104210673)
      ·
        refine ⟨55229275796254941078158005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73639034395006588104210673 55229275796254941078158005)
        ·
          refine ⟨5177744605898900726077313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55229275796254941078158005 5177744605898900726077313)
          ·
            refine ⟨3883308454424175544557985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5177744605898900726077313 3883308454424175544557985)
            ·
              refine ⟨2912481340818131658418489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883308454424175544557985 2912481340818131658418489)
              ·
                refine ⟨2184361005613598743813867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912481340818131658418489 2184361005613598743813867)
                ·
                  refine ⟨3276541508420398115720801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184361005613598743813867 3276541508420398115720801)
                  ·
                    refine ⟨2457406131315298586790601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276541508420398115720801 2457406131315298586790601)
                    ·
                      refine ⟨1843054598486473940092951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457406131315298586790601 1843054598486473940092951)
                      ·
                        rfl

theorem cell23_3589336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_3589336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589336 prefixEnd_3589336 := by exact prefixLift 3589336
  have htrace : WordTrace (prefixWord ++ tailWord_3589336) baseStart_3589336 baseEnd_3589336 := by
    simpa [prefixWord, tailWord_3589336, baseEnd_3589336] using wordTrace_append hprefix tailTrace_3589336
  have hstable : (prefixWord ++ tailWord_3589336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589336).length < 2 ^ (prefixWord ++ tailWord_3589336).sum := by decide
  have hdescent : baseEnd_3589336 < baseStart_3589336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589361 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3589361 : Nat := 118140960795 + 3589361 * 2 ^ 59
def prefixEnd_3589361 : Nat := 4983230072969 + 3 ^ 40 * 3589361 * 2
def baseEnd_3589361 : Nat := 1843067435502836342280335

theorem tailTrace_3589361 : CollatzResearch.WordTrace tailWord_3589361 prefixEnd_3589361 1843067435502836342280335 := by
  unfold tailWord_3589361
  simp only [CollatzResearch.WordTrace]
  refine ⟨130914750749365585899367937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87276500499577057266245291 130914750749365585899367937)
  ·
    refine ⟨98186063062024189424525953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130914750749365585899367937 98186063062024189424525953)
    ·
      refine ⟨73639547296518142068394465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98186063062024189424525953 73639547296518142068394465)
      ·
        refine ⟨55229660472388606551295849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73639547296518142068394465 55229660472388606551295849)
        ·
          refine ⟨41422245354291454913471887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55229660472388606551295849 41422245354291454913471887)
          ·
            refine ⟨62133368031437182370207831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41422245354291454913471887 62133368031437182370207831)
            ·
              refine ⟨93200052047155773555311747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62133368031437182370207831 93200052047155773555311747)
              ·
                refine ⟨139800078070733660332967621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93200052047155773555311747 139800078070733660332967621)
                ·
                  refine ⟨26212514638262561312431429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139800078070733660332967621 26212514638262561312431429)
                  ·
                    refine ⟨4914846494674230246080893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26212514638262561312431429 4914846494674230246080893)
                    ·
                      refine ⟨1843067435502836342280335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4914846494674230246080893 1843067435502836342280335)
                      ·
                        rfl

theorem cell23_3589361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3589361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589361 prefixEnd_3589361 := by exact prefixLift 3589361
  have htrace : WordTrace (prefixWord ++ tailWord_3589361) baseStart_3589361 baseEnd_3589361 := by
    simpa [prefixWord, tailWord_3589361, baseEnd_3589361] using wordTrace_append hprefix tailTrace_3589361
  have hstable : (prefixWord ++ tailWord_3589361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589361).length < 2 ^ (prefixWord ++ tailWord_3589361).sum := by decide
  have hdescent : baseEnd_3589361 < baseStart_3589361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589411 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 7]
def baseStart_3589411 : Nat := 118140960795 + 3589411 * 2 ^ 59
def prefixEnd_3589411 : Nat := 4983230072969 + 3 ^ 40 * 3589411 * 2
def baseEnd_3589411 : Nat := 614364369845187048885035

theorem tailTrace_3589411 : CollatzResearch.WordTrace tailWord_3589411 prefixEnd_3589411 614364369845187048885035 := by
  unfold tailWord_3589411
  simp only [CollatzResearch.WordTrace]
  refine ⟨130916574399184444438688087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87277716266122962959125391 130916574399184444438688087)
  ·
    refine ⟨196374861598776666658032131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130916574399184444438688087 196374861598776666658032131)
    ·
      refine ⟨294562292398164999987048197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196374861598776666658032131 294562292398164999987048197)
      ·
        refine ⟨55230429824655937497571537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294562292398164999987048197 55230429824655937497571537)
        ·
          refine ⟨41422822368491953123178653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55230429824655937497571537 41422822368491953123178653)
          ·
            refine ⟨15533558388184482421191995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41422822368491953123178653 15533558388184482421191995)
            ·
              refine ⟨23300337582276723631787993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533558388184482421191995 23300337582276723631787993)
              ·
                refine ⟨17475253186707542723840995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23300337582276723631787993 17475253186707542723840995)
                ·
                  refine ⟨26212879780061314085761493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17475253186707542723840995 26212879780061314085761493)
                  ·
                    refine ⟨614364369845187048885035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26212879780061314085761493 614364369845187048885035)
                    ·
                      rfl

theorem cell23_3589411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_3589411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589411 prefixEnd_3589411 := by exact prefixLift 3589411
  have htrace : WordTrace (prefixWord ++ tailWord_3589411) baseStart_3589411 baseEnd_3589411 := by
    simpa [prefixWord, tailWord_3589411, baseEnd_3589411] using wordTrace_append hprefix tailTrace_3589411
  have hstable : (prefixWord ++ tailWord_3589411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589411).length < 2 ^ (prefixWord ++ tailWord_3589411).sum := by decide
  have hdescent : baseEnd_3589411 < baseStart_3589411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589428 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3589428 : Nat := 118140960795 + 3589428 * 2 ^ 59
def prefixEnd_3589428 : Nat := 4983230072969 + 3 ^ 40 * 3589428 * 2
def baseEnd_3589428 : Nat := 614367279568895860047509

theorem tailTrace_3589428 : CollatzResearch.WordTrace tailWord_3589428 prefixEnd_3589428 614367279568895860047509 := by
  unfold tailWord_3589428
  simp only [CollatzResearch.WordTrace]
  refine ⟨65458597220061428171028469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87278129626748570894704625 65458597220061428171028469)
  ·
    refine ⟨6136743489380758891033919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65458597220061428171028469 6136743489380758891033919)
    ·
      refine ⟨9205115234071138336550879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136743489380758891033919 9205115234071138336550879)
      ·
        refine ⟨13807672851106707504826319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205115234071138336550879 13807672851106707504826319)
        ·
          refine ⟨20711509276660061257239479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807672851106707504826319 20711509276660061257239479)
          ·
            refine ⟨31067263914990091885859219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20711509276660061257239479 31067263914990091885859219)
            ·
              refine ⟨46600895872485137828788829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31067263914990091885859219 46600895872485137828788829)
              ·
                refine ⟨17475335952181926685795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46600895872485137828788829 17475335952181926685795811)
                ·
                  refine ⟨26213003928272890028693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17475335952181926685795811 26213003928272890028693717)
                  ·
                    refine ⟨614367279568895860047509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26213003928272890028693717 614367279568895860047509)
                    ·
                      rfl

theorem cell23_3589428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3589428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589428 prefixEnd_3589428 := by exact prefixLift 3589428
  have htrace : WordTrace (prefixWord ++ tailWord_3589428) baseStart_3589428 baseEnd_3589428 := by
    simpa [prefixWord, tailWord_3589428, baseEnd_3589428] using wordTrace_append hprefix tailTrace_3589428
  have hstable : (prefixWord ++ tailWord_3589428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589428).length < 2 ^ (prefixWord ++ tailWord_3589428).sum := by decide
  have hdescent : baseEnd_3589428 < baseStart_3589428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589438 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3589438 : Nat := 118140960795 + 3589438 * 2 ^ 59
def prefixEnd_3589438 : Nat := 4983230072969 + 3 ^ 40 * 3589438 * 2
def baseEnd_3589438 : Nat := 1843106973513232541017481

theorem tailTrace_3589438 : CollatzResearch.WordTrace tailWord_3589438 prefixEnd_3589438 1843106973513232541017481 := by
  unfold tailWord_3589438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364694896260828506240121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87278372780057752033280645 16364694896260828506240121)
  ·
    refine ⟨12273521172195621379680091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16364694896260828506240121 12273521172195621379680091)
    ·
      refine ⟨18410281758293432069520137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12273521172195621379680091 18410281758293432069520137)
      ·
        refine ⟨13807711318720074052140103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18410281758293432069520137 13807711318720074052140103)
        ·
          refine ⟨20711566978080111078210155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807711318720074052140103 20711566978080111078210155)
          ·
            refine ⟨31067350467120166617315233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20711566978080111078210155 31067350467120166617315233)
            ·
              refine ⟨23300512850340124962986425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31067350467120166617315233 23300512850340124962986425)
              ·
                refine ⟨17475384637755093722239819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23300512850340124962986425 17475384637755093722239819)
                ·
                  refine ⟨26213076956632640583359729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17475384637755093722239819 26213076956632640583359729)
                  ·
                    refine ⟨19659807717474480437519797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26213076956632640583359729 19659807717474480437519797)
                    ·
                      refine ⟨1843106973513232541017481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19659807717474480437519797 1843106973513232541017481)
                      ·
                        rfl

theorem cell23_3589438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3589438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589438 prefixEnd_3589438 := by exact prefixLift 3589438
  have htrace : WordTrace (prefixWord ++ tailWord_3589438) baseStart_3589438 baseEnd_3589438 := by
    simpa [prefixWord, tailWord_3589438, baseEnd_3589438] using wordTrace_append hprefix tailTrace_3589438
  have hstable : (prefixWord ++ tailWord_3589438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589438).length < 2 ^ (prefixWord ++ tailWord_3589438).sum := by decide
  have hdescent : baseEnd_3589438 < baseStart_3589438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589482 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3589482 : Nat := 118140960795 + 3589482 * 2 ^ 59
def prefixEnd_3589482 : Nat := 4983230072969 + 3 ^ 40 * 3589482 * 2
def baseEnd_3589482 : Nat := 1843129566662030368867279

theorem tailTrace_3589482 : CollatzResearch.WordTrace tailWord_3589482 prefixEnd_3589482 1843129566662030368867279 := by
  unfold tailWord_3589482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729790995481805891130675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87279442654618149043015133 32729790995481805891130675)
  ·
    refine ⟨49094686493222708836696013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32729790995481805891130675 49094686493222708836696013)
    ·
      refine ⟨18410507434958515813761005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49094686493222708836696013 18410507434958515813761005)
      ·
        refine ⟨6903940288109443430160377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18410507434958515813761005 6903940288109443430160377)
        ·
          refine ⟨5177955216082082572620283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903940288109443430160377 5177955216082082572620283)
          ·
            refine ⟨7766932824123123858930425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177955216082082572620283 7766932824123123858930425)
            ·
              refine ⟨5825199618092342894197819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7766932824123123858930425 5825199618092342894197819)
              ·
                refine ⟨8737799427138514341296729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825199618092342894197819 8737799427138514341296729)
                ·
                  refine ⟨6553349570353885755972547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8737799427138514341296729 6553349570353885755972547)
                  ·
                    refine ⟨9830024355530828633958821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553349570353885755972547 9830024355530828633958821)
                    ·
                      refine ⟨1843129566662030368867279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9830024355530828633958821 1843129566662030368867279)
                      ·
                        rfl

theorem cell23_3589482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3589482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589482 prefixEnd_3589482 := by exact prefixLift 3589482
  have htrace : WordTrace (prefixWord ++ tailWord_3589482) baseStart_3589482 baseEnd_3589482 := by
    simpa [prefixWord, tailWord_3589482, baseEnd_3589482] using wordTrace_append hprefix tailTrace_3589482
  have hstable : (prefixWord ++ tailWord_3589482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589482).length < 2 ^ (prefixWord ++ tailWord_3589482).sum := by decide
  have hdescent : baseEnd_3589482 < baseStart_3589482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589485 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3589485 : Nat := 118140960795 + 3589485 * 2 ^ 59
def prefixEnd_3589485 : Nat := 4983230072969 + 3 ^ 40 * 3589485 * 2
def baseEnd_3589485 : Nat := 1843131107103993857129765

theorem tailTrace_3589485 : CollatzResearch.WordTrace tailWord_3589485 prefixEnd_3589485 1843131107103993857129765 := by
  unfold tailWord_3589485
  simp only [CollatzResearch.WordTrace]
  refine ⟨130919273400916355076881909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87279515600610903384587939 130919273400916355076881909)
  ·
    refine ⟨12273681881335908288457679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130919273400916355076881909 12273681881335908288457679)
    ·
      refine ⟨18410522822003862432686519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12273681881335908288457679 18410522822003862432686519)
      ·
        refine ⟨27615784233005793649029779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18410522822003862432686519 27615784233005793649029779)
        ·
          refine ⟨41423676349508690473544669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27615784233005793649029779 41423676349508690473544669)
          ·
            refine ⟨15533878631065758927579251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41423676349508690473544669 15533878631065758927579251)
            ·
              refine ⟨23300817946598638391368877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533878631065758927579251 23300817946598638391368877)
              ·
                refine ⟨8737806729974489396763329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23300817946598638391368877 8737806729974489396763329)
                ·
                  refine ⟨6553355047480867047572497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8737806729974489396763329 6553355047480867047572497)
                  ·
                    refine ⟨4915016285610650285679373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6553355047480867047572497 4915016285610650285679373)
                    ·
                      refine ⟨1843131107103993857129765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915016285610650285679373 1843131107103993857129765)
                      ·
                        rfl

theorem cell23_3589485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3589485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589485 prefixEnd_3589485 := by exact prefixLift 3589485
  have htrace : WordTrace (prefixWord ++ tailWord_3589485) baseStart_3589485 baseEnd_3589485 := by
    simpa [prefixWord, tailWord_3589485, baseEnd_3589485] using wordTrace_append hprefix tailTrace_3589485
  have hstable : (prefixWord ++ tailWord_3589485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589485).length < 2 ^ (prefixWord ++ tailWord_3589485).sum := by decide
  have hdescent : baseEnd_3589485 < baseStart_3589485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589515 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 3]
def baseStart_3589515 : Nat := 118140960795 + 3589515 * 2 ^ 59
def prefixEnd_3589515 : Nat := 4983230072969 + 3 ^ 40 * 3589515 * 2
def baseEnd_3589515 : Nat := 1843146511523628739754627

theorem tailTrace_3589515 : CollatzResearch.WordTrace tailWord_3589515 prefixEnd_3589515 1843146511523628739754627 := by
  unfold tailWord_3589515
  simp only [CollatzResearch.WordTrace]
  refine ⟨130920367590807670200473999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87280245060538446800315999 130920367590807670200473999)
  ·
    refine ⟨196380551386211505300710999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130920367590807670200473999 196380551386211505300710999)
    ·
      refine ⟨294570827079317257951066499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196380551386211505300710999 294570827079317257951066499)
      ·
        refine ⟨441856240618975886926599749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294570827079317257951066499 441856240618975886926599749)
        ·
          refine ⟨82848045116057978798737453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441856240618975886926599749 82848045116057978798737453)
          ·
            refine ⟨31068016918521742049526545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82848045116057978798737453 31068016918521742049526545)
            ·
              refine ⟨23301012688891306537144909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31068016918521742049526545 23301012688891306537144909)
              ·
                refine ⟨8737879758334239951429341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23301012688891306537144909 8737879758334239951429341)
                ·
                  refine ⟨3276704909375339981786003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8737879758334239951429341 3276704909375339981786003)
                  ·
                    refine ⟨4915057364063009972679005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276704909375339981786003 4915057364063009972679005)
                    ·
                      refine ⟨1843146511523628739754627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915057364063009972679005 1843146511523628739754627)
                      ·
                        rfl

theorem cell23_3589515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 3].length) (baseStart_3589515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589515 prefixEnd_3589515 := by exact prefixLift 3589515
  have htrace : WordTrace (prefixWord ++ tailWord_3589515) baseStart_3589515 baseEnd_3589515 := by
    simpa [prefixWord, tailWord_3589515, baseEnd_3589515] using wordTrace_append hprefix tailTrace_3589515
  have hstable : (prefixWord ++ tailWord_3589515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589515).length < 2 ^ (prefixWord ++ tailWord_3589515).sum := by decide
  have hdescent : baseEnd_3589515 < baseStart_3589515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589525 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_3589525 : Nat := 118140960795 + 3589525 * 2 ^ 59
def prefixEnd_3589525 : Nat := 4983230072969 + 3 ^ 40 * 3589525 * 2
def baseEnd_3589525 : Nat := 1843151646330173700629581

theorem tailTrace_3589525 : CollatzResearch.WordTrace tailWord_3589525 prefixEnd_3589525 1843151646330173700629581 := by
  unfold tailWord_3589525
  simp only [CollatzResearch.WordTrace]
  refine ⟨130920732320771441908338029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87280488213847627938892019 130920732320771441908338029)
  ·
    refine ⟨49095274620289290715626761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130920732320771441908338029 49095274620289290715626761)
    ·
      refine ⟨36821455965216968036720071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49095274620289290715626761 36821455965216968036720071)
      ·
        refine ⟨55232183947825452055080107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36821455965216968036720071 55232183947825452055080107)
        ·
          refine ⟨82848275921738178082620161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55232183947825452055080107 82848275921738178082620161)
          ·
            refine ⟨62136206941303633561965121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82848275921738178082620161 62136206941303633561965121)
            ·
              refine ⟨46602155205977725171473841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62136206941303633561965121 46602155205977725171473841)
              ·
                refine ⟨34951616404483293878605381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46602155205977725171473841 34951616404483293878605381)
                ·
                  refine ⟨6553428075840617602238509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34951616404483293878605381 6553428075840617602238509)
                  ·
                    refine ⟨2457535528440231600839441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6553428075840617602238509 2457535528440231600839441)
                    ·
                      refine ⟨1843151646330173700629581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457535528440231600839441 1843151646330173700629581)
                      ·
                        rfl

theorem cell23_3589525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_3589525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589525 prefixEnd_3589525 := by exact prefixLift 3589525
  have htrace : WordTrace (prefixWord ++ tailWord_3589525) baseStart_3589525 baseEnd_3589525 := by
    simpa [prefixWord, tailWord_3589525, baseEnd_3589525] using wordTrace_append hprefix tailTrace_3589525
  have hstable : (prefixWord ++ tailWord_3589525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589525).length < 2 ^ (prefixWord ++ tailWord_3589525).sum := by decide
  have hdescent : baseEnd_3589525 < baseStart_3589525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589548 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_3589548 : Nat := 118140960795 + 3589548 * 2 ^ 59
def prefixEnd_3589548 : Nat := 4983230072969 + 3 ^ 40 * 3589548 * 2
def baseEnd_3589548 : Nat := 614387818795075703547325

theorem tailTrace_3589548 : CollatzResearch.WordTrace tailWord_3589548 prefixEnd_3589548 614387818795075703547325 := by
  unfold tailWord_3589548
  simp only [CollatzResearch.WordTrace]
  refine ⟨65460785599844058418212649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87281047466458744557616865 65460785599844058418212649)
  ·
    refine ⟨49095589199883043813659487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65460785599844058418212649 49095589199883043813659487)
    ·
      refine ⟨73643383799824565720489231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49095589199883043813659487 73643383799824565720489231)
      ·
        refine ⟨110465075699736848580733847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73643383799824565720489231 110465075699736848580733847)
        ·
          refine ⟨165697613549605272871100771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110465075699736848580733847 165697613549605272871100771)
          ·
            refine ⟨248546420324407909306651157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165697613549605272871100771 248546420324407909306651157)
            ·
              refine ⟨11650613452706620748749273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248546420324407909306651157 11650613452706620748749273)
              ·
                refine ⟨8737960089529965561561955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11650613452706620748749273 8737960089529965561561955)
                ·
                  refine ⟨13106940134294948342342933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737960089529965561561955 13106940134294948342342933)
                  ·
                    refine ⟨614387818795075703547325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13106940134294948342342933 614387818795075703547325)
                    ·
                      rfl

theorem cell23_3589548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_3589548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589548 prefixEnd_3589548 := by exact prefixLift 3589548
  have htrace : WordTrace (prefixWord ++ tailWord_3589548) baseStart_3589548 baseEnd_3589548 := by
    simpa [prefixWord, tailWord_3589548, baseEnd_3589548] using wordTrace_append hprefix tailTrace_3589548
  have hstable : (prefixWord ++ tailWord_3589548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589548).length < 2 ^ (prefixWord ++ tailWord_3589548).sum := by decide
  have hdescent : baseEnd_3589548 < baseStart_3589548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589565 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_3589565 : Nat := 118140960795 + 3589565 * 2 ^ 59
def prefixEnd_3589565 : Nat := 4983230072969 + 3 ^ 40 * 3589565 * 2
def baseEnd_3589565 : Nat := 614390728518784514709799

theorem tailTrace_3589565 : CollatzResearch.WordTrace tailWord_3589565 prefixEnd_3589565 614390728518784514709799 := by
  unfold tailWord_3589565
  simp only [CollatzResearch.WordTrace]
  refine ⟨130922191240626528739794149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87281460827084352493196099 130922191240626528739794149)
  ·
    refine ⟨24547910857617474138711403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130922191240626528739794149 24547910857617474138711403)
    ·
      refine ⟨36821866286426211208067105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24547910857617474138711403 36821866286426211208067105)
      ·
        refine ⟨27616399714819658406050329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36821866286426211208067105 27616399714819658406050329)
        ·
          refine ⟨20712299786114743804537747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27616399714819658406050329 20712299786114743804537747)
          ·
            refine ⟨31068449679172115706806621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20712299786114743804537747 31068449679172115706806621)
            ·
              refine ⟨11650668629689543390052483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31068449679172115706806621 11650668629689543390052483)
              ·
                refine ⟨17476002944534315085078725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650668629689543390052483 17476002944534315085078725)
                ·
                  refine ⟨3276750552100184078452261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17476002944534315085078725 3276750552100184078452261)
                  ·
                    refine ⟨614390728518784514709799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3276750552100184078452261 614390728518784514709799)
                    ·
                      rfl

theorem cell23_3589565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_3589565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589565 prefixEnd_3589565 := by exact prefixLift 3589565
  have htrace : WordTrace (prefixWord ++ tailWord_3589565) baseStart_3589565 baseEnd_3589565 := by
    simpa [prefixWord, tailWord_3589565, baseEnd_3589565] using wordTrace_append hprefix tailTrace_3589565
  have hstable : (prefixWord ++ tailWord_3589565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589565).length < 2 ^ (prefixWord ++ tailWord_3589565).sum := by decide
  have hdescent : baseEnd_3589565 < baseStart_3589565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589568 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_3589568 : Nat := 118140960795 + 3589568 * 2 ^ 59
def prefixEnd_3589568 : Nat := 4983230072969 + 3 ^ 40 * 3589568 * 2
def baseEnd_3589568 : Nat := 1843173725998317032391883

theorem tailTrace_3589568 : CollatzResearch.WordTrace tailWord_3589568 prefixEnd_3589568 1843173725998317032391883 := by
  unfold tailWord_3589568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65461150329807830126076679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87281533773077106834768905 65461150329807830126076679)
  ·
    refine ⟨98191725494711745189115019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65461150329807830126076679 98191725494711745189115019)
    ·
      refine ⟨147287588242067617783672529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98191725494711745189115019 147287588242067617783672529)
      ·
        refine ⟨110465691181550713337754397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147287588242067617783672529 110465691181550713337754397)
        ·
          refine ⟨41424634193081517501657899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110465691181550713337754397 41424634193081517501657899)
          ·
            refine ⟨62136951289622276252486849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41424634193081517501657899 62136951289622276252486849)
            ·
              refine ⟨46602713467216707189365137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62136951289622276252486849 46602713467216707189365137)
              ·
                refine ⟨34952035100412530392023853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46602713467216707189365137 34952035100412530392023853)
                ·
                  refine ⟨13107013162654698897008945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34952035100412530392023853 13107013162654698897008945)
                  ·
                    refine ⟨9830259871991024172756709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13107013162654698897008945 9830259871991024172756709)
                    ·
                      refine ⟨1843173725998317032391883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9830259871991024172756709 1843173725998317032391883)
                      ·
                        rfl

theorem cell23_3589568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_3589568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589568 prefixEnd_3589568 := by exact prefixLift 3589568
  have htrace : WordTrace (prefixWord ++ tailWord_3589568) baseStart_3589568 baseEnd_3589568 := by
    simpa [prefixWord, tailWord_3589568, baseEnd_3589568] using wordTrace_append hprefix tailTrace_3589568
  have hstable : (prefixWord ++ tailWord_3589568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589568).length < 2 ^ (prefixWord ++ tailWord_3589568).sum := by decide
  have hdescent : baseEnd_3589568 < baseStart_3589568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589639 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3589639 : Nat := 118140960795 + 3589639 * 2 ^ 59
def prefixEnd_3589639 : Nat := 4983230072969 + 3 ^ 40 * 3589639 * 2
def baseEnd_3589639 : Nat := 1843210183124786254604057

theorem tailTrace_3589639 : CollatzResearch.WordTrace tailWord_3589639 prefixEnd_3589639 1843210183124786254604057 := by
  unfold tailWord_3589639
  simp only [CollatzResearch.WordTrace]
  refine ⟨130924890242358439377987971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87283260161572292918658647 130924890242358439377987971)
  ·
    refine ⟨196387335363537659066981957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130924890242358439377987971 196387335363537659066981957)
    ·
      refine ⟨36822625380663311075059117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196387335363537659066981957 36822625380663311075059117)
      ·
        refine ⟨13808484517748741653147169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36822625380663311075059117 13808484517748741653147169)
        ·
          refine ⟨10356363388311556239860377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808484517748741653147169 10356363388311556239860377)
          ·
            refine ⟨7767272541233667179895283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356363388311556239860377 7767272541233667179895283)
            ·
              refine ⟨11650908811850500769842925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767272541233667179895283 11650908811850500769842925)
              ·
                refine ⟨4369090804443937788691097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11650908811850500769842925 4369090804443937788691097)
                ·
                  refine ⟨3276818103332953341518323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369090804443937788691097 3276818103332953341518323)
                  ·
                    refine ⟨4915227154999430012277485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276818103332953341518323 4915227154999430012277485)
                    ·
                      refine ⟨1843210183124786254604057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915227154999430012277485 1843210183124786254604057)
                      ·
                        rfl

theorem cell23_3589639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3589639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589639 prefixEnd_3589639 := by exact prefixLift 3589639
  have htrace : WordTrace (prefixWord ++ tailWord_3589639) baseStart_3589639 baseEnd_3589639 := by
    simpa [prefixWord, tailWord_3589639, baseEnd_3589639] using wordTrace_append hprefix tailTrace_3589639
  have hstable : (prefixWord ++ tailWord_3589639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589639).length < 2 ^ (prefixWord ++ tailWord_3589639).sum := by decide
  have hdescent : baseEnd_3589639 < baseStart_3589639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589665 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3589665 : Nat := 118140960795 + 3589665 * 2 ^ 59
def prefixEnd_3589665 : Nat := 4983230072969 + 3 ^ 40 * 3589665 * 2
def baseEnd_3589665 : Nat := 1843223533621803152878937

theorem tailTrace_3589665 : CollatzResearch.WordTrace tailWord_3589665 prefixEnd_3589665 1843223533621803152878937 := by
  unfold tailWord_3589665
  simp only [CollatzResearch.WordTrace]
  refine ⟨130925838540264245818434449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87283892360176163878956299 130925838540264245818434449)
  ·
    refine ⟨98194378905198184363825837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130925838540264245818434449 98194378905198184363825837)
    ·
      refine ⟨36822892089449319136434689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98194378905198184363825837 36822892089449319136434689)
      ·
        refine ⟨27617169067086989352326017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36822892089449319136434689 27617169067086989352326017)
        ·
          refine ⟨20712876800315242014244513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27617169067086989352326017 20712876800315242014244513)
          ·
            refine ⟨15534657600236431510683385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20712876800315242014244513 15534657600236431510683385)
            ·
              refine ⟨11650993200177323633012539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15534657600236431510683385 11650993200177323633012539)
              ·
                refine ⟨17476489800265985449518809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650993200177323633012539 17476489800265985449518809)
                ·
                  refine ⟨13107367350199489087139107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17476489800265985449518809 13107367350199489087139107)
                  ·
                    refine ⟨19661051025299233630708661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13107367350199489087139107 19661051025299233630708661)
                    ·
                      refine ⟨1843223533621803152878937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19661051025299233630708661 1843223533621803152878937)
                      ·
                        rfl

theorem cell23_3589665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3589665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589665 prefixEnd_3589665 := by exact prefixLift 3589665
  have htrace : WordTrace (prefixWord ++ tailWord_3589665) baseStart_3589665 baseEnd_3589665 := by
    simpa [prefixWord, tailWord_3589665, baseEnd_3589665] using wordTrace_append hprefix tailTrace_3589665
  have hstable : (prefixWord ++ tailWord_3589665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589665).length < 2 ^ (prefixWord ++ tailWord_3589665).sum := by decide
  have hdescent : baseEnd_3589665 < baseStart_3589665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589692 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3589692 : Nat := 118140960795 + 3589692 * 2 ^ 59
def prefixEnd_3589692 : Nat := 4983230072969 + 3 ^ 40 * 3589692 * 2
def baseEnd_3589692 : Nat := 1843237397599474547241313

theorem tailTrace_3589692 : CollatzResearch.WordTrace tailWord_3589692 prefixEnd_3589692 1843237397599474547241313 := by
  unfold tailWord_3589692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65463411655583214714833665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87284548874110952953111553 65463411655583214714833665)
  ·
    refine ⟨49097558741687411036125249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65463411655583214714833665 49097558741687411036125249)
    ·
      refine ⟨36823169056265558277093937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49097558741687411036125249 36823169056265558277093937)
      ·
        refine ⟨27617376792199168707820453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36823169056265558277093937 27617376792199168707820453)
        ·
          refine ⟨5178258148537344132716335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27617376792199168707820453 5178258148537344132716335)
          ·
            refine ⟨7767387222806016199074503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178258148537344132716335 7767387222806016199074503)
            ·
              refine ⟨11651080834209024298611755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767387222806016199074503 11651080834209024298611755)
              ·
                refine ⟨17476621251313536447917633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11651080834209024298611755 17476621251313536447917633)
                ·
                  refine ⟨13107465938485152335938225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17476621251313536447917633 13107465938485152335938225)
                  ·
                    refine ⟨9830599453863864251953669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13107465938485152335938225 9830599453863864251953669)
                    ·
                      refine ⟨1843237397599474547241313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9830599453863864251953669 1843237397599474547241313)
                      ·
                        rfl

theorem cell23_3589692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3589692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589692 prefixEnd_3589692 := by exact prefixLift 3589692
  have htrace : WordTrace (prefixWord ++ tailWord_3589692) baseStart_3589692 baseEnd_3589692 := by
    simpa [prefixWord, tailWord_3589692, baseEnd_3589692] using wordTrace_append hprefix tailTrace_3589692
  have hstable : (prefixWord ++ tailWord_3589692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589692).length < 2 ^ (prefixWord ++ tailWord_3589692).sum := by decide
  have hdescent : baseEnd_3589692 < baseStart_3589692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589695 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_3589695 : Nat := 118140960795 + 3589695 * 2 ^ 59
def prefixEnd_3589695 : Nat := 4983230072969 + 3 ^ 40 * 3589695 * 2
def baseEnd_3589695 : Nat := 1843238938041438035503799

theorem tailTrace_3589695 : CollatzResearch.WordTrace tailWord_3589695 prefixEnd_3589695 1843238938041438035503799 := by
  unfold tailWord_3589695
  simp only [CollatzResearch.WordTrace]
  refine ⟨130926932730155560942026539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87284621820103707294684359 130926932730155560942026539)
  ·
    refine ⟨196390399095233341413039809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130926932730155560942026539 196390399095233341413039809)
    ·
      refine ⟨147292799321425006059779857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196390399095233341413039809 147292799321425006059779857)
      ·
        refine ⟨110469599491068754544834893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147292799321425006059779857 110469599491068754544834893)
        ·
          refine ⟨41426099809150782954313085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110469599491068754544834893 41426099809150782954313085)
          ·
            refine ⟨15534787428431543607867407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41426099809150782954313085 15534787428431543607867407)
            ·
              refine ⟨23302181142647315411801111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534787428431543607867407 23302181142647315411801111)
              ·
                refine ⟨34953271713970973117701667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23302181142647315411801111 34953271713970973117701667)
                ·
                  refine ⟨52429907570956459676552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34953271713970973117701667 52429907570956459676552501)
                  ·
                    refine ⟨4915303834777168094676797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52429907570956459676552501 4915303834777168094676797)
                    ·
                      refine ⟨1843238938041438035503799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915303834777168094676797 1843238938041438035503799)
                      ·
                        rfl

theorem cell23_3589695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_3589695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589695 prefixEnd_3589695 := by exact prefixLift 3589695
  have htrace : WordTrace (prefixWord ++ tailWord_3589695) baseStart_3589695 baseEnd_3589695 := by
    simpa [prefixWord, tailWord_3589695, baseEnd_3589695] using wordTrace_append hprefix tailTrace_3589695
  have hstable : (prefixWord ++ tailWord_3589695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589695).length < 2 ^ (prefixWord ++ tailWord_3589695).sum := by decide
  have hdescent : baseEnd_3589695 < baseStart_3589695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589755 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3]
def baseStart_3589755 : Nat := 118140960795 + 3589755 * 2 ^ 59
def prefixEnd_3589755 : Nat := 4983230072969 + 3 ^ 40 * 3589755 * 2
def baseEnd_3589755 : Nat := 1843269746880707800753523

theorem tailTrace_3589755 : CollatzResearch.WordTrace tailWord_3589755 prefixEnd_3589755 1843269746880707800753523 := by
  unfold tailWord_3589755
  simp only [CollatzResearch.WordTrace]
  refine ⟨130929121109938191189210719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87286080739958794126140479 130929121109938191189210719)
  ·
    refine ⟨196393681664907286783816079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130929121109938191189210719 196393681664907286783816079)
    ·
      refine ⟨294590522497360930175724119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196393681664907286783816079 294590522497360930175724119)
      ·
        refine ⟨441885783746041395263586179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294590522497360930175724119 441885783746041395263586179)
        ·
          refine ⟨662828675619062092895379269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441885783746041395263586179 662828675619062092895379269)
          ·
            refine ⟨124280376678574142417883613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 662828675619062092895379269 124280376678574142417883613)
            ·
              refine ⟨46605141254465303406706355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124280376678574142417883613 46605141254465303406706355)
              ·
                refine ⟨69907711881697955110059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46605141254465303406706355 69907711881697955110059533)
                ·
                  refine ⟨26215391955636733166272325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69907711881697955110059533 26215391955636733166272325)
                  ·
                    refine ⟨4915385991681887468676061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26215391955636733166272325 4915385991681887468676061)
                    ·
                      refine ⟨1843269746880707800753523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915385991681887468676061 1843269746880707800753523)
                      ·
                        rfl

theorem cell23_3589755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].length) (baseStart_3589755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589755 prefixEnd_3589755 := by exact prefixLift 3589755
  have htrace : WordTrace (prefixWord ++ tailWord_3589755) baseStart_3589755 baseEnd_3589755 := by
    simpa [prefixWord, tailWord_3589755, baseEnd_3589755] using wordTrace_append hprefix tailTrace_3589755
  have hstable : (prefixWord ++ tailWord_3589755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589755).length < 2 ^ (prefixWord ++ tailWord_3589755).sum := by decide
  have hdescent : baseEnd_3589755 < baseStart_3589755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589765 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3589765 : Nat := 118140960795 + 3589765 * 2 ^ 59
def prefixEnd_3589765 : Nat := 4983230072969 + 3 ^ 40 * 3589765 * 2
def baseEnd_3589765 : Nat := 1843274881687252761628477

theorem tailTrace_3589765 : CollatzResearch.WordTrace tailWord_3589765 prefixEnd_3589765 1843274881687252761628477 := by
  unfold tailWord_3589765
  simp only [CollatzResearch.WordTrace]
  refine ⟨130929485839901962897074749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87286323893267975264716499 130929485839901962897074749)
  ·
    refine ⟨49098557189963236086403031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130929485839901962897074749 49098557189963236086403031)
    ·
      refine ⟨73647835784944854129604547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49098557189963236086403031 73647835784944854129604547)
      ·
        refine ⟨110471753677417281194406821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73647835784944854129604547 110471753677417281194406821)
        ·
          refine ⟨20713453814515740223951279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110471753677417281194406821 20713453814515740223951279)
          ·
            refine ⟨31070180721773610335926919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20713453814515740223951279 31070180721773610335926919)
            ·
              refine ⟨46605271082660415503890379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31070180721773610335926919 46605271082660415503890379)
              ·
                refine ⟨69907906623990623255835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46605271082660415503890379 69907906623990623255835569)
                ·
                  refine ⟨52430929967992967441876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69907906623990623255835569 52430929967992967441876677)
                  ·
                    refine ⟨9830799368998681395351877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52430929967992967441876677 9830799368998681395351877)
                    ·
                      refine ⟨1843274881687252761628477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9830799368998681395351877 1843274881687252761628477)
                      ·
                        rfl

theorem cell23_3589765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3589765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589765 prefixEnd_3589765 := by exact prefixLift 3589765
  have htrace : WordTrace (prefixWord ++ tailWord_3589765) baseStart_3589765 baseEnd_3589765 := by
    simpa [prefixWord, tailWord_3589765, baseEnd_3589765] using wordTrace_append hprefix tailTrace_3589765
  have hstable : (prefixWord ++ tailWord_3589765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589765).length < 2 ^ (prefixWord ++ tailWord_3589765).sum := by decide
  have hdescent : baseEnd_3589765 < baseStart_3589765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589772 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3589772 : Nat := 118140960795 + 3589772 * 2 ^ 59
def prefixEnd_3589772 : Nat := 4983230072969 + 3 ^ 40 * 3589772 * 2
def baseEnd_3589772 : Nat := 1843278476051834234240945

theorem tailTrace_3589772 : CollatzResearch.WordTrace tailWord_3589772 prefixEnd_3589772 1843278476051834234240945 := by
  unfold tailWord_3589772
  simp only [CollatzResearch.WordTrace]
  refine ⟨65464870575438301546289785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87286494100584402061719713 65464870575438301546289785)
  ·
    refine ⟨49098652931578726159717339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65464870575438301546289785 49098652931578726159717339)
    ·
      refine ⟨73647979397368089239576009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49098652931578726159717339 73647979397368089239576009)
      ·
        refine ⟨55235984548026066929682007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73647979397368089239576009 55235984548026066929682007)
        ·
          refine ⟨82853976822039100394523011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55235984548026066929682007 82853976822039100394523011)
          ·
            refine ⟨124280965233058650591784517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82853976822039100394523011 124280965233058650591784517)
            ·
              refine ⟨23302680981198496985959597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124280965233058650591784517 23302680981198496985959597)
              ·
                refine ⟨8738505367949436369734849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23302680981198496985959597 8738505367949436369734849)
                ·
                  refine ⟨6553879025962077277301137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8738505367949436369734849 6553879025962077277301137)
                  ·
                    refine ⟨4915409269471557957975853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6553879025962077277301137 4915409269471557957975853)
                    ·
                      refine ⟨1843278476051834234240945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915409269471557957975853 1843278476051834234240945)
                      ·
                        rfl

theorem cell23_3589772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3589772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589772 prefixEnd_3589772 := by exact prefixLift 3589772
  have htrace : WordTrace (prefixWord ++ tailWord_3589772) baseStart_3589772 baseEnd_3589772 := by
    simpa [prefixWord, tailWord_3589772, baseEnd_3589772] using wordTrace_append hprefix tailTrace_3589772
  have hstable : (prefixWord ++ tailWord_3589772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589772).length < 2 ^ (prefixWord ++ tailWord_3589772).sum := by decide
  have hdescent : baseEnd_3589772 < baseStart_3589772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589869 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3589869 : Nat := 118140960795 + 3589869 * 2 ^ 59
def prefixEnd_3589869 : Nat := 4983230072969 + 3 ^ 40 * 3589869 * 2
def baseEnd_3589869 : Nat := 614442761225106784909333

theorem tailTrace_3589869 : CollatzResearch.WordTrace tailWord_3589869 prefixEnd_3589869 614442761225106784909333 := by
  unfold tailWord_3589869
  simp only [CollatzResearch.WordTrace]
  refine ⟨130933279031525188658860661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87288852687683459105907107 130933279031525188658860661)
  ·
    refine ⟨12274994909205486436768187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130933279031525188658860661 12274994909205486436768187)
    ·
      refine ⟨18412492363808229655152281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274994909205486436768187 18412492363808229655152281)
      ·
        refine ⟨13809369272856172241364211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18412492363808229655152281 13809369272856172241364211)
        ·
          refine ⟨20714053909284258362046317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13809369272856172241364211 20714053909284258362046317)
          ·
            refine ⟨7767770215981596885767369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20714053909284258362046317 7767770215981596885767369)
            ·
              refine ⟨5825827661986197664325527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7767770215981596885767369 5825827661986197664325527)
              ·
                refine ⟨8738741492979296496488291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825827661986197664325527 8738741492979296496488291)
                ·
                  refine ⟨13108112239468944744732437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8738741492979296496488291 13108112239468944744732437)
                  ·
                    refine ⟨614442761225106784909333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13108112239468944744732437 614442761225106784909333)
                    ·
                      rfl

theorem cell23_3589869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3589869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589869 prefixEnd_3589869 := by exact prefixLift 3589869
  have htrace : WordTrace (prefixWord ++ tailWord_3589869) baseStart_3589869 baseEnd_3589869 := by
    simpa [prefixWord, tailWord_3589869, baseEnd_3589869] using wordTrace_append hprefix tailTrace_3589869
  have hstable : (prefixWord ++ tailWord_3589869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589869).length < 2 ^ (prefixWord ++ tailWord_3589869).sum := by decide
  have hdescent : baseEnd_3589869 < baseStart_3589869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589894 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3589894 : Nat := 118140960795 + 3589894 * 2 ^ 59
def prefixEnd_3589894 : Nat := 4983230072969 + 3 ^ 40 * 3589894 * 2
def baseEnd_3589894 : Nat := 204815680076853639657265

theorem tailTrace_3589894 : CollatzResearch.WordTrace tailWord_3589894 prefixEnd_3589894 204815680076853639657265 := by
  unfold tailWord_3589894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091693464263581810266273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87289460570956411952347157 4091693464263581810266273)
  ·
    refine ⟨3068770098197686357699705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4091693464263581810266273 3068770098197686357699705)
    ·
      refine ⟨2301577573648264768274779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068770098197686357699705 2301577573648264768274779)
      ·
        refine ⟨3452366360472397152412169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301577573648264768274779 3452366360472397152412169)
        ·
          refine ⟨2589274770354297864309127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452366360472397152412169 2589274770354297864309127)
          ·
            refine ⟨3883912155531446796463691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589274770354297864309127 3883912155531446796463691)
            ·
              refine ⟨5825868233297170194695537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883912155531446796463691 5825868233297170194695537)
              ·
                refine ⟨4369401174972877646021653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5825868233297170194695537 4369401174972877646021653)
                ·
                  refine ⟨204815680076853639657265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4369401174972877646021653 204815680076853639657265)
                  ·
                    rfl

theorem cell23_3589894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3589894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589894 prefixEnd_3589894 := by exact prefixLift 3589894
  have htrace : WordTrace (prefixWord ++ tailWord_3589894) baseStart_3589894 baseEnd_3589894 := by
    simpa [prefixWord, tailWord_3589894, baseEnd_3589894] using wordTrace_append hprefix tailTrace_3589894
  have hstable : (prefixWord ++ tailWord_3589894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589894).length < 2 ^ (prefixWord ++ tailWord_3589894).sum := by decide
  have hdescent : baseEnd_3589894 < baseStart_3589894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589952 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_3589952 : Nat := 118140960795 + 3589952 * 2 ^ 59
def prefixEnd_3589952 : Nat := 4983230072969 + 3 ^ 40 * 3589952 * 2
def baseEnd_3589952 : Nat := 1843370902569643529990117

theorem tailTrace_3589952 : CollatzResearch.WordTrace tailWord_3589952 prefixEnd_3589952 1843370902569643529990117 := by
  unfold tailWord_3589952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65468153145112246917066055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87290870860149662556088073 65468153145112246917066055)
  ·
    refine ⟨98202229717668370375599083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65468153145112246917066055 98202229717668370375599083)
    ·
      refine ⟨147303344576502555563398625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98202229717668370375599083 147303344576502555563398625)
      ·
        refine ⟨110477508432376916672548969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147303344576502555563398625 110477508432376916672548969)
        ·
          refine ⟨82858131324282687504411727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110477508432376916672548969 82858131324282687504411727)
          ·
            refine ⟨124287196986424031256617591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82858131324282687504411727 124287196986424031256617591)
            ·
              refine ⟨186430795479636046884926387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124287196986424031256617591 186430795479636046884926387)
              ·
                refine ⟨279646193219454070327389581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186430795479636046884926387 279646193219454070327389581)
                ·
                  refine ⟨104867322457295276372771093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279646193219454070327389581 104867322457295276372771093)
                  ·
                    refine ⟨4915655740185716079973645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104867322457295276372771093 4915655740185716079973645)
                    ·
                      refine ⟨1843370902569643529990117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4915655740185716079973645 1843370902569643529990117)
                      ·
                        rfl

theorem cell23_3589952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_3589952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589952 prefixEnd_3589952 := by exact prefixLift 3589952
  have htrace : WordTrace (prefixWord ++ tailWord_3589952) baseStart_3589952 baseEnd_3589952 := by
    simpa [prefixWord, tailWord_3589952, baseEnd_3589952] using wordTrace_append hprefix tailTrace_3589952
  have hstable : (prefixWord ++ tailWord_3589952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589952).length < 2 ^ (prefixWord ++ tailWord_3589952).sum := by decide
  have hdescent : baseEnd_3589952 < baseStart_3589952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589983 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 2, 2, 2]
def baseStart_3589983 : Nat := 118140960795 + 3589983 * 2 ^ 59
def prefixEnd_3589983 : Nat := 4983230072969 + 3 ^ 40 * 3589983 * 2
def baseEnd_3589983 : Nat := 1843386820469932908702475

theorem tailTrace_3589983 : CollatzResearch.WordTrace tailWord_3589983 prefixEnd_3589983 1843386820469932908702475 := by
  unfold tailWord_3589983
  simp only [CollatzResearch.WordTrace]
  refine ⟨130937436953112186128510603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87291624635408124085673735 130937436953112186128510603)
  ·
    refine ⟨196406155429668279192765905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130937436953112186128510603 196406155429668279192765905)
    ·
      refine ⟨147304616572251209394574429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196406155429668279192765905 147304616572251209394574429)
      ·
        refine ⟨55239231214594203522965411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147304616572251209394574429 55239231214594203522965411)
        ·
          refine ⟨82858846821891305284448117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55239231214594203522965411 82858846821891305284448117)
          ·
            refine ⟨7768016889552309870417011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82858846821891305284448117 7768016889552309870417011)
            ·
              refine ⟨11652025334328464805625517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768016889552309870417011 11652025334328464805625517)
              ·
                refine ⟨4369509500373174302109569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652025334328464805625517 4369509500373174302109569)
                ·
                  refine ⟨3277132125279880726582177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369509500373174302109569 3277132125279880726582177)
                  ·
                    refine ⟨2457849093959910544936633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277132125279880726582177 2457849093959910544936633)
                    ·
                      refine ⟨1843386820469932908702475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457849093959910544936633 1843386820469932908702475)
                      ·
                        rfl

theorem cell23_3589983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_3589983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3589983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3589983 prefixEnd_3589983 := by exact prefixLift 3589983
  have htrace : WordTrace (prefixWord ++ tailWord_3589983) baseStart_3589983 baseEnd_3589983 := by
    simpa [prefixWord, tailWord_3589983, baseEnd_3589983] using wordTrace_append hprefix tailTrace_3589983
  have hstable : (prefixWord ++ tailWord_3589983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589983).length < 2 ^ (prefixWord ++ tailWord_3589983).sum := by decide
  have hdescent : baseEnd_3589983 < baseStart_3589983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590017 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3590017 : Nat := 118140960795 + 3590017 * 2 ^ 59
def prefixEnd_3590017 : Nat := 4983230072969 + 3 ^ 40 * 3590017 * 2
def baseEnd_3590017 : Nat := 1843404278812185775677319

theorem tailTrace_3590017 : CollatzResearch.WordTrace tailWord_3590017 prefixEnd_3590017 1843404278812185775677319 := by
  unfold tailWord_3590017
  simp only [CollatzResearch.WordTrace]
  refine ⟨130938677034989009935248305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87292451356659339956832203 130938677034989009935248305)
  ·
    refine ⟨98204007776241757451436229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130938677034989009935248305 98204007776241757451436229)
    ·
      refine ⟨18413251458045329522144293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98204007776241757451436229 18413251458045329522144293)
      ·
        refine ⟨3452484648383499285402055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18413251458045329522144293 3452484648383499285402055)
        ·
          refine ⟨5178726972575248928103083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452484648383499285402055 5178726972575248928103083)
          ·
            refine ⟨7768090458862873392154625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178726972575248928103083 7768090458862873392154625)
            ·
              refine ⟨5826067844147155044115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768090458862873392154625 5826067844147155044115969)
              ·
                refine ⟨4369550883110366283086977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826067844147155044115969 4369550883110366283086977)
                ·
                  refine ⟨3277163162332774712315233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369550883110366283086977 3277163162332774712315233)
                  ·
                    refine ⟨2457872371749581034236425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277163162332774712315233 2457872371749581034236425)
                    ·
                      refine ⟨1843404278812185775677319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457872371749581034236425 1843404278812185775677319)
                      ·
                        rfl

theorem cell23_3590017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3590017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590017 prefixEnd_3590017 := by exact prefixLift 3590017
  have htrace : WordTrace (prefixWord ++ tailWord_3590017) baseStart_3590017 baseEnd_3590017 := by
    simpa [prefixWord, tailWord_3590017, baseEnd_3590017] using wordTrace_append hprefix tailTrace_3590017
  have hstable : (prefixWord ++ tailWord_3590017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590017).length < 2 ^ (prefixWord ++ tailWord_3590017).sum := by decide
  have hdescent : baseEnd_3590017 < baseStart_3590017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590019 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 2, 5]
def baseStart_3590019 : Nat := 118140960795 + 3590019 * 2 ^ 59
def prefixEnd_3590019 : Nat := 4983230072969 + 3 ^ 40 * 3590019 * 2
def baseEnd_3590019 : Nat := 614468435257831589284103

theorem tailTrace_3590019 : CollatzResearch.WordTrace tailWord_3590019 prefixEnd_3590019 614468435257831589284103 := by
  unfold tailWord_3590019
  simp only [CollatzResearch.WordTrace]
  refine ⟨130938749980981764276821111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87292499987321176184547407 130938749980981764276821111)
  ·
    refine ⟨196408124971472646415231667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130938749980981764276821111 196408124971472646415231667)
    ·
      refine ⟨294612187457208969622847501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196408124971472646415231667 294612187457208969622847501)
      ·
        refine ⟨110479570296453363608567813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294612187457208969622847501 110479570296453363608567813)
        ·
          refine ⟨20714919430585005676606465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110479570296453363608567813 20714919430585005676606465)
          ·
            refine ⟨15536189572938754257454849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20714919430585005676606465 15536189572938754257454849)
            ·
              refine ⟨11652142179704065693091137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15536189572938754257454849 11652142179704065693091137)
              ·
                refine ⟨8739106634778049269818353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11652142179704065693091137 8739106634778049269818353)
                ·
                  refine ⟨6554329976083536952363765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739106634778049269818353 6554329976083536952363765)
                  ·
                    refine ⟨614468435257831589284103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6554329976083536952363765 614468435257831589284103)
                    ·
                      rfl

theorem cell23_3590019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].length) (baseStart_3590019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590019 prefixEnd_3590019 := by exact prefixLift 3590019
  have htrace : WordTrace (prefixWord ++ tailWord_3590019) baseStart_3590019 baseEnd_3590019 := by
    simpa [prefixWord, tailWord_3590019, baseEnd_3590019] using wordTrace_append hprefix tailTrace_3590019
  have hstable : (prefixWord ++ tailWord_3590019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590019).length < 2 ^ (prefixWord ++ tailWord_3590019).sum := by decide
  have hdescent : baseEnd_3590019 < baseStart_3590019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590069 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3590069 : Nat := 118140960795 + 3590069 * 2 ^ 59
def prefixEnd_3590069 : Nat := 4983230072969 + 3 ^ 40 * 3590069 * 2
def baseEnd_3590069 : Nat := 1843430979806219572227079

theorem tailTrace_3590069 : CollatzResearch.WordTrace tailWord_3590069 prefixEnd_3590069 1843430979806219572227079 := by
  unfold tailWord_3590069
  simp only [CollatzResearch.WordTrace]
  refine ⟨130940573630800622816141261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87293715753867081877427507 130940573630800622816141261)
  ·
    refine ⟨49102715111550233556052973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130940573630800622816141261 49102715111550233556052973)
    ·
      refine ⟨18413518166831337583519865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49102715111550233556052973 18413518166831337583519865)
      ·
        refine ⟨13810138625123503187639899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18413518166831337583519865 13810138625123503187639899)
        ·
          refine ⟨20715207937685254781459849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810138625123503187639899 20715207937685254781459849)
          ·
            refine ⟨15536405953263941086094887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20715207937685254781459849 15536405953263941086094887)
            ·
              refine ⟨23304608929895911629142331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15536405953263941086094887 23304608929895911629142331)
              ·
                refine ⟨34956913394843867443713497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23304608929895911629142331 34956913394843867443713497)
                ·
                  refine ⟨26217685046132900582785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34956913394843867443713497 26217685046132900582785123)
                  ·
                    refine ⟨39326527569199350874177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26217685046132900582785123 39326527569199350874177685)
                    ·
                      refine ⟨1843430979806219572227079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39326527569199350874177685 1843430979806219572227079)
                      ·
                        rfl

theorem cell23_3590069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3590069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590069 prefixEnd_3590069 := by exact prefixLift 3590069
  have htrace : WordTrace (prefixWord ++ tailWord_3590069) baseStart_3590069 baseEnd_3590069 := by
    simpa [prefixWord, tailWord_3590069, baseEnd_3590069] using wordTrace_append hprefix tailTrace_3590069
  have hstable : (prefixWord ++ tailWord_3590069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590069).length < 2 ^ (prefixWord ++ tailWord_3590069).sum := by decide
  have hdescent : baseEnd_3590069 < baseStart_3590069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590116 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_3590116 : Nat := 118140960795 + 3590116 * 2 ^ 59
def prefixEnd_3590116 : Nat := 4983230072969 + 3 ^ 40 * 3590116 * 2
def baseEnd_3590116 : Nat := 1843455113396980888339363

theorem tailTrace_3590116 : CollatzResearch.WordTrace tailWord_3590116 prefixEnd_3590116 1843455113396980888339363 := by
  unfold tailWord_3590116
  simp only [CollatzResearch.WordTrace]
  refine ⟨65471143930815174921551101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87294858574420233228734801 65471143930815174921551101)
  ·
    refine ⟨24551678974055690595581663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65471143930815174921551101 24551678974055690595581663)
    ·
      refine ⟨36827518461083535893372495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551678974055690595581663 36827518461083535893372495)
      ·
        refine ⟨55241277691625303840058743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36827518461083535893372495 55241277691625303840058743)
        ·
          refine ⟨82861916537437955760088115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55241277691625303840058743 82861916537437955760088115)
          ·
            refine ⟨124292874806156933640132173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82861916537437955760088115 124292874806156933640132173)
            ·
              refine ⟨46609828052308850115049565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124292874806156933640132173 46609828052308850115049565)
              ·
                refine ⟨17478685519615818793143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46609828052308850115049565 17478685519615818793143587)
                ·
                  refine ⟨26218028279423728189715381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17478685519615818793143587 26218028279423728189715381)
                  ·
                    refine ⟨2457940151195974517785817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26218028279423728189715381 2457940151195974517785817)
                    ·
                      refine ⟨1843455113396980888339363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457940151195974517785817 1843455113396980888339363)
                      ·
                        rfl

theorem cell23_3590116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_3590116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590116 prefixEnd_3590116 := by exact prefixLift 3590116
  have htrace : WordTrace (prefixWord ++ tailWord_3590116) baseStart_3590116 baseEnd_3590116 := by
    simpa [prefixWord, tailWord_3590116, baseEnd_3590116] using wordTrace_append hprefix tailTrace_3590116
  have hstable : (prefixWord ++ tailWord_3590116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590116).length < 2 ^ (prefixWord ++ tailWord_3590116).sum := by decide
  have hdescent : baseEnd_3590116 < baseStart_3590116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590163 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 3, 2, 2]
def baseStart_3590163 : Nat := 118140960795 + 3590163 * 2 ^ 59
def prefixEnd_3590163 : Nat := 4983230072969 + 3 ^ 40 * 3590163 * 2
def baseEnd_3590163 : Nat := 1843479246987742204451647

theorem tailTrace_3590163 : CollatzResearch.WordTrace tailWord_3590163 prefixEnd_3590163 1843479246987742204451647 := by
  unfold tailWord_3590163
  simp only [CollatzResearch.WordTrace]
  refine ⟨130944002092460076870063143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87296001394973384580042095 130944002092460076870063143)
  ·
    refine ⟨196416003138690115305094715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130944002092460076870063143 196416003138690115305094715)
    ·
      refine ⟨294624004708035172957642073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196416003138690115305094715 294624004708035172957642073)
      ·
        refine ⟨220968003531026379718231555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294624004708035172957642073 220968003531026379718231555)
        ·
          refine ⟨331452005296539569577347333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220968003531026379718231555 331452005296539569577347333)
          ·
            refine ⟨62147250993101169295752625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331452005296539569577347333 62147250993101169295752625)
            ·
              refine ⟨46610438244825876971814469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62147250993101169295752625 46610438244825876971814469)
              ·
                refine ⟨8739457170904851932215213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46610438244825876971814469 8739457170904851932215213)
                ·
                  refine ⟨3277296439089319474580705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8739457170904851932215213 3277296439089319474580705)
                  ·
                    refine ⟨2457972329316989605935529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277296439089319474580705 2457972329316989605935529)
                    ·
                      refine ⟨1843479246987742204451647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2457972329316989605935529 1843479246987742204451647)
                      ·
                        rfl

theorem cell23_3590163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2, 2].length) (baseStart_3590163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590163 prefixEnd_3590163 := by exact prefixLift 3590163
  have htrace : WordTrace (prefixWord ++ tailWord_3590163) baseStart_3590163 baseEnd_3590163 := by
    simpa [prefixWord, tailWord_3590163, baseEnd_3590163] using wordTrace_append hprefix tailTrace_3590163
  have hstable : (prefixWord ++ tailWord_3590163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590163).length < 2 ^ (prefixWord ++ tailWord_3590163).sum := by decide
  have hdescent : baseEnd_3590163 < baseStart_3590163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590190 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3590190 : Nat := 118140960795 + 3590190 * 2 ^ 59
def prefixEnd_3590190 : Nat := 4983230072969 + 3 ^ 40 * 3590190 * 2
def baseEnd_3590190 : Nat := 614497703655137866271341

theorem tailTrace_3590190 : CollatzResearch.WordTrace tailWord_3590190 prefixEnd_3590190 614497703655137866271341 := by
  unfold tailWord_3590190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368123357920282560162003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87296657908908173654197349 16368123357920282560162003)
  ·
    refine ⟨24552185036880423840243005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368123357920282560162003 24552185036880423840243005)
    ·
      refine ⟨9207069388830158940091127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24552185036880423840243005 9207069388830158940091127)
      ·
        refine ⟨13810604083245238410136691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207069388830158940091127 13810604083245238410136691)
        ·
          refine ⟨20715906124867857615205037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810604083245238410136691 20715906124867857615205037)
          ·
            refine ⟨7768464796825446605701889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20715906124867857615205037 7768464796825446605701889)
            ·
              refine ⟨5826348597619084954276417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768464796825446605701889 5826348597619084954276417)
              ·
                refine ⟨4369761448214313715707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826348597619084954276417 4369761448214313715707313)
                ·
                  refine ⟨3277321086160735286780485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369761448214313715707313 3277321086160735286780485)
                  ·
                    refine ⟨614497703655137866271341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277321086160735286780485 614497703655137866271341)
                    ·
                      rfl

theorem cell23_3590190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3590190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590190 prefixEnd_3590190 := by exact prefixLift 3590190
  have htrace : WordTrace (prefixWord ++ tailWord_3590190) baseStart_3590190 baseEnd_3590190 := by
    simpa [prefixWord, tailWord_3590190, baseEnd_3590190] using wordTrace_append hprefix tailTrace_3590190
  have hstable : (prefixWord ++ tailWord_3590190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590190).length < 2 ^ (prefixWord ++ tailWord_3590190).sum := by decide
  have hdescent : baseEnd_3590190 < baseStart_3590190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590199 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 7]
def baseStart_3590199 : Nat := 118140960795 + 3590199 * 2 ^ 59
def prefixEnd_3590199 : Nat := 4983230072969 + 3 ^ 40 * 3590199 * 2
def baseEnd_3590199 : Nat := 614499244097101354533827

theorem tailTrace_3590199 : CollatzResearch.WordTrace tailWord_3590199 prefixEnd_3590199 614499244097101354533827 := by
  unfold tailWord_3590199
  simp only [CollatzResearch.WordTrace]
  refine ⟨130945315120329655018373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87296876746886436678915767 130945315120329655018373651)
  ·
    refine ⟨196417972680494482527560477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130945315120329655018373651 196417972680494482527560477)
    ·
      refine ⟨73656739755185430947835179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196417972680494482527560477 73656739755185430947835179)
      ·
        refine ⟨110485109632778146421752769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73656739755185430947835179 110485109632778146421752769)
        ·
          refine ⟨82863832224583609816314577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110485109632778146421752769 82863832224583609816314577)
          ·
            refine ⟨62147874168437707362235933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82863832224583609816314577 62147874168437707362235933)
            ·
              refine ⟨23305452813164140260838475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62147874168437707362235933 23305452813164140260838475)
              ·
                refine ⟨34958179219746210391257713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23305452813164140260838475 34958179219746210391257713)
                ·
                  refine ⟨26218634414809657793443285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34958179219746210391257713 26218634414809657793443285)
                  ·
                    refine ⟨614499244097101354533827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26218634414809657793443285 614499244097101354533827)
                    ·
                      rfl

theorem cell23_3590199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_3590199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590199 prefixEnd_3590199 := by exact prefixLift 3590199
  have htrace : WordTrace (prefixWord ++ tailWord_3590199) baseStart_3590199 baseEnd_3590199 := by
    simpa [prefixWord, tailWord_3590199, baseEnd_3590199] using wordTrace_append hprefix tailTrace_3590199
  have hstable : (prefixWord ++ tailWord_3590199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590199).length < 2 ^ (prefixWord ++ tailWord_3590199).sum := by decide
  have hdescent : baseEnd_3590199 < baseStart_3590199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590240 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2]
def baseStart_3590240 : Nat := 118140960795 + 3590240 * 2 ^ 59
def prefixEnd_3590240 : Nat := 4983230072969 + 3 ^ 40 * 3590240 * 2
def baseEnd_3590240 : Nat := 1843518784998138403188793

theorem tailTrace_3590240 : CollatzResearch.WordTrace tailWord_3590240 prefixEnd_3590240 1843518784998138403188793 := by
  unfold tailWord_3590240
  simp only [CollatzResearch.WordTrace]
  refine ⟨65473405256590559510308087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87297873675454079347077449 65473405256590559510308087)
  ·
    refine ⟨98210107884885839265462131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65473405256590559510308087 98210107884885839265462131)
    ·
      refine ⟨147315161827328758898193197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98210107884885839265462131 147315161827328758898193197)
      ·
        refine ⟨55243185685248284586822449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147315161827328758898193197 55243185685248284586822449)
        ·
          refine ⟨41432389263936213440116837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55243185685248284586822449 41432389263936213440116837)
          ·
            refine ⟨7768572986988040020021907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41432389263936213440116837 7768572986988040020021907)
            ·
              refine ⟨11652859480482060030032861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768572986988040020021907 11652859480482060030032861)
              ·
                refine ⟨4369822305180772511262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652859480482060030032861 4369822305180772511262323)
                ·
                  refine ⟨6554733457771158766893485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369822305180772511262323 6554733457771158766893485)
                  ·
                    refine ⟨2458025046664184537585057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6554733457771158766893485 2458025046664184537585057)
                    ·
                      refine ⟨1843518784998138403188793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458025046664184537585057 1843518784998138403188793)
                      ·
                        rfl

theorem cell23_3590240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_3590240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590240 prefixEnd_3590240 := by exact prefixLift 3590240
  have htrace : WordTrace (prefixWord ++ tailWord_3590240) baseStart_3590240 baseEnd_3590240 := by
    simpa [prefixWord, tailWord_3590240, baseEnd_3590240] using wordTrace_append hprefix tailTrace_3590240
  have hstable : (prefixWord ++ tailWord_3590240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590240).length < 2 ^ (prefixWord ++ tailWord_3590240).sum := by decide
  have hdescent : baseEnd_3590240 < baseStart_3590240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590276 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 7]
def baseStart_3590276 : Nat := 118140960795 + 3590276 * 2 ^ 59
def prefixEnd_3590276 : Nat := 4983230072969 + 3 ^ 40 * 3590276 * 2
def baseEnd_3590276 : Nat := 204837474477966695815403

theorem tailTrace_3590276 : CollatzResearch.WordTrace tailWord_3590276 prefixEnd_3590276 204837474477966695815403 := by
  unfold tailWord_3590276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65474061770525348584463341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87298749027367131445951121 65474061770525348584463341)
  ·
    refine ⟨24552773163947005719173753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65474061770525348584463341 24552773163947005719173753)
    ·
      refine ⟨18414579872960254289380315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24552773163947005719173753 18414579872960254289380315)
      ·
        refine ⟨27621869809440381434070473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414579872960254289380315 27621869809440381434070473)
        ·
          refine ⟨20716402357080286075552855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27621869809440381434070473 20716402357080286075552855)
          ·
            refine ⟨31074603535620429113329283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20716402357080286075552855 31074603535620429113329283)
            ·
              refine ⟨46611905303430643669993925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31074603535620429113329283 46611905303430643669993925)
              ·
                refine ⟨8739732244393245688123861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46611905303430643669993925 8739732244393245688123861)
                ·
                  refine ⟨204837474477966695815403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8739732244393245688123861 204837474477966695815403)
                  ·
                    rfl

theorem cell23_3590276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_3590276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590276 prefixEnd_3590276 := by exact prefixLift 3590276
  have htrace : WordTrace (prefixWord ++ tailWord_3590276) baseStart_3590276 baseEnd_3590276 := by
    simpa [prefixWord, tailWord_3590276, baseEnd_3590276] using wordTrace_append hprefix tailTrace_3590276
  have hstable : (prefixWord ++ tailWord_3590276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590276).length < 2 ^ (prefixWord ++ tailWord_3590276).sum := by decide
  have hdescent : baseEnd_3590276 < baseStart_3590276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590321 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3590321 : Nat := 118140960795 + 3590321 * 2 ^ 59
def prefixEnd_3590321 : Nat := 4983230072969 + 3 ^ 40 * 3590321 * 2
def baseEnd_3590321 : Nat := 1843560376931152586275921

theorem tailTrace_3590321 : CollatzResearch.WordTrace tailWord_3590321 prefixEnd_3590321 1843560376931152586275921 := by
  unfold tailWord_3590321
  simp only [CollatzResearch.WordTrace]
  refine ⟨130949764825887669854314817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87299843217258446569543211 130949764825887669854314817)
  ·
    refine ⟨98212323619415752390736113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130949764825887669854314817 98212323619415752390736113)
    ·
      refine ⟨73659242714561814293052085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98212323619415752390736113 73659242714561814293052085)
      ·
        refine ⟨6905554004490170089973633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73659242714561814293052085 6905554004490170089973633)
        ·
          refine ⟨5179165503367627567480225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905554004490170089973633 5179165503367627567480225)
          ·
            refine ⟨3884374127525720675610169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179165503367627567480225 3884374127525720675610169)
            ·
              refine ⟨2913280595644290506707627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884374127525720675610169 2913280595644290506707627)
              ·
                refine ⟨4369920893466435760061441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913280595644290506707627 4369920893466435760061441)
                ·
                  refine ⟨3277440670099826820046081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369920893466435760061441 3277440670099826820046081)
                  ·
                    refine ⟨2458080502574870115034561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277440670099826820046081 2458080502574870115034561)
                    ·
                      refine ⟨1843560376931152586275921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458080502574870115034561 1843560376931152586275921)
                      ·
                        rfl

theorem cell23_3590321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3590321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590321 prefixEnd_3590321 := by exact prefixLift 3590321
  have htrace : WordTrace (prefixWord ++ tailWord_3590321) baseStart_3590321 baseEnd_3590321 := by
    simpa [prefixWord, tailWord_3590321, baseEnd_3590321] using wordTrace_append hprefix tailTrace_3590321
  have hstable : (prefixWord ++ tailWord_3590321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590321).length < 2 ^ (prefixWord ++ tailWord_3590321).sum := by decide
  have hdescent : baseEnd_3590321 < baseStart_3590321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590340 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3590340 : Nat := 118140960795 + 3590340 * 2 ^ 59
def prefixEnd_3590340 : Nat := 4983230072969 + 3 ^ 40 * 3590340 * 2
def baseEnd_3590340 : Nat := 614523377687862670646111

theorem tailTrace_3590340 : CollatzResearch.WordTrace tailWord_3590340 prefixEnd_3590340 614523377687862670646111 := by
  unfold tailWord_3590340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65475228906409418049628237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87300305208545890732837649 65475228906409418049628237)
  ·
    refine ⟨24553210839903531768610589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65475228906409418049628237 24553210839903531768610589)
    ·
      refine ⟨9207454064963824413228971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24553210839903531768610589 9207454064963824413228971)
      ·
        refine ⟨13811181097445736619843457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207454064963824413228971 13811181097445736619843457)
        ·
          refine ⟨10358385823084302464882593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811181097445736619843457 10358385823084302464882593)
          ·
            refine ⟨7768789367313226848661945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10358385823084302464882593 7768789367313226848661945)
            ·
              refine ⟨5826592025484920136496459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768789367313226848661945 5826592025484920136496459)
              ·
                refine ⟨8739888038227380204744689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826592025484920136496459 8739888038227380204744689)
                ·
                  refine ⟨6554916028670535153558517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739888038227380204744689 6554916028670535153558517)
                  ·
                    refine ⟨614523377687862670646111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6554916028670535153558517 614523377687862670646111)
                    ·
                      rfl

theorem cell23_3590340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3590340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590340 prefixEnd_3590340 := by exact prefixLift 3590340
  have htrace : WordTrace (prefixWord ++ tailWord_3590340) baseStart_3590340 baseEnd_3590340 := by
    simpa [prefixWord, tailWord_3590340, baseEnd_3590340] using wordTrace_append hprefix tailTrace_3590340
  have hstable : (prefixWord ++ tailWord_3590340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590340).length < 2 ^ (prefixWord ++ tailWord_3590340).sum := by decide
  have hdescent : baseEnd_3590340 < baseStart_3590340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590343 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_3590343 : Nat := 118140960795 + 3590343 * 2 ^ 59
def prefixEnd_3590343 : Nat := 4983230072969 + 3 ^ 40 * 3590343 * 2
def baseEnd_3590343 : Nat := 1843571673505551500200819

theorem tailTrace_3590343 : CollatzResearch.WordTrace tailWord_3590343 prefixEnd_3590343 1843571673505551500200819 := by
  unfold tailWord_3590343
  simp only [CollatzResearch.WordTrace]
  refine ⟨130950567231807967611615683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87300378154538645074410455 130950567231807967611615683)
  ·
    refine ⟨196425850847711951417423525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130950567231807967611615683 196425850847711951417423525)
    ·
      refine ⟨36829847033945990890766911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196425850847711951417423525 36829847033945990890766911)
      ·
        refine ⟨55244770550918986336150367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36829847033945990890766911 55244770550918986336150367)
        ·
          refine ⟨82867155826378479504225551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55244770550918986336150367 82867155826378479504225551)
          ·
            refine ⟨124300733739567719256338327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82867155826378479504225551 124300733739567719256338327)
            ·
              refine ⟨186451100609351578884507491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124300733739567719256338327 186451100609351578884507491)
              ·
                refine ⟨279676650914027368326761237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186451100609351578884507491 279676650914027368326761237)
                ·
                  refine ⟨13109843011595032890316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279676650914027368326761237 13109843011595032890316933)
                  ·
                    refine ⟨2458095564674068666934425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13109843011595032890316933 2458095564674068666934425)
                    ·
                      refine ⟨1843571673505551500200819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458095564674068666934425 1843571673505551500200819)
                      ·
                        rfl

theorem cell23_3590343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_3590343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590343 prefixEnd_3590343 := by exact prefixLift 3590343
  have htrace : WordTrace (prefixWord ++ tailWord_3590343) baseStart_3590343 baseEnd_3590343 := by
    simpa [prefixWord, tailWord_3590343, baseEnd_3590343] using wordTrace_append hprefix tailTrace_3590343
  have hstable : (prefixWord ++ tailWord_3590343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590343).length < 2 ^ (prefixWord ++ tailWord_3590343).sum := by decide
  have hdescent : baseEnd_3590343 < baseStart_3590343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590383 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 6]
def baseStart_3590383 : Nat := 118140960795 + 3590383 * 2 ^ 59
def prefixEnd_3590383 : Nat := 4983230072969 + 3 ^ 40 * 3590383 * 2
def baseEnd_3590383 : Nat := 204843579192414593744515

theorem tailTrace_3590383 : CollatzResearch.WordTrace tailWord_3590383 prefixEnd_3590383 204843579192414593744515 := by
  unfold tailWord_3590383
  simp only [CollatzResearch.WordTrace]
  refine ⟨130952026151663054443071803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87301350767775369628714535 130952026151663054443071803)
  ·
    refine ⟨196428039227494581664607705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130952026151663054443071803 196428039227494581664607705)
    ·
      refine ⟨147321029420620936248455779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196428039227494581664607705 147321029420620936248455779)
      ·
        refine ⟨220981544130931404372683669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147321029420620936248455779 220981544130931404372683669)
        ·
          refine ⟨10358509881137409579969547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220981544130931404372683669 10358509881137409579969547)
          ·
            refine ⟨15537764821706114369954321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358509881137409579969547 15537764821706114369954321)
            ·
              refine ⟨11653323616279585777465741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15537764821706114369954321 11653323616279585777465741)
              ·
                refine ⟨4369996356104844666549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11653323616279585777465741 4369996356104844666549653)
                ·
                  refine ⟨204843579192414593744515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4369996356104844666549653 204843579192414593744515)
                  ·
                    rfl

theorem cell23_3590383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 6].length) (baseStart_3590383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590383 prefixEnd_3590383 := by exact prefixLift 3590383
  have htrace : WordTrace (prefixWord ++ tailWord_3590383) baseStart_3590383 baseEnd_3590383 := by
    simpa [prefixWord, tailWord_3590383, baseEnd_3590383] using wordTrace_append hprefix tailTrace_3590383
  have hstable : (prefixWord ++ tailWord_3590383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590383).length < 2 ^ (prefixWord ++ tailWord_3590383).sum := by decide
  have hdescent : baseEnd_3590383 < baseStart_3590383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590404 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_3590404 : Nat := 118140960795 + 3590404 * 2 ^ 59
def prefixEnd_3590404 : Nat := 4983230072969 + 3 ^ 40 * 3590404 * 2
def baseEnd_3590404 : Nat := 614534331941825253846013

theorem tailTrace_3590404 : CollatzResearch.WordTrace tailWord_3590404 prefixEnd_3590404 614534331941825253846013 := by
  unfold tailWord_3590404
  simp only [CollatzResearch.WordTrace]
  refine ⟨65476396042293487514793133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87301861389724650019724177 65476396042293487514793133)
  ·
    refine ⟨24553648515860057818047425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65476396042293487514793133 24553648515860057818047425)
    ·
      refine ⟨18415236386895043363535569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24553648515860057818047425 18415236386895043363535569)
      ·
        refine ⟨13811427290171282522651677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18415236386895043363535569 13811427290171282522651677)
        ·
          refine ⟨5179285233814230945994379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13811427290171282522651677 5179285233814230945994379)
          ·
            refine ⟨7768927850721346418991569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179285233814230945994379 7768927850721346418991569)
            ·
              refine ⟨5826695888041009814243677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768927850721346418991569 5826695888041009814243677)
              ·
                refine ⟨2185010958015378680341379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5826695888041009814243677 2185010958015378680341379)
                ·
                  refine ⟨3277516437023068020512069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185010958015378680341379 3277516437023068020512069)
                  ·
                    refine ⟨614534331941825253846013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277516437023068020512069 614534331941825253846013)
                    ·
                      rfl

theorem cell23_3590404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_3590404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590404 prefixEnd_3590404 := by exact prefixLift 3590404
  have htrace : WordTrace (prefixWord ++ tailWord_3590404) baseStart_3590404 baseEnd_3590404 := by
    simpa [prefixWord, tailWord_3590404, baseEnd_3590404] using wordTrace_append hprefix tailTrace_3590404
  have hstable : (prefixWord ++ tailWord_3590404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590404).length < 2 ^ (prefixWord ++ tailWord_3590404).sum := by decide
  have hdescent : baseEnd_3590404 < baseStart_3590404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590427 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 1, 1, 3]
def baseStart_3590427 : Nat := 118140960795 + 3590427 * 2 ^ 59
def prefixEnd_3590427 : Nat := 4983230072969 + 3 ^ 40 * 3590427 * 2
def baseEnd_3590427 : Nat := 1843614805880529171550433

theorem tailTrace_3590427 : CollatzResearch.WordTrace tailWord_3590427 prefixEnd_3590427 1843614805880529171550433 := by
  unfold tailWord_3590427
  simp only [CollatzResearch.WordTrace]
  refine ⟨130953630963503649957673535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87302420642335766638449023 130953630963503649957673535)
  ·
    refine ⟨196430446445255474936510303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130953630963503649957673535 196430446445255474936510303)
    ·
      refine ⟨294645669667883212404765455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196430446445255474936510303 294645669667883212404765455)
      ·
        refine ⟨441968504501824818607148183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294645669667883212404765455 441968504501824818607148183)
        ·
          refine ⟨662952756752737227910722275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441968504501824818607148183 662952756752737227910722275)
          ·
            refine ⟨994429135129105841866083413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662952756752737227910722275 994429135129105841866083413)
            ·
              refine ⟨11653466427294209084368165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 994429135129105841866083413 11653466427294209084368165)
              ·
                refine ⟨2185024955117664203319031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11653466427294209084368165 2185024955117664203319031)
                ·
                  refine ⟨3277537432676496304978547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185024955117664203319031 3277537432676496304978547)
                  ·
                    refine ⟨4916306149014744457467821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3277537432676496304978547 4916306149014744457467821)
                    ·
                      refine ⟨1843614805880529171550433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916306149014744457467821 1843614805880529171550433)
                      ·
                        rfl

theorem cell23_3590427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 1, 3].length) (baseStart_3590427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590427 prefixEnd_3590427 := by exact prefixLift 3590427
  have htrace : WordTrace (prefixWord ++ tailWord_3590427) baseStart_3590427 baseEnd_3590427 := by
    simpa [prefixWord, tailWord_3590427, baseEnd_3590427] using wordTrace_append hprefix tailTrace_3590427
  have hstable : (prefixWord ++ tailWord_3590427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590427).length < 2 ^ (prefixWord ++ tailWord_3590427).sum := by decide
  have hdescent : baseEnd_3590427 < baseStart_3590427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590433 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3590433 : Nat := 118140960795 + 3590433 * 2 ^ 59
def prefixEnd_3590433 : Nat := 4983230072969 + 3 ^ 40 * 3590433 * 2
def baseEnd_3590433 : Nat := 1843617886764456148075405

theorem tailTrace_3590433 : CollatzResearch.WordTrace tailWord_3590433 prefixEnd_3590433 1843617886764456148075405 := by
  unfold tailWord_3590433
  simp only [CollatzResearch.WordTrace]
  refine ⟨130953849801481912982391953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87302566534321275321594635 130953849801481912982391953)
  ·
    refine ⟨98215387351111434736793965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130953849801481912982391953 98215387351111434736793965)
    ·
      refine ⟨36830770256666788026297737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98215387351111434736793965 36830770256666788026297737)
      ·
        refine ⟨27623077692500091019723303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36830770256666788026297737 27623077692500091019723303)
        ·
          refine ⟨41434616538750136529584955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27623077692500091019723303 41434616538750136529584955)
          ·
            refine ⟨62151924808125204794377433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41434616538750136529584955 62151924808125204794377433)
            ·
              refine ⟨46613943606093903595783075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62151924808125204794377433 46613943606093903595783075)
              ·
                refine ⟨69920915409140855393674613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46613943606093903595783075 69920915409140855393674613)
                ·
                  refine ⟨6555085819606955193156995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69920915409140855393674613 6555085819606955193156995)
                  ·
                    refine ⟨9832628729410432789735493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555085819606955193156995 9832628729410432789735493)
                    ·
                      refine ⟨1843617886764456148075405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9832628729410432789735493 1843617886764456148075405)
                      ·
                        rfl

theorem cell23_3590433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3590433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590433 prefixEnd_3590433 := by exact prefixLift 3590433
  have htrace : WordTrace (prefixWord ++ tailWord_3590433) baseStart_3590433 baseEnd_3590433 := by
    simpa [prefixWord, tailWord_3590433, baseEnd_3590433] using wordTrace_append hprefix tailTrace_3590433
  have hstable : (prefixWord ++ tailWord_3590433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590433).length < 2 ^ (prefixWord ++ tailWord_3590433).sum := by decide
  have hdescent : baseEnd_3590433 < baseStart_3590433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590453 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3590453 : Nat := 118140960795 + 3590453 * 2 ^ 59
def prefixEnd_3590453 : Nat := 4983230072969 + 3 ^ 40 * 3590453 * 2
def baseEnd_3590453 : Nat := 1843628156377546069825313

theorem tailTrace_3590453 : CollatzResearch.WordTrace tailWord_3590453 prefixEnd_3590453 1843628156377546069825313 := by
  unfold tailWord_3590453
  simp only [CollatzResearch.WordTrace]
  refine ⟨130954579261409456398120013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87303052840939637598746675 130954579261409456398120013)
  ·
    refine ⟨49107967223028546149295005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130954579261409456398120013 49107967223028546149295005)
    ·
      refine ⟨18415487708635704805985627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49107967223028546149295005 18415487708635704805985627)
      ·
        refine ⟨27623231562953557208978441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415487708635704805985627 27623231562953557208978441)
        ·
          refine ⟨20717423672215167906733831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27623231562953557208978441 20717423672215167906733831)
          ·
            refine ⟨31076135508322751860100747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20717423672215167906733831 31076135508322751860100747)
            ·
              refine ⟨46614203262484127790151121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31076135508322751860100747 46614203262484127790151121)
              ·
                refine ⟨34960652446863095842613341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46614203262484127790151121 34960652446863095842613341)
                ·
                  refine ⟨13110244667573660940980003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34960652446863095842613341 13110244667573660940980003)
                  ·
                    refine ⟨19665367001360491411470005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13110244667573660940980003 19665367001360491411470005)
                    ·
                      refine ⟨1843628156377546069825313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19665367001360491411470005 1843628156377546069825313)
                      ·
                        rfl

theorem cell23_3590453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3590453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590453 prefixEnd_3590453 := by exact prefixLift 3590453
  have htrace : WordTrace (prefixWord ++ tailWord_3590453) baseStart_3590453 baseEnd_3590453 := by
    simpa [prefixWord, tailWord_3590453, baseEnd_3590453] using wordTrace_append hprefix tailTrace_3590453
  have hstable : (prefixWord ++ tailWord_3590453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590453).length < 2 ^ (prefixWord ++ tailWord_3590453).sum := by decide
  have hdescent : baseEnd_3590453 < baseStart_3590453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590463 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3590463 : Nat := 118140960795 + 3590463 * 2 ^ 59
def prefixEnd_3590463 : Nat := 4983230072969 + 3 ^ 40 * 3590463 * 2
def baseEnd_3590463 : Nat := 1843633291184091030700267

theorem tailTrace_3590463 : CollatzResearch.WordTrace tailWord_3590463 prefixEnd_3590463 1843633291184091030700267 := by
  unfold tailWord_3590463
  simp only [CollatzResearch.WordTrace]
  refine ⟨130954943991373228105984043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87303295994248818737322695 130954943991373228105984043)
  ·
    refine ⟨196432415987059842158976065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130954943991373228105984043 196432415987059842158976065)
    ·
      refine ⟨147324311990294881619232049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196432415987059842158976065 147324311990294881619232049)
      ·
        refine ⟨110493233992721161214424037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147324311990294881619232049 110493233992721161214424037)
        ·
          refine ⟨20717481373635217727704507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110493233992721161214424037 20717481373635217727704507)
          ·
            refine ⟨31076222060452826591556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20717481373635217727704507 31076222060452826591556761)
            ·
              refine ⟨23307166545339619943667571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31076222060452826591556761 23307166545339619943667571)
              ·
                refine ⟨34960749818009429915501357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23307166545339619943667571 34960749818009429915501357)
                ·
                  refine ⟨13110281181753536218313009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34960749818009429915501357 13110281181753536218313009)
                  ·
                    refine ⟨9832710886315152163734757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13110281181753536218313009 9832710886315152163734757)
                    ·
                      refine ⟨1843633291184091030700267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9832710886315152163734757 1843633291184091030700267)
                      ·
                        rfl

theorem cell23_3590463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3590463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590463 prefixEnd_3590463 := by exact prefixLift 3590463
  have htrace : WordTrace (prefixWord ++ tailWord_3590463) baseStart_3590463 baseEnd_3590463 := by
    simpa [prefixWord, tailWord_3590463, baseEnd_3590463] using wordTrace_append hprefix tailTrace_3590463
  have hstable : (prefixWord ++ tailWord_3590463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590463).length < 2 ^ (prefixWord ++ tailWord_3590463).sum := by decide
  have hdescent : baseEnd_3590463 < baseStart_3590463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590483 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3]
def baseStart_3590483 : Nat := 118140960795 + 3590483 * 2 ^ 59
def prefixEnd_3590483 : Nat := 4983230072969 + 3 ^ 40 * 3590483 * 2
def baseEnd_3590483 : Nat := 1843643560797180952450175

theorem tailTrace_3590483 : CollatzResearch.WordTrace tailWord_3590483 prefixEnd_3590483 1843643560797180952450175 := by
  unfold tailWord_3590483
  simp only [CollatzResearch.WordTrace]
  refine ⟨130955673451300771521712103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87303782300867181014474735 130955673451300771521712103)
  ·
    refine ⟨196433510176951157282568155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130955673451300771521712103 196433510176951157282568155)
    ·
      refine ⟨294650265265426735923852233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196433510176951157282568155 294650265265426735923852233)
      ·
        refine ⟨220987698949070051942889175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294650265265426735923852233 220987698949070051942889175)
        ·
          refine ⟨331481548423605077914333763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220987698949070051942889175 331481548423605077914333763)
          ·
            refine ⟨497222322635407616871500645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331481548423605077914333763 497222322635407616871500645)
            ·
              refine ⟨93229185494138928163406371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497222322635407616871500645 93229185494138928163406371)
              ·
                refine ⟨139843778241208392245109557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93229185494138928163406371 139843778241208392245109557)
                ·
                  refine ⟨13110354210113286772979021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139843778241208392245109557 13110354210113286772979021)
                  ·
                    refine ⟨4916382828792482539867133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13110354210113286772979021 4916382828792482539867133)
                    ·
                      refine ⟨1843643560797180952450175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916382828792482539867133 1843643560797180952450175)
                      ·
                        rfl

theorem cell23_3590483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_3590483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590483 prefixEnd_3590483 := by exact prefixLift 3590483
  have htrace : WordTrace (prefixWord ++ tailWord_3590483) baseStart_3590483 baseEnd_3590483 := by
    simpa [prefixWord, tailWord_3590483, baseEnd_3590483] using wordTrace_append hprefix tailTrace_3590483
  have hstable : (prefixWord ++ tailWord_3590483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590483).length < 2 ^ (prefixWord ++ tailWord_3590483).sum := by decide
  have hdescent : baseEnd_3590483 < baseStart_3590483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590484 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_3590484 : Nat := 118140960795 + 3590484 * 2 ^ 59
def prefixEnd_3590484 : Nat := 4983230072969 + 3 ^ 40 * 3590484 * 2
def baseEnd_3590484 : Nat := 1843644074277835448537671

theorem tailTrace_3590484 : CollatzResearch.WordTrace tailWord_3590484 prefixEnd_3590484 1843644074277835448537671 := by
  unfold tailWord_3590484
  simp only [CollatzResearch.WordTrace]
  refine ⟨65477854962148574346249253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87303806616198099128332337 65477854962148574346249253)
  ·
    refine ⟨12277097805402857689921735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65477854962148574346249253 12277097805402857689921735)
    ·
      refine ⟨18415646708104286534882603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277097805402857689921735 18415646708104286534882603)
      ·
        refine ⟨27623470062156429802323905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415646708104286534882603 27623470062156429802323905)
        ·
          refine ⟨20717602546617322351742929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27623470062156429802323905 20717602546617322351742929)
          ·
            refine ⟨15538201909962991763807197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20717602546617322351742929 15538201909962991763807197)
            ·
              refine ⟨5826825716236121911427699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15538201909962991763807197 5826825716236121911427699)
              ·
                refine ⟨8740238574354182867141549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826825716236121911427699 8740238574354182867141549)
                ·
                  refine ⟨3277589465382818575178081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8740238574354182867141549 3277589465382818575178081)
                  ·
                    refine ⟨2458192099037113931383561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277589465382818575178081 2458192099037113931383561)
                    ·
                      refine ⟨1843644074277835448537671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458192099037113931383561 1843644074277835448537671)
                      ·
                        rfl

theorem cell23_3590484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_3590484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590484 prefixEnd_3590484 := by exact prefixLift 3590484
  have htrace : WordTrace (prefixWord ++ tailWord_3590484) baseStart_3590484 baseEnd_3590484 := by
    simpa [prefixWord, tailWord_3590484, baseEnd_3590484] using wordTrace_append hprefix tailTrace_3590484
  have hstable : (prefixWord ++ tailWord_3590484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590484).length < 2 ^ (prefixWord ++ tailWord_3590484).sum := by decide
  have hdescent : baseEnd_3590484 < baseStart_3590484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590500 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_3590500 : Nat := 118140960795 + 3590500 * 2 ^ 59
def prefixEnd_3590500 : Nat := 4983230072969 + 3 ^ 40 * 3590500 * 2
def baseEnd_3590500 : Nat := 1843652289968307385937597

theorem tailTrace_3590500 : CollatzResearch.WordTrace tailWord_3590500 prefixEnd_3590500 1843652289968307385937597 := by
  unfold tailWord_3590500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65478146746119591712540477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87304195661492788950053969 65478146746119591712540477)
  ·
    refine ⟨24554305029794846892202679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65478146746119591712540477 24554305029794846892202679)
    ·
      refine ⟨36831457544692270338304019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24554305029794846892202679 36831457544692270338304019)
      ·
        refine ⟨55247186317038405507456029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36831457544692270338304019 55247186317038405507456029)
        ·
          refine ⟨20717694868889402065296011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55247186317038405507456029 20717694868889402065296011)
          ·
            refine ⟨31076542303334103097944017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20717694868889402065296011 31076542303334103097944017)
            ·
              refine ⟨23307406727500577323458013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31076542303334103097944017 23307406727500577323458013)
              ·
                refine ⟨8740277522812716496296755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23307406727500577323458013 8740277522812716496296755)
                ·
                  refine ⟨13110416284219074744445133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740277522812716496296755 13110416284219074744445133)
                  ·
                    refine ⟨4916406106582153029166925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13110416284219074744445133 4916406106582153029166925)
                    ·
                      refine ⟨1843652289968307385937597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916406106582153029166925 1843652289968307385937597)
                      ·
                        rfl

theorem cell23_3590500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_3590500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590500 prefixEnd_3590500 := by exact prefixLift 3590500
  have htrace : WordTrace (prefixWord ++ tailWord_3590500) baseStart_3590500 baseEnd_3590500 := by
    simpa [prefixWord, tailWord_3590500, baseEnd_3590500] using wordTrace_append hprefix tailTrace_3590500
  have hstable : (prefixWord ++ tailWord_3590500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590500).length < 2 ^ (prefixWord ++ tailWord_3590500).sum := by decide
  have hdescent : baseEnd_3590500 < baseStart_3590500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590504 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3590504 : Nat := 118140960795 + 3590504 * 2 ^ 59
def prefixEnd_3590504 : Nat := 4983230072969 + 3 ^ 40 * 3590504 * 2
def baseEnd_3590504 : Nat := 1843654343890925370287579

theorem tailTrace_3590504 : CollatzResearch.WordTrace tailWord_3590504 prefixEnd_3590504 1843654343890925370287579 := by
  unfold tailWord_3590504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65478219692112346054113283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87304292922816461405484377 65478219692112346054113283)
  ·
    refine ⟨98217329538168519081169925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65478219692112346054113283 98217329538168519081169925)
    ·
      refine ⟨18415749288406597327719361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98217329538168519081169925 18415749288406597327719361)
      ·
        refine ⟨13811811966304947995789521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18415749288406597327719361 13811811966304947995789521)
        ·
          refine ⟨10358858974728710996842141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811811966304947995789521 10358858974728710996842141)
          ·
            refine ⟨3884572115523266623815803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10358858974728710996842141 3884572115523266623815803)
            ·
              refine ⟨5826858173284899935723705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884572115523266623815803 5826858173284899935723705)
              ·
                refine ⟨4370143629963674951792779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826858173284899935723705 4370143629963674951792779)
                ·
                  refine ⟨6555215444945512427689169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370143629963674951792779 6555215444945512427689169)
                  ·
                    refine ⟨4916411583709134320766877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555215444945512427689169 4916411583709134320766877)
                    ·
                      refine ⟨1843654343890925370287579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916411583709134320766877 1843654343890925370287579)
                      ·
                        rfl

theorem cell23_3590504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3590504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590504 prefixEnd_3590504 := by exact prefixLift 3590504
  have htrace : WordTrace (prefixWord ++ tailWord_3590504) baseStart_3590504 baseEnd_3590504 := by
    simpa [prefixWord, tailWord_3590504, baseEnd_3590504] using wordTrace_append hprefix tailTrace_3590504
  have hstable : (prefixWord ++ tailWord_3590504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590504).length < 2 ^ (prefixWord ++ tailWord_3590504).sum := by decide
  have hdescent : baseEnd_3590504 < baseStart_3590504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590517 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3590517 : Nat := 118140960795 + 3590517 * 2 ^ 59
def prefixEnd_3590517 : Nat := 4983230072969 + 3 ^ 40 * 3590517 * 2
def baseEnd_3590517 : Nat := 1843661019139433819425019

theorem tailTrace_3590517 : CollatzResearch.WordTrace tailWord_3590517 prefixEnd_3590517 1843661019139433819425019 := by
  unfold tailWord_3590517
  simp only [CollatzResearch.WordTrace]
  refine ⟨130956913533177595328449805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87304609022118396885633203 130956913533177595328449805)
  ·
    refine ⟨49108842574941598248168677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130956913533177595328449805 49108842574941598248168677)
    ·
      refine ⟨9207907982801549671531627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49108842574941598248168677 9207907982801549671531627)
      ·
        refine ⟨13811861974202324507297441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207907982801549671531627 13811861974202324507297441)
        ·
          refine ⟨10358896480651743380473081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811861974202324507297441 10358896480651743380473081)
          ·
            refine ⟨7769172360488807535354811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10358896480651743380473081 7769172360488807535354811)
            ·
              refine ⟨11653758540733211303032217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769172360488807535354811 11653758540733211303032217)
              ·
                refine ⟨8740318905549908477274163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11653758540733211303032217 8740318905549908477274163)
                ·
                  refine ⟨13110478358324862715911245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740318905549908477274163 13110478358324862715911245)
                  ·
                    refine ⟨4916429384371823518466717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13110478358324862715911245 4916429384371823518466717)
                    ·
                      refine ⟨1843661019139433819425019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916429384371823518466717 1843661019139433819425019)
                      ·
                        rfl

theorem cell23_3590517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3590517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590517 prefixEnd_3590517 := by exact prefixLift 3590517
  have htrace : WordTrace (prefixWord ++ tailWord_3590517) baseStart_3590517 baseEnd_3590517 := by
    simpa [prefixWord, tailWord_3590517, baseEnd_3590517] using wordTrace_append hprefix tailTrace_3590517
  have hstable : (prefixWord ++ tailWord_3590517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590517).length < 2 ^ (prefixWord ++ tailWord_3590517).sum := by decide
  have hdescent : baseEnd_3590517 < baseStart_3590517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590533 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3590533 : Nat := 118140960795 + 3590533 * 2 ^ 59
def prefixEnd_3590533 : Nat := 4983230072969 + 3 ^ 40 * 3590533 * 2
def baseEnd_3590533 : Nat := 614556411609968585608315

theorem tailTrace_3590533 : CollatzResearch.WordTrace tailWord_3590533 prefixEnd_3590533 614556411609968585608315 := by
  unfold tailWord_3590533
  simp only [CollatzResearch.WordTrace]
  refine ⟨130957497101119630061032253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87304998067413086707354835 130957497101119630061032253)
  ·
    refine ⟨49109061412919861272887095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130957497101119630061032253 49109061412919861272887095)
    ·
      refine ⟨73663592119379791909330643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49109061412919861272887095 73663592119379791909330643)
      ·
        refine ⟨110495388179069687863995965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73663592119379791909330643 110495388179069687863995965)
        ·
          refine ⟨41435770567151132948998487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110495388179069687863995965 41435770567151132948998487)
          ·
            refine ⟨62153655850726699423497731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41435770567151132948998487 62153655850726699423497731)
            ·
              refine ⟨93230483776090049135246597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62153655850726699423497731 93230483776090049135246597)
              ·
                refine ⟨17480715708016884212858737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93230483776090049135246597 17480715708016884212858737)
                ·
                  refine ⟨13110536781012663159644053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17480715708016884212858737 13110536781012663159644053)
                  ·
                    refine ⟨614556411609968585608315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13110536781012663159644053 614556411609968585608315)
                    ·
                      rfl

theorem cell23_3590533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3590533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590533 prefixEnd_3590533 := by exact prefixLift 3590533
  have htrace : WordTrace (prefixWord ++ tailWord_3590533) baseStart_3590533 baseEnd_3590533 := by
    simpa [prefixWord, tailWord_3590533, baseEnd_3590533] using wordTrace_append hprefix tailTrace_3590533
  have hstable : (prefixWord ++ tailWord_3590533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590533).length < 2 ^ (prefixWord ++ tailWord_3590533).sum := by decide
  have hdescent : baseEnd_3590533 < baseStart_3590533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590563 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 9]
def baseStart_3590563 : Nat := 118140960795 + 3590563 * 2 ^ 59
def prefixEnd_3590563 : Nat := 4983230072969 + 3 ^ 40 * 3590563 * 2
def baseEnd_3590563 : Nat := 204853848805504515494423

theorem tailTrace_3590563 : CollatzResearch.WordTrace tailWord_3590563 prefixEnd_3590563 204853848805504515494423 := by
  unfold tailWord_3590563
  simp only [CollatzResearch.WordTrace]
  refine ⟨130958591291010945184624343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87305727527340630123082895 130958591291010945184624343)
  ·
    refine ⟨196437886936516417776936515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130958591291010945184624343 196437886936516417776936515)
    ·
      refine ⟨294656830404774626665404773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196437886936516417776936515 294656830404774626665404773)
      ·
        refine ⟨55248155700895242499763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294656830404774626665404773 55248155700895242499763395)
        ·
          refine ⟨82872233551342863749645093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55248155700895242499763395 82872233551342863749645093)
          ·
            refine ⟨15538543790876786953058455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82872233551342863749645093 15538543790876786953058455)
            ·
              refine ⟨23307815686315180429587683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538543790876786953058455 23307815686315180429587683)
              ·
                refine ⟨34961723529472770644381525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23307815686315180429587683 34961723529472770644381525)
                ·
                  refine ⟨204853848805504515494423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34961723529472770644381525 204853848805504515494423)
                  ·
                    rfl

theorem cell23_3590563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 9].length) (baseStart_3590563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590563 prefixEnd_3590563 := by exact prefixLift 3590563
  have htrace : WordTrace (prefixWord ++ tailWord_3590563) baseStart_3590563 baseEnd_3590563 := by
    simpa [prefixWord, tailWord_3590563, baseEnd_3590563] using wordTrace_append hprefix tailTrace_3590563
  have hstable : (prefixWord ++ tailWord_3590563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590563).length < 2 ^ (prefixWord ++ tailWord_3590563).sum := by decide
  have hdescent : baseEnd_3590563 < baseStart_3590563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590603 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_3590603 : Nat := 118140960795 + 3590603 * 2 ^ 59
def prefixEnd_3590603 : Nat := 4983230072969 + 3 ^ 40 * 3590603 * 2
def baseEnd_3590603 : Nat := 1843705178475720482949623

theorem tailTrace_3590603 : CollatzResearch.WordTrace tailWord_3590603 prefixEnd_3590603 1843705178475720482949623 := by
  unfold tailWord_3590603
  simp only [CollatzResearch.WordTrace]
  refine ⟨130960050210866032016080463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87306700140577354677386975 130960050210866032016080463)
  ·
    refine ⟨196440075316299048024120695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130960050210866032016080463 196440075316299048024120695)
    ·
      refine ⟨294660112974448572036181043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196440075316299048024120695 294660112974448572036181043)
      ·
        refine ⟨441990169461672858054271565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294660112974448572036181043 441990169461672858054271565)
        ·
          refine ⟨165746313548127321770351837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441990169461672858054271565 165746313548127321770351837)
          ·
            refine ⟨62154867580547745663881939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165746313548127321770351837 62154867580547745663881939)
            ·
              refine ⟨93232301370821618495822909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62154867580547745663881939 93232301370821618495822909)
              ·
                refine ⟨34962113014058106935933591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93232301370821618495822909 34962113014058106935933591)
                ·
                  refine ⟨52443169521087160403900387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34962113014058106935933591 52443169521087160403900387)
                  ·
                    refine ⟨78664754281630740605850581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52443169521087160403900387 78664754281630740605850581)
                    ·
                      refine ⟨1843705178475720482949623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78664754281630740605850581 1843705178475720482949623)
                      ·
                        rfl

theorem cell23_3590603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_3590603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590603 prefixEnd_3590603 := by exact prefixLift 3590603
  have htrace : WordTrace (prefixWord ++ tailWord_3590603) baseStart_3590603 baseEnd_3590603 := by
    simpa [prefixWord, tailWord_3590603, baseEnd_3590603] using wordTrace_append hprefix tailTrace_3590603
  have hstable : (prefixWord ++ tailWord_3590603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590603).length < 2 ^ (prefixWord ++ tailWord_3590603).sum := by decide
  have hdescent : baseEnd_3590603 < baseStart_3590603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590650 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_3590650 : Nat := 118140960795 + 3590650 * 2 ^ 59
def prefixEnd_3590650 : Nat := 4983230072969 + 3 ^ 40 * 3590650 * 2
def baseEnd_3590650 : Nat := 1843729312066481799061907

theorem tailTrace_3590650 : CollatzResearch.WordTrace tailWord_3590650 prefixEnd_3590650 1843729312066481799061907 := by
  unfold tailWord_3590650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740441110423939760760351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87307842961130506028694269 32740441110423939760760351)
  ·
    refine ⟨49110661665635909641140527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32740441110423939760760351 49110661665635909641140527)
    ·
      refine ⟨73665992498453864461710791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49110661665635909641140527 73665992498453864461710791)
      ·
        refine ⟨110498988747680796692566187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73665992498453864461710791 110498988747680796692566187)
        ·
          refine ⟨165748483121521195038849281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110498988747680796692566187 165748483121521195038849281)
          ·
            refine ⟨124311362341140896279136961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165748483121521195038849281 124311362341140896279136961)
            ·
              refine ⟨93233521755855672209352721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124311362341140896279136961 93233521755855672209352721)
              ·
                refine ⟨69925141316891754157014541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93233521755855672209352721 69925141316891754157014541)
                ·
                  refine ⟨26221927993834407808880453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69925141316891754157014541 26221927993834407808880453)
                  ·
                    refine ⟨4916611498843951464165085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26221927993834407808880453 4916611498843951464165085)
                    ·
                      refine ⟨1843729312066481799061907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916611498843951464165085 1843729312066481799061907)
                      ·
                        rfl

theorem cell23_3590650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_3590650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590650 prefixEnd_3590650 := by exact prefixLift 3590650
  have htrace : WordTrace (prefixWord ++ tailWord_3590650) baseStart_3590650 baseEnd_3590650 := by
    simpa [prefixWord, tailWord_3590650, baseEnd_3590650] using wordTrace_append hprefix tailTrace_3590650
  have hstable : (prefixWord ++ tailWord_3590650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590650).length < 2 ^ (prefixWord ++ tailWord_3590650).sum := by decide
  have hdescent : baseEnd_3590650 < baseStart_3590650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590684 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3590684 : Nat := 118140960795 + 3590684 * 2 ^ 59
def prefixEnd_3590684 : Nat := 4983230072969 + 3 ^ 40 * 3590684 * 2
def baseEnd_3590684 : Nat := 1843746770408734666036751

theorem tailTrace_3590684 : CollatzResearch.WordTrace tailWord_3590684 prefixEnd_3590684 1843746770408734666036751 := by
  unfold tailWord_3590684
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481502261786291424889553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87308669682381721899852737 65481502261786291424889553)
  ·
    refine ⟨49111126696339718568667165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65481502261786291424889553 49111126696339718568667165)
    ·
      refine ⟨18416672511127394463250187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49111126696339718568667165 18416672511127394463250187)
      ·
        refine ⟨27625008766691091694875281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18416672511127394463250187 27625008766691091694875281)
        ·
          refine ⟨20718756575018318771156461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27625008766691091694875281 20718756575018318771156461)
          ·
            refine ⟨7769533715631869539183673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20718756575018318771156461 7769533715631869539183673)
            ·
              refine ⟨5827150286723902154387755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769533715631869539183673 5827150286723902154387755)
              ·
                refine ⟨8740725430085853231581633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827150286723902154387755 8740725430085853231581633)
                ·
                  refine ⟨6555544072564389923686225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8740725430085853231581633 6555544072564389923686225)
                  ·
                    refine ⟨4916658054423292442764669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555544072564389923686225 4916658054423292442764669)
                    ·
                      refine ⟨1843746770408734666036751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916658054423292442764669 1843746770408734666036751)
                      ·
                        rfl

theorem cell23_3590684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3590684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590684 prefixEnd_3590684 := by exact prefixLift 3590684
  have htrace : WordTrace (prefixWord ++ tailWord_3590684) baseStart_3590684 baseEnd_3590684 := by
    simpa [prefixWord, tailWord_3590684, baseEnd_3590684] using wordTrace_append hprefix tailTrace_3590684
  have hstable : (prefixWord ++ tailWord_3590684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590684).length < 2 ^ (prefixWord ++ tailWord_3590684).sum := by decide
  have hdescent : baseEnd_3590684 < baseStart_3590684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590690 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3590690 : Nat := 118140960795 + 3590690 * 2 ^ 59
def prefixEnd_3590690 : Nat := 4983230072969 + 3 ^ 40 * 3590690 * 2
def baseEnd_3590690 : Nat := 1843749851292661642561723

theorem tailTrace_3590690 : CollatzResearch.WordTrace tailWord_3590690 prefixEnd_3590690 1843749851292661642561723 := by
  unfold tailWord_3590690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740805840387711468624381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87308815574367230582998349 32740805840387711468624381)
  ·
    refine ⟨12277802190145391800734143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32740805840387711468624381 12277802190145391800734143)
    ·
      refine ⟨18416703285218087701101215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277802190145391800734143 18416703285218087701101215)
      ·
        refine ⟨27625054927827131551651823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18416703285218087701101215 27625054927827131551651823)
        ·
          refine ⟨41437582391740697327477735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27625054927827131551651823 41437582391740697327477735)
          ·
            refine ⟨62156373587611045991216603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41437582391740697327477735 62156373587611045991216603)
            ·
              refine ⟨93234560381416568986824905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62156373587611045991216603 93234560381416568986824905)
              ·
                refine ⟨69925920286062426740118679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93234560381416568986824905 69925920286062426740118679)
                ·
                  refine ⟨104888880429093640110178019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69925920286062426740118679 104888880429093640110178019)
                  ·
                    refine ⟨157333320643640460165267029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104888880429093640110178019 157333320643640460165267029)
                    ·
                      refine ⟨1843749851292661642561723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 157333320643640460165267029 1843749851292661642561723)
                      ·
                        rfl

theorem cell23_3590690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3590690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590690 prefixEnd_3590690 := by exact prefixLift 3590690
  have htrace : WordTrace (prefixWord ++ tailWord_3590690) baseStart_3590690 baseEnd_3590690 := by
    simpa [prefixWord, tailWord_3590690, baseEnd_3590690] using wordTrace_append hprefix tailTrace_3590690
  have hstable : (prefixWord ++ tailWord_3590690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590690).length < 2 ^ (prefixWord ++ tailWord_3590690).sum := by decide
  have hdescent : baseEnd_3590690 < baseStart_3590690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590717 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_3590717 : Nat := 118140960795 + 3590717 * 2 ^ 59
def prefixEnd_3590717 : Nat := 4983230072969 + 3 ^ 40 * 3590717 * 2
def baseEnd_3590717 : Nat := 614587905090111012308033

theorem tailTrace_3590717 : CollatzResearch.WordTrace tailWord_3590717 prefixEnd_3590717 614587905090111012308033 := by
  unfold tailWord_3590717
  simp only [CollatzResearch.WordTrace]
  refine ⟨130964208132453029485730405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87309472088302019657153603 130964208132453029485730405)
  ·
    refine ⟨24555789024834943028574451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130964208132453029485730405 24555789024834943028574451)
    ·
      refine ⟨36833683537252414542861677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555789024834943028574451 36833683537252414542861677)
      ·
        refine ⟨13812631326469655453573129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36833683537252414542861677 13812631326469655453573129)
        ·
          refine ⟨10359473494852241590179847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13812631326469655453573129 10359473494852241590179847)
          ·
            refine ⟨15539210242278362385269771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359473494852241590179847 15539210242278362385269771)
            ·
              refine ⟨23308815363417543577904657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539210242278362385269771 23308815363417543577904657)
              ·
                refine ⟨17481611522563157683428493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23308815363417543577904657 17481611522563157683428493)
                ·
                  refine ⟨6555604320961184131285685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17481611522563157683428493 6555604320961184131285685)
                  ·
                    refine ⟨614587905090111012308033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6555604320961184131285685 614587905090111012308033)
                    ·
                      rfl

theorem cell23_3590717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_3590717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590717 prefixEnd_3590717 := by exact prefixLift 3590717
  have htrace : WordTrace (prefixWord ++ tailWord_3590717) baseStart_3590717 baseEnd_3590717 := by
    simpa [prefixWord, tailWord_3590717, baseEnd_3590717] using wordTrace_append hprefix tailTrace_3590717
  have hstable : (prefixWord ++ tailWord_3590717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590717).length < 2 ^ (prefixWord ++ tailWord_3590717).sum := by decide
  have hdescent : baseEnd_3590717 < baseStart_3590717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590737 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3590737 : Nat := 118140960795 + 3590737 * 2 ^ 59
def prefixEnd_3590737 : Nat := 4983230072969 + 3 ^ 40 * 3590737 * 2
def baseEnd_3590737 : Nat := 1843773984883422958674007

theorem tailTrace_3590737 : CollatzResearch.WordTrace tailWord_3590737 prefixEnd_3590737 1843773984883422958674007 := by
  unfold tailWord_3590737
  simp only [CollatzResearch.WordTrace]
  refine ⟨130964937592380572901458465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87309958394920381934305643 130964937592380572901458465)
  ·
    refine ⟨98223703194285429676093849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130964937592380572901458465 98223703194285429676093849)
    ·
      refine ⟨73667777395714072257070387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98223703194285429676093849 73667777395714072257070387)
      ·
        refine ⟨110501666093571108385605581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73667777395714072257070387 110501666093571108385605581)
        ·
          refine ⟨41438124785089165644602093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110501666093571108385605581 41438124785089165644602093)
          ·
            refine ⟨15539296794408437116725785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41438124785089165644602093 15539296794408437116725785)
            ·
              refine ⟨11654472595806327837544339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539296794408437116725785 11654472595806327837544339)
              ·
                refine ⟨17481708893709491756316509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654472595806327837544339 17481708893709491756316509)
                ·
                  refine ⟨6555640835141059408618691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17481708893709491756316509 6555640835141059408618691)
                  ·
                    refine ⟨9833461252711589112928037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555640835141059408618691 9833461252711589112928037)
                    ·
                      refine ⟨1843773984883422958674007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9833461252711589112928037 1843773984883422958674007)
                      ·
                        rfl

theorem cell23_3590737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3590737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590737 prefixEnd_3590737 := by exact prefixLift 3590737
  have htrace : WordTrace (prefixWord ++ tailWord_3590737) baseStart_3590737 baseEnd_3590737 := by
    simpa [prefixWord, tailWord_3590737, baseEnd_3590737] using wordTrace_append hprefix tailTrace_3590737
  have hstable : (prefixWord ++ tailWord_3590737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590737).length < 2 ^ (prefixWord ++ tailWord_3590737).sum := by decide
  have hdescent : baseEnd_3590737 < baseStart_3590737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590764 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_3590764 : Nat := 118140960795 + 3590764 * 2 ^ 59
def prefixEnd_3590764 : Nat := 4983230072969 + 3 ^ 40 * 3590764 * 2
def baseEnd_3590764 : Nat := 614595949620364784345461

theorem tailTrace_3590764 : CollatzResearch.WordTrace tailWord_3590764 prefixEnd_3590764 614595949620364784345461 := by
  unfold tailWord_3590764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65482961181641378256345673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87310614908855171008460897 65482961181641378256345673)
  ·
    refine ⟨49112220886231033692259255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65482961181641378256345673 49112220886231033692259255)
    ·
      refine ⟨73668331329346550538388883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49112220886231033692259255 73668331329346550538388883)
      ·
        refine ⟨110502496994019825807583325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73668331329346550538388883 110502496994019825807583325)
        ·
          refine ⟨41438436372757434677843747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110502496994019825807583325 41438436372757434677843747)
          ·
            refine ⟨62157654559136152016765621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41438436372757434677843747 62157654559136152016765621)
            ·
              refine ⟨5827280114919014251571777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62157654559136152016765621 5827280114919014251571777)
              ·
                refine ⟨4370460086189260688678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5827280114919014251571777 4370460086189260688678833)
                ·
                  refine ⟨3277845064641945516509125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370460086189260688678833 3277845064641945516509125)
                  ·
                    refine ⟨614595949620364784345461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3277845064641945516509125 614595949620364784345461)
                    ·
                      rfl

theorem cell23_3590764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_3590764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590764 prefixEnd_3590764 := by exact prefixLift 3590764
  have htrace : WordTrace (prefixWord ++ tailWord_3590764) baseStart_3590764 baseEnd_3590764 := by
    simpa [prefixWord, tailWord_3590764, baseEnd_3590764] using wordTrace_append hprefix tailTrace_3590764
  have hstable : (prefixWord ++ tailWord_3590764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590764).length < 2 ^ (prefixWord ++ tailWord_3590764).sum := by decide
  have hdescent : baseEnd_3590764 < baseStart_3590764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590781 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_3590781 : Nat := 118140960795 + 3590781 * 2 ^ 59
def prefixEnd_3590781 : Nat := 4983230072969 + 3 ^ 40 * 3590781 * 2
def baseEnd_3590781 : Nat := 614598859344073595507935

theorem tailTrace_3590781 : CollatzResearch.WordTrace tailWord_3590781 prefixEnd_3590781 614598859344073595507935 := by
  unfold tailWord_3590781
  simp only [CollatzResearch.WordTrace]
  refine ⟨130966542404221168416060197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87311028269480778944040131 130966542404221168416060197)
  ·
    refine ⟨24556226700791469078011287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130966542404221168416060197 24556226700791469078011287)
    ·
      refine ⟨36834340051187203617016931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24556226700791469078011287 36834340051187203617016931)
      ·
        refine ⟨55251510076780805425525397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36834340051187203617016931 55251510076780805425525397)
        ·
          refine ⟨2589914534849100254321503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55251510076780805425525397 2589914534849100254321503)
          ·
            refine ⟨3884871802273650381482255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589914534849100254321503 3884871802273650381482255)
            ·
              refine ⟨5827307703410475572223383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884871802273650381482255 5827307703410475572223383)
              ·
                refine ⟨8740961555115713358335075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827307703410475572223383 8740961555115713358335075)
                ·
                  refine ⟨13111442332673570037502613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740961555115713358335075 13111442332673570037502613)
                  ·
                    refine ⟨614598859344073595507935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13111442332673570037502613 614598859344073595507935)
                    ·
                      rfl

theorem cell23_3590781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_3590781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590781 prefixEnd_3590781 := by exact prefixLift 3590781
  have htrace : WordTrace (prefixWord ++ tailWord_3590781) baseStart_3590781 baseEnd_3590781 := by
    simpa [prefixWord, tailWord_3590781, baseEnd_3590781] using wordTrace_append hprefix tailTrace_3590781
  have hstable : (prefixWord ++ tailWord_3590781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590781).length < 2 ^ (prefixWord ++ tailWord_3590781).sum := by decide
  have hdescent : baseEnd_3590781 < baseStart_3590781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590784 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_3590784 : Nat := 118140960795 + 3590784 * 2 ^ 59
def prefixEnd_3590784 : Nat := 4983230072969 + 3 ^ 40 * 3590784 * 2
def baseEnd_3590784 : Nat := 1843798118474184274786291

theorem tailTrace_3590784 : CollatzResearch.WordTrace tailWord_3590784 prefixEnd_3590784 1843798118474184274786291 := by
  unfold tailWord_3590784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65483325911605149964209703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87311101215473533285612937 65483325911605149964209703)
  ·
    refine ⟨98224988867407724946314555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65483325911605149964209703 98224988867407724946314555)
    ·
      refine ⟨147337483301111587419471833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98224988867407724946314555 147337483301111587419471833)
      ·
        refine ⟨110503112475833690564603875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147337483301111587419471833 110503112475833690564603875)
        ·
          refine ⟨165754668713750535846905813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110503112475833690564603875 165754668713750535846905813)
          ·
            refine ⟨3884875047978528183911855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165754668713750535846905813 3884875047978528183911855)
            ·
              refine ⟨5827312571967792275867783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884875047978528183911855 5827312571967792275867783)
              ·
                refine ⟨8740968857951688413801675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827312571967792275867783 8740968857951688413801675)
                ·
                  refine ⟨13111453286927532620702513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740968857951688413801675 13111453286927532620702513)
                  ·
                    refine ⟨9833589965195649465526885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13111453286927532620702513 9833589965195649465526885)
                    ·
                      refine ⟨1843798118474184274786291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9833589965195649465526885 1843798118474184274786291)
                      ·
                        rfl

theorem cell23_3590784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_3590784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590784 prefixEnd_3590784 := by exact prefixLift 3590784
  have htrace : WordTrace (prefixWord ++ tailWord_3590784) baseStart_3590784 baseEnd_3590784 := by
    simpa [prefixWord, tailWord_3590784, baseEnd_3590784] using wordTrace_append hprefix tailTrace_3590784
  have hstable : (prefixWord ++ tailWord_3590784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590784).length < 2 ^ (prefixWord ++ tailWord_3590784).sum := by decide
  have hdescent : baseEnd_3590784 < baseStart_3590784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590847 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3590847 : Nat := 118140960795 + 3590847 * 2 ^ 59
def prefixEnd_3590847 : Nat := 4983230072969 + 3 ^ 40 * 3590847 * 2
def baseEnd_3590847 : Nat := 1843830467755417528298501

theorem tailTrace_3590847 : CollatzResearch.WordTrace tailWord_3590847 prefixEnd_3590847 1843830467755417528298501 := by
  unfold tailWord_3590847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130968949621982061687962795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87312633081321374458641863 130968949621982061687962795)
  ·
    refine ⟨196453424432973092531944193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130968949621982061687962795 196453424432973092531944193)
    ·
      refine ⟨147340068324729819398958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196453424432973092531944193 147340068324729819398958145)
      ·
        refine ⟨110505051243547364549218609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147340068324729819398958145 110505051243547364549218609)
        ·
          refine ⟨82878788432660523411913957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110505051243547364549218609 82878788432660523411913957)
          ·
            refine ⟨15539772831123848139733867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82878788432660523411913957 15539772831123848139733867)
            ·
              refine ⟨23309659246685772209600801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539772831123848139733867 23309659246685772209600801)
              ·
                refine ⟨17482244435014329157200601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23309659246685772209600801 17482244435014329157200601)
                ·
                  refine ⟨13111683326260746867900451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17482244435014329157200601 13111683326260746867900451)
                  ·
                    refine ⟨19667524989391120301850677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13111683326260746867900451 19667524989391120301850677)
                    ·
                      refine ⟨1843830467755417528298501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19667524989391120301850677 1843830467755417528298501)
                      ·
                        rfl

theorem cell23_3590847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3590847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590847 prefixEnd_3590847 := by exact prefixLift 3590847
  have htrace : WordTrace (prefixWord ++ tailWord_3590847) baseStart_3590847 baseEnd_3590847 := by
    simpa [prefixWord, tailWord_3590847, baseEnd_3590847] using wordTrace_append hprefix tailTrace_3590847
  have hstable : (prefixWord ++ tailWord_3590847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590847).length < 2 ^ (prefixWord ++ tailWord_3590847).sum := by decide
  have hdescent : baseEnd_3590847 < baseStart_3590847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590848 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2]
def baseStart_3590848 : Nat := 118140960795 + 3590848 * 2 ^ 59
def prefixEnd_3590848 : Nat := 4983230072969 + 3 ^ 40 * 3590848 * 2
def baseEnd_3590848 : Nat := 1843830981236072024385997

theorem tailTrace_3590848 : CollatzResearch.WordTrace tailWord_3590848 prefixEnd_3590848 1843830981236072024385997 := by
  unfold tailWord_3590848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65484493047489219429374599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87312657396652292572499465 65484493047489219429374599)
  ·
    refine ⟨98226739571233829144061899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65484493047489219429374599 98226739571233829144061899)
    ·
      refine ⟨147340109356850743716092849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98226739571233829144061899 147340109356850743716092849)
      ·
        refine ⟨110505082017638057787069637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147340109356850743716092849 110505082017638057787069637)
        ·
          refine ⟨20719702878307135835075557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110505082017638057787069637 20719702878307135835075557)
          ·
            refine ⟨3884944289682587969076667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20719702878307135835075557 3884944289682587969076667)
            ·
              refine ⟨5827416434523881953615001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884944289682587969076667 5827416434523881953615001)
              ·
                refine ⟨4370562325892911465211251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5827416434523881953615001 4370562325892911465211251)
                ·
                  refine ⟨6555843488839367197816877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370562325892911465211251 6555843488839367197816877)
                  ·
                    refine ⟨2458441308314762699181329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6555843488839367197816877 2458441308314762699181329)
                    ·
                      refine ⟨1843830981236072024385997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458441308314762699181329 1843830981236072024385997)
                      ·
                        rfl

theorem cell23_3590848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_3590848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590848 prefixEnd_3590848 := by exact prefixLift 3590848
  have htrace : WordTrace (prefixWord ++ tailWord_3590848) baseStart_3590848 baseEnd_3590848 := by
    simpa [prefixWord, tailWord_3590848, baseEnd_3590848] using wordTrace_append hprefix tailTrace_3590848
  have hstable : (prefixWord ++ tailWord_3590848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590848).length < 2 ^ (prefixWord ++ tailWord_3590848).sum := by decide
  have hdescent : baseEnd_3590848 < baseStart_3590848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590894 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3590894 : Nat := 118140960795 + 3590894 * 2 ^ 59
def prefixEnd_3590894 : Nat := 4983230072969 + 3 ^ 40 * 3590894 * 2
def baseEnd_3590894 : Nat := 1843854601346178844410785

theorem tailTrace_3590894 : CollatzResearch.WordTrace tailWord_3590894 prefixEnd_3590894 1843854601346178844410785 := by
  unfold tailWord_3590894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16371332981601473589365467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87313775901874525809949157 16371332981601473589365467)
  ·
    refine ⟨24556999472402210384048201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16371332981601473589365467 24556999472402210384048201)
    ·
      refine ⟨18417749604301657788036151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24556999472402210384048201 18417749604301657788036151)
      ·
        refine ⟨27626624406452486682054227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18417749604301657788036151 27626624406452486682054227)
        ·
          refine ⟨41439936609678730023081341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27626624406452486682054227 41439936609678730023081341)
          ·
            refine ⟨15539976228629523758655503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41439936609678730023081341 15539976228629523758655503)
            ·
              refine ⟨23309964342944285637983255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539976228629523758655503 23309964342944285637983255)
              ·
                refine ⟨34964946514416428456974883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23309964342944285637983255 34964946514416428456974883)
                ·
                  refine ⟨52447419771624642685462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34964946514416428456974883 52447419771624642685462325)
                  ·
                    refine ⟨4916945603589810251762093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52447419771624642685462325 4916945603589810251762093)
                    ·
                      refine ⟨1843854601346178844410785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4916945603589810251762093 1843854601346178844410785)
                      ·
                        rfl

theorem cell23_3590894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3590894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590894 prefixEnd_3590894 := by exact prefixLift 3590894
  have htrace : WordTrace (prefixWord ++ tailWord_3590894) baseStart_3590894 baseEnd_3590894 := by
    simpa [prefixWord, tailWord_3590894, baseEnd_3590894] using wordTrace_append hprefix tailTrace_3590894
  have hstable : (prefixWord ++ tailWord_3590894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590894).length < 2 ^ (prefixWord ++ tailWord_3590894).sum := by decide
  have hdescent : baseEnd_3590894 < baseStart_3590894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590897 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3590897 : Nat := 118140960795 + 3590897 * 2 ^ 59
def prefixEnd_3590897 : Nat := 4983230072969 + 3 ^ 40 * 3590897 * 2
def baseEnd_3590897 : Nat := 614618713929380777557757

theorem tailTrace_3590897 : CollatzResearch.WordTrace tailWord_3590897 prefixEnd_3590897 614618713929380777557757 := by
  unfold tailWord_3590897
  simp only [CollatzResearch.WordTrace]
  refine ⟨130970773271800920227282945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87313848847867280151521963 130970773271800920227282945)
  ·
    refine ⟨98228079953850690170462209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130970773271800920227282945 98228079953850690170462209)
    ·
      refine ⟨73671059965388017627846657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98228079953850690170462209 73671059965388017627846657)
      ·
        refine ⟨55253294974041013220884993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73671059965388017627846657 55253294974041013220884993)
        ·
          refine ⟨41439971230530759915663745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55253294974041013220884993 41439971230530759915663745)
          ·
            refine ⟨31079978422898069936747809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41439971230530759915663745 31079978422898069936747809)
            ·
              refine ⟨23309983817173552452560857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31079978422898069936747809 23309983817173552452560857)
              ·
                refine ⟨17482487862880164339420643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23309983817173552452560857 17482487862880164339420643)
                ·
                  refine ⟨26223731794320246509130965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17482487862880164339420643 26223731794320246509130965)
                  ·
                    refine ⟨614618713929380777557757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26223731794320246509130965 614618713929380777557757)
                    ·
                      rfl

theorem cell23_3590897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3590897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590897 prefixEnd_3590897 := by exact prefixLift 3590897
  have htrace : WordTrace (prefixWord ++ tailWord_3590897) baseStart_3590897 baseEnd_3590897 := by
    simpa [prefixWord, tailWord_3590897, baseEnd_3590897] using wordTrace_append hprefix tailTrace_3590897
  have hstable : (prefixWord ++ tailWord_3590897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590897).length < 2 ^ (prefixWord ++ tailWord_3590897).sum := by decide
  have hdescent : baseEnd_3590897 < baseStart_3590897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590904 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_3590904 : Nat := 118140960795 + 3590904 * 2 ^ 59
def prefixEnd_3590904 : Nat := 4983230072969 + 3 ^ 40 * 3590904 * 2
def baseEnd_3590904 : Nat := 1843859736152723805285739

theorem tailTrace_3590904 : CollatzResearch.WordTrace tailWord_3590904 prefixEnd_3590904 1843859736152723805285739 := by
  unfold tailWord_3590904
  simp only [CollatzResearch.WordTrace]
  refine ⟨65485514291387780211393883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87314019055183706948525177 65485514291387780211393883)
  ·
    refine ⟨98228271437081670317090825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65485514291387780211393883 98228271437081670317090825)
    ·
      refine ⟨73671203577811252737818119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98228271437081670317090825 73671203577811252737818119)
      ·
        refine ⟨110506805366716879106727179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73671203577811252737818119 110506805366716879106727179)
        ·
          refine ⟨165760208050075318660090769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110506805366716879106727179 165760208050075318660090769)
          ·
            refine ⟨124320156037556488995068077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165760208050075318660090769 124320156037556488995068077)
            ·
              refine ⟨46620058514083683373150529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124320156037556488995068077 46620058514083683373150529)
              ·
                refine ⟨34965043885562762529862897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46620058514083683373150529 34965043885562762529862897)
                ·
                  refine ⟨26223782914172071897397173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34965043885562762529862897 26223782914172071897397173)
                  ·
                    refine ⟨2458479648203631740380985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26223782914172071897397173 2458479648203631740380985)
                    ·
                      refine ⟨1843859736152723805285739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458479648203631740380985 1843859736152723805285739)
                      ·
                        rfl

theorem cell23_3590904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_3590904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590904 prefixEnd_3590904 := by exact prefixLift 3590904
  have htrace : WordTrace (prefixWord ++ tailWord_3590904) baseStart_3590904 baseEnd_3590904 := by
    simpa [prefixWord, tailWord_3590904, baseEnd_3590904] using wordTrace_append hprefix tailTrace_3590904
  have hstable : (prefixWord ++ tailWord_3590904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590904).length < 2 ^ (prefixWord ++ tailWord_3590904).sum := by decide
  have hdescent : baseEnd_3590904 < baseStart_3590904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590947 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3590947 : Nat := 118140960795 + 3590947 * 2 ^ 59
def prefixEnd_3590947 : Nat := 4983230072969 + 3 ^ 40 * 3590947 * 2
def baseEnd_3590947 : Nat := 1843881815820867137048041

theorem tailTrace_3590947 : CollatzResearch.WordTrace tailWord_3590947 prefixEnd_3590947 1843881815820867137048041 := by
  unfold tailWord_3590947
  simp only [CollatzResearch.WordTrace]
  refine ⟨130972596921619778766603095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87315064614413185844402063 130972596921619778766603095)
  ·
    refine ⟨196458895382429668149904643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130972596921619778766603095 196458895382429668149904643)
    ·
      refine ⟨294688343073644502224856965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196458895382429668149904643 294688343073644502224856965)
      ·
        refine ⟨55254064326308344167160681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294688343073644502224856965 55254064326308344167160681)
        ·
          refine ⟨41440548244731258125370511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55254064326308344167160681 41440548244731258125370511)
          ·
            refine ⟨62160822367096887188055767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41440548244731258125370511 62160822367096887188055767)
            ·
              refine ⟨93241233550645330782083651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62160822367096887188055767 93241233550645330782083651)
              ·
                refine ⟨139861850325967996173125477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93241233550645330782083651 139861850325967996173125477)
                ·
                  refine ⟨26224096936118999282461027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139861850325967996173125477 26224096936118999282461027)
                  ·
                    refine ⟨39336145404178498923691541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26224096936118999282461027 39336145404178498923691541)
                    ·
                      refine ⟨1843881815820867137048041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39336145404178498923691541 1843881815820867137048041)
                      ·
                        rfl

theorem cell23_3590947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3590947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3590947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3590947 prefixEnd_3590947 := by exact prefixLift 3590947
  have htrace : WordTrace (prefixWord ++ tailWord_3590947) baseStart_3590947 baseEnd_3590947 := by
    simpa [prefixWord, tailWord_3590947, baseEnd_3590947] using wordTrace_append hprefix tailTrace_3590947
  have hstable : (prefixWord ++ tailWord_3590947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590947).length < 2 ^ (prefixWord ++ tailWord_3590947).sum := by decide
  have hdescent : baseEnd_3590947 < baseStart_3590947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591051 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 2, 4]
def baseStart_3591051 : Nat := 118140960795 + 3591051 * 2 ^ 59
def prefixEnd_3591051 : Nat := 4983230072969 + 3 ^ 40 * 3591051 * 2
def baseEnd_3591051 : Nat := 614645072602978243382521

theorem tailTrace_3591051 : CollatzResearch.WordTrace tailWord_3591051 prefixEnd_3591051 614645072602978243382521 := by
  unfold tailWord_3591051
  simp only [CollatzResearch.WordTrace]
  refine ⟨130976390113243004528389007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87317593408828669685592671 130976390113243004528389007)
  ·
    refine ⟨196464585169864506792583511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130976390113243004528389007 196464585169864506792583511)
    ·
      refine ⟨294696877754796760188875267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196464585169864506792583511 294696877754796760188875267)
      ·
        refine ⟨442045316632195140283312901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294696877754796760188875267 442045316632195140283312901)
        ·
          refine ⟨82883496868536588803121169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442045316632195140283312901 82883496868536588803121169)
          ·
            refine ⟨62162622651402441602340877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82883496868536588803121169 62162622651402441602340877)
            ·
              refine ⟨23310983494275915600877829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62162622651402441602340877 23310983494275915600877829)
              ·
                refine ⟨4370809405176734175164593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23310983494275915600877829 4370809405176734175164593)
                ·
                  refine ⟨3278107053882550631373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370809405176734175164593 3278107053882550631373445)
                  ·
                    refine ⟨614645072602978243382521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278107053882550631373445 614645072602978243382521)
                    ·
                      rfl

theorem cell23_3591051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 4].length) (baseStart_3591051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591051 prefixEnd_3591051 := by exact prefixLift 3591051
  have htrace : WordTrace (prefixWord ++ tailWord_3591051) baseStart_3591051 baseEnd_3591051 := by
    simpa [prefixWord, tailWord_3591051, baseEnd_3591051] using wordTrace_append hprefix tailTrace_3591051
  have hstable : (prefixWord ++ tailWord_3591051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591051).length < 2 ^ (prefixWord ++ tailWord_3591051).sum := by decide
  have hdescent : baseEnd_3591051 < baseStart_3591051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591061 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_3591061 : Nat := 118140960795 + 3591061 * 2 ^ 59
def prefixEnd_3591061 : Nat := 4983230072969 + 3 ^ 40 * 3591061 * 2
def baseEnd_3591061 : Nat := 1843940352615479691022517

theorem tailTrace_3591061 : CollatzResearch.WordTrace tailWord_3591061 prefixEnd_3591061 1843940352615479691022517 := by
  unfold tailWord_3591061
  simp only [CollatzResearch.WordTrace]
  refine ⟨130976754843206776236253037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87317836562137850824168691 130976754843206776236253037)
  ·
    refine ⟨49116283066202541088594889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130976754843206776236253037 49116283066202541088594889)
    ·
      refine ⟨36837212299651905816446167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49116283066202541088594889 36837212299651905816446167)
      ·
        refine ⟨55255818449477858724669251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36837212299651905816446167 55255818449477858724669251)
        ·
          refine ⟨82883727674216788087003877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55255818449477858724669251 82883727674216788087003877)
          ·
            refine ⟨15540698938915647766313227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82883727674216788087003877 15540698938915647766313227)
            ·
              refine ⟨23311048408373471649469841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540698938915647766313227 23311048408373471649469841)
              ·
                refine ⟨17483286306280103737102381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23311048408373471649469841 17483286306280103737102381)
                ·
                  refine ⟨6556232364855038901413393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17483286306280103737102381 6556232364855038901413393)
                  ·
                    refine ⟨4917174273641279176060045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6556232364855038901413393 4917174273641279176060045)
                    ·
                      refine ⟨1843940352615479691022517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917174273641279176060045 1843940352615479691022517)
                      ·
                        rfl

theorem cell23_3591061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_3591061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591061 prefixEnd_3591061 := by exact prefixLift 3591061
  have htrace : WordTrace (prefixWord ++ tailWord_3591061) baseStart_3591061 baseEnd_3591061 := by
    simpa [prefixWord, tailWord_3591061, baseEnd_3591061] using wordTrace_append hprefix tailTrace_3591061
  have hstable : (prefixWord ++ tailWord_3591061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591061).length < 2 ^ (prefixWord ++ tailWord_3591061).sum := by decide
  have hdescent : baseEnd_3591061 < baseStart_3591061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591068 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3591068 : Nat := 118140960795 + 3591068 * 2 ^ 59
def prefixEnd_3591068 : Nat := 4983230072969 + 3 ^ 40 * 3591068 * 2
def baseEnd_3591068 : Nat := 614647982326687054544995

theorem tailTrace_3591068 : CollatzResearch.WordTrace tailWord_3591068 prefixEnd_3591068 614647982326687054544995 := by
  unfold tailWord_3591068
  simp only [CollatzResearch.WordTrace]
  refine ⟨65488505077090708215878929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87318006769454277621171905 65488505077090708215878929)
  ·
    refine ⟨49116378807818031161909197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65488505077090708215878929 49116378807818031161909197)
    ·
      refine ⟨18418642052931761685715949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49116378807818031161909197 18418642052931761685715949)
      ·
        refine ⟨6906990769849410632143481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18418642052931761685715949 6906990769849410632143481)
        ·
          refine ⟨5180243077387057974107611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906990769849410632143481 5180243077387057974107611)
          ·
            refine ⟨7770364616080586961161417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180243077387057974107611 7770364616080586961161417)
            ·
              refine ⟨5827773462060440220871063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770364616080586961161417 5827773462060440220871063)
              ·
                refine ⟨8741660193090660331306595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827773462060440220871063 8741660193090660331306595)
                ·
                  refine ⟨13112490289635990496959893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741660193090660331306595 13112490289635990496959893)
                  ·
                    refine ⟨614647982326687054544995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13112490289635990496959893 614647982326687054544995)
                    ·
                      rfl

theorem cell23_3591068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3591068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591068 prefixEnd_3591068 := by exact prefixLift 3591068
  have htrace : WordTrace (prefixWord ++ tailWord_3591068) baseStart_3591068 baseEnd_3591068 := by
    simpa [prefixWord, tailWord_3591068, baseEnd_3591068] using wordTrace_append hprefix tailTrace_3591068
  have hstable : (prefixWord ++ tailWord_3591068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591068).length < 2 ^ (prefixWord ++ tailWord_3591068).sum := by decide
  have hdescent : baseEnd_3591068 < baseStart_3591068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591071 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3591071 : Nat := 118140960795 + 3591071 * 2 ^ 59
def prefixEnd_3591071 : Nat := 4983230072969 + 3 ^ 40 * 3591071 * 2
def baseEnd_3591071 : Nat := 1843945487422024651897471

theorem tailTrace_3591071 : CollatzResearch.WordTrace tailWord_3591071 prefixEnd_3591071 1843945487422024651897471 := by
  unfold tailWord_3591071
  simp only [CollatzResearch.WordTrace]
  refine ⟨130977119573170547944117067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87318079715447031962744711 130977119573170547944117067)
  ·
    refine ⟨196465679359755821916175601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130977119573170547944117067 196465679359755821916175601)
    ·
      refine ⟨147349259519816866437131701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196465679359755821916175601 147349259519816866437131701)
      ·
        refine ⟨13813993079982831228481097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147349259519816866437131701 13813993079982831228481097)
        ·
          refine ⟨10360494809987123421360823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13813993079982831228481097 10360494809987123421360823)
          ·
            refine ⟨15540742214980685132041235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360494809987123421360823 15540742214980685132041235)
            ·
              refine ⟨23311113322471027698061853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540742214980685132041235 23311113322471027698061853)
              ·
                refine ⟨8741667495926635386773195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23311113322471027698061853 8741667495926635386773195)
                ·
                  refine ⟨13112501243889953080159793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741667495926635386773195 13112501243889953080159793)
                  ·
                    refine ⟨9834375932917464810119845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13112501243889953080159793 9834375932917464810119845)
                    ·
                      refine ⟨1843945487422024651897471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9834375932917464810119845 1843945487422024651897471)
                      ·
                        rfl

theorem cell23_3591071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3591071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591071 prefixEnd_3591071 := by exact prefixLift 3591071
  have htrace : WordTrace (prefixWord ++ tailWord_3591071) baseStart_3591071 baseEnd_3591071 := by
    simpa [prefixWord, tailWord_3591071, baseEnd_3591071] using wordTrace_append hprefix tailTrace_3591071
  have hstable : (prefixWord ++ tailWord_3591071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591071).length < 2 ^ (prefixWord ++ tailWord_3591071).sum := by decide
  have hdescent : baseEnd_3591071 < baseStart_3591071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591092 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3591092 : Nat := 118140960795 + 3591092 * 2 ^ 59
def prefixEnd_3591092 : Nat := 4983230072969 + 3 ^ 40 * 3591092 * 2
def baseEnd_3591092 : Nat := 1843956270515769069734875

theorem tailTrace_3591092 : CollatzResearch.WordTrace tailWord_3591092 prefixEnd_3591092 1843956270515769069734875 := by
  unfold tailWord_3591092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65488942753047234265315765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87318590337396312353754353 65488942753047234265315765)
  ·
    refine ⟨6139588383098178212373353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65488942753047234265315765 6139588383098178212373353)
    ·
      refine ⟨4604691287323633659280015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139588383098178212373353 4604691287323633659280015)
      ·
        refine ⟨6907036930985450488920023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604691287323633659280015 6907036930985450488920023)
        ·
          refine ⟨10360555396478175733380035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907036930985450488920023 10360555396478175733380035)
          ·
            refine ⟨15540833094717263600070053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360555396478175733380035 15540833094717263600070053)
            ·
              refine ⟨2913906205259486925013135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15540833094717263600070053 2913906205259486925013135)
              ·
                refine ⟨4370859307889230387519703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913906205259486925013135 4370859307889230387519703)
                ·
                  refine ⟨6556288961833845581279555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370859307889230387519703 6556288961833845581279555)
                  ·
                    refine ⟨9834433442750768371919333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6556288961833845581279555 9834433442750768371919333)
                    ·
                      refine ⟨1843956270515769069734875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9834433442750768371919333 1843956270515769069734875)
                      ·
                        rfl

theorem cell23_3591092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3591092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591092 prefixEnd_3591092 := by exact prefixLift 3591092
  have htrace : WordTrace (prefixWord ++ tailWord_3591092) baseStart_3591092 baseEnd_3591092 := by
    simpa [prefixWord, tailWord_3591092, baseEnd_3591092] using wordTrace_append hprefix tailTrace_3591092
  have hstable : (prefixWord ++ tailWord_3591092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591092).length < 2 ^ (prefixWord ++ tailWord_3591092).sum := by decide
  have hdescent : baseEnd_3591092 < baseStart_3591092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591125 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3591125 : Nat := 118140960795 + 3591125 * 2 ^ 59
def prefixEnd_3591125 : Nat := 4983230072969 + 3 ^ 40 * 3591125 * 2
def baseEnd_3591125 : Nat := 1843973215377367440622223

theorem tailTrace_3591125 : CollatzResearch.WordTrace tailWord_3591125 prefixEnd_3591125 1843973215377367440622223 := by
  unfold tailWord_3591125
  simp only [CollatzResearch.WordTrace]
  refine ⟨130979089114974915166582829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87319392743316610111055219 130979089114974915166582829)
  ·
    refine ⟨49117158418115593187468561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130979089114974915166582829 49117158418115593187468561)
    ·
      refine ⟨36837868813586694890601421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49117158418115593187468561 36837868813586694890601421)
      ·
        refine ⟨13814200805095010583975533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36837868813586694890601421 13814200805095010583975533)
        ·
          refine ⟨5180325301910628968990825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13814200805095010583975533 5180325301910628968990825)
          ·
            refine ⟨3885243976432971726743119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180325301910628968990825 3885243976432971726743119)
            ·
              refine ⟨5827865964649457590114679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885243976432971726743119 5827865964649457590114679)
              ·
                refine ⟨8741798946974186385172019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827865964649457590114679 8741798946974186385172019)
                ·
                  refine ⟨13112698420461279577758029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741798946974186385172019 13112698420461279577758029)
                  ·
                    refine ⟨4917261907672979841659261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13112698420461279577758029 4917261907672979841659261)
                    ·
                      refine ⟨1843973215377367440622223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917261907672979841659261 1843973215377367440622223)
                      ·
                        rfl

theorem cell23_3591125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3591125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591125 prefixEnd_3591125 := by exact prefixLift 3591125
  have htrace : WordTrace (prefixWord ++ tailWord_3591125) baseStart_3591125 baseEnd_3591125 := by
    simpa [prefixWord, tailWord_3591125, baseEnd_3591125] using wordTrace_append hprefix tailTrace_3591125
  have hstable : (prefixWord ++ tailWord_3591125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591125).length < 2 ^ (prefixWord ++ tailWord_3591125).sum := by decide
  have hdescent : baseEnd_3591125 < baseStart_3591125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591138 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3591138 : Nat := 118140960795 + 3591138 * 2 ^ 59
def prefixEnd_3591138 : Nat := 4983230072969 + 3 ^ 40 * 3591138 * 2
def baseEnd_3591138 : Nat := 1843979890625875889759663

theorem tailTrace_3591138 : CollatzResearch.WordTrace tailWord_3591138 prefixEnd_3591138 1843979890625875889759663 := by
  unfold tailWord_3591138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32744890815981954596701517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87319708842618545591204045 32744890815981954596701517)
  ·
    refine ⟨12279334055993232973763069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32744890815981954596701517 12279334055993232973763069)
    ·
      refine ⟨4604750270997462365161151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12279334055993232973763069 4604750270997462365161151)
      ·
        refine ⟨6907125406496193547741727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604750270997462365161151 6907125406496193547741727)
        ·
          refine ⟨10360688109744290321612591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907125406496193547741727 10360688109744290321612591)
          ·
            refine ⟨15541032164616435482418887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360688109744290321612591 15541032164616435482418887)
            ·
              refine ⟨23311548246924653223628331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541032164616435482418887 23311548246924653223628331)
              ·
                refine ⟨34967322370386979835442497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23311548246924653223628331 34967322370386979835442497)
                ·
                  refine ⟨26225491777790234876581873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34967322370386979835442497 26225491777790234876581873)
                  ·
                    refine ⟨19669118833342676157436405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26225491777790234876581873 19669118833342676157436405)
                    ·
                      refine ⟨1843979890625875889759663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19669118833342676157436405 1843979890625875889759663)
                      ·
                        rfl

theorem cell23_3591138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3591138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591138 prefixEnd_3591138 := by exact prefixLift 3591138
  have htrace : WordTrace (prefixWord ++ tailWord_3591138) baseStart_3591138 baseEnd_3591138 := by
    simpa [prefixWord, tailWord_3591138, baseEnd_3591138] using wordTrace_append hprefix tailTrace_3591138
  have hstable : (prefixWord ++ tailWord_3591138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591138).length < 2 ^ (prefixWord ++ tailWord_3591138).sum := by decide
  have hdescent : baseEnd_3591138 < baseStart_3591138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591151 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_3591151 : Nat := 118140960795 + 3591151 * 2 ^ 59
def prefixEnd_3591151 : Nat := 4983230072969 + 3 ^ 40 * 3591151 * 2
def baseEnd_3591151 : Nat := 1843986565874384338897103

theorem tailTrace_3591151 : CollatzResearch.WordTrace tailWord_3591151 prefixEnd_3591151 1843986565874384338897103 := by
  unfold tailWord_3591151
  simp only [CollatzResearch.WordTrace]
  refine ⟨130980037412880721607029307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87320024941920481071352871 130980037412880721607029307)
  ·
    refine ⟨196470056119321082410543961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130980037412880721607029307 196470056119321082410543961)
    ·
      refine ⟨147352542089490811807907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196470056119321082410543961 147352542089490811807907971)
      ·
        refine ⟨221028813134236217711861957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147352542089490811807907971 221028813134236217711861957)
        ·
          refine ⟨41442902462669290820974117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221028813134236217711861957 41442902462669290820974117)
          ·
            refine ⟨7770544211750492028932647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41442902462669290820974117 7770544211750492028932647)
            ·
              refine ⟨11655816317625738043398971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770544211750492028932647 11655816317625738043398971)
              ·
                refine ⟨17483724476438607065098457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655816317625738043398971 17483724476438607065098457)
                ·
                  refine ⟨13112793357328955298823843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17483724476438607065098457 13112793357328955298823843)
                  ·
                    refine ⟨19669190035993432948235765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13112793357328955298823843 19669190035993432948235765)
                    ·
                      refine ⟨1843986565874384338897103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19669190035993432948235765 1843986565874384338897103)
                      ·
                        rfl

theorem cell23_3591151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_3591151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591151 prefixEnd_3591151 := by exact prefixLift 3591151
  have htrace : WordTrace (prefixWord ++ tailWord_3591151) baseStart_3591151 baseEnd_3591151 := by
    simpa [prefixWord, tailWord_3591151, baseEnd_3591151] using wordTrace_append hprefix tailTrace_3591151
  have hstable : (prefixWord ++ tailWord_3591151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591151).length < 2 ^ (prefixWord ++ tailWord_3591151).sum := by decide
  have hdescent : baseEnd_3591151 < baseStart_3591151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591165 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_3591165 : Nat := 118140960795 + 3591165 * 2 ^ 59
def prefixEnd_3591165 : Nat := 4983230072969 + 3 ^ 40 * 3591165 * 2
def baseEnd_3591165 : Nat := 1843993754603547284122039

theorem tailTrace_3591165 : CollatzResearch.WordTrace tailWord_3591165 prefixEnd_3591165 1843993754603547284122039 := by
  unfold tailWord_3591165
  simp only [CollatzResearch.WordTrace]
  refine ⟨130980548034830001998038949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87320365356553334665359299 130980548034830001998038949)
  ·
    refine ⟨24558852756530625374632303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130980548034830001998038949 24558852756530625374632303)
    ·
      refine ⟨36838279134795938061948455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24558852756530625374632303 36838279134795938061948455)
      ·
        refine ⟨55257418702193907092922683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36838279134795938061948455 55257418702193907092922683)
        ·
          refine ⟨82886128053290860639384025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55257418702193907092922683 82886128053290860639384025)
          ·
            refine ⟨62164596039968145479538019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82886128053290860639384025 62164596039968145479538019)
            ·
              refine ⟨93246894059952218219307029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62164596039968145479538019 93246894059952218219307029)
              ·
                refine ⟨4370948159060260229030017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93246894059952218219307029 4370948159060260229030017)
                ·
                  refine ⟨3278211119295195171772513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370948159060260229030017 3278211119295195171772513)
                  ·
                    refine ⟨2458658339471396378829385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3278211119295195171772513 2458658339471396378829385)
                    ·
                      refine ⟨1843993754603547284122039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458658339471396378829385 1843993754603547284122039)
                      ·
                        rfl

theorem cell23_3591165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_3591165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591165 prefixEnd_3591165 := by exact prefixLift 3591165
  have htrace : WordTrace (prefixWord ++ tailWord_3591165) baseStart_3591165 baseEnd_3591165 := by
    simpa [prefixWord, tailWord_3591165, baseEnd_3591165] using wordTrace_append hprefix tailTrace_3591165
  have hstable : (prefixWord ++ tailWord_3591165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591165).length < 2 ^ (prefixWord ++ tailWord_3591165).sum := by decide
  have hdescent : baseEnd_3591165 < baseStart_3591165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591182 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3591182 : Nat := 118140960795 + 3591182 * 2 ^ 59
def prefixEnd_3591182 : Nat := 4983230072969 + 3 ^ 40 * 3591182 * 2
def baseEnd_3591182 : Nat := 1844002483774673717609461

theorem tailTrace_3591182 : CollatzResearch.WordTrace tailWord_3591182 prefixEnd_3591182 1844002483774673717609461 := by
  unfold tailWord_3591182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372646009471051737675975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87320778717178942600938533 16372646009471051737675975)
  ·
    refine ⟨24558969014206577606513963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372646009471051737675975 24558969014206577606513963)
    ·
      refine ⟨36838453521309866409770945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24558969014206577606513963 36838453521309866409770945)
      ·
        refine ⟨27628840140982399807328209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36838453521309866409770945 27628840140982399807328209)
        ·
          refine ⟨20721630105736799855496157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27628840140982399807328209 20721630105736799855496157)
          ·
            refine ⟨7770611289651299945811059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20721630105736799855496157 7770611289651299945811059)
            ·
              refine ⟨11655916934476949918716589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770611289651299945811059 11655916934476949918716589)
              ·
                refine ⟨4370968850428856219518721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11655916934476949918716589 4370968850428856219518721)
                ·
                  refine ⟨3278226637821642164639041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370968850428856219518721 3278226637821642164639041)
                  ·
                    refine ⟨2458669978366231623479281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3278226637821642164639041 2458669978366231623479281)
                    ·
                      refine ⟨1844002483774673717609461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458669978366231623479281 1844002483774673717609461)
                      ·
                        rfl

theorem cell23_3591182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3591182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591182 prefixEnd_3591182 := by exact prefixLift 3591182
  have htrace : WordTrace (prefixWord ++ tailWord_3591182) baseStart_3591182 baseEnd_3591182 := by
    simpa [prefixWord, tailWord_3591182, baseEnd_3591182] using wordTrace_append hprefix tailTrace_3591182
  have hstable : (prefixWord ++ tailWord_3591182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591182).length < 2 ^ (prefixWord ++ tailWord_3591182).sum := by decide
  have hdescent : baseEnd_3591182 < baseStart_3591182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591221 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3591221 : Nat := 118140960795 + 3591221 * 2 ^ 59
def prefixEnd_3591221 : Nat := 4983230072969 + 3 ^ 40 * 3591221 * 2
def baseEnd_3591221 : Nat := 1844022509520199065021781

theorem tailTrace_3591221 : CollatzResearch.WordTrace tailWord_3591221 prefixEnd_3591221 1844022509520199065021781 := by
  unfold tailWord_3591221
  simp only [CollatzResearch.WordTrace]
  refine ⟨130982590522627123562077517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87321727015084749041385011 130982590522627123562077517)
  ·
    refine ⟨49118471445985171335779069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130982590522627123562077517 49118471445985171335779069)
    ·
      refine ⟨18419426792244439250917151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49118471445985171335779069 18419426792244439250917151)
      ·
        refine ⟨27629140188366658876375727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18419426792244439250917151 27629140188366658876375727)
        ·
          refine ⟨41443710282549988314563591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27629140188366658876375727 41443710282549988314563591)
          ·
            refine ⟨62165565423824982471845387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41443710282549988314563591 62165565423824982471845387)
            ·
              refine ⟨93248348135737473707768081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62165565423824982471845387 93248348135737473707768081)
              ·
                refine ⟨69936261101803105280826061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93248348135737473707768081 69936261101803105280826061)
                ·
                  refine ⟨26226097913176164480309773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69936261101803105280826061 26226097913176164480309773)
                  ·
                    refine ⟨9834786717441061680116165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26226097913176164480309773 9834786717441061680116165)
                    ·
                      refine ⟨1844022509520199065021781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9834786717441061680116165 1844022509520199065021781)
                      ·
                        rfl

theorem cell23_3591221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3591221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591221 prefixEnd_3591221 := by exact prefixLift 3591221
  have htrace : WordTrace (prefixWord ++ tailWord_3591221) baseStart_3591221 baseEnd_3591221 := by
    simpa [prefixWord, tailWord_3591221, baseEnd_3591221] using wordTrace_append hprefix tailTrace_3591221
  have hstable : (prefixWord ++ tailWord_3591221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591221).length < 2 ^ (prefixWord ++ tailWord_3591221).sum := by decide
  have hdescent : baseEnd_3591221 < baseStart_3591221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591222 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_3591222 : Nat := 118140960795 + 3591222 * 2 ^ 59
def prefixEnd_3591222 : Nat := 4983230072969 + 3 ^ 40 * 3591222 * 2
def baseEnd_3591222 : Nat := 204891447000094840123253

theorem tailTrace_3591222 : CollatzResearch.WordTrace tailWord_3591222 prefixEnd_3591222 204891447000094840123253 := by
  unfold tailWord_3591222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186414187226468795803995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87321751330415667155242613 8186414187226468795803995)
  ·
    refine ⟨12279621280839703193705993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8186414187226468795803995 12279621280839703193705993)
    ·
      refine ⟨9209715960629777395279495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12279621280839703193705993 9209715960629777395279495)
      ·
        refine ⟨13814573940944666092919243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209715960629777395279495 13814573940944666092919243)
        ·
          refine ⟨20721860911416999139378865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814573940944666092919243 20721860911416999139378865)
          ·
            refine ⟨15541395683562749354534149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20721860911416999139378865 15541395683562749354534149)
            ·
              refine ⟨2914011690668015503975153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15541395683562749354534149 2914011690668015503975153)
              ·
                refine ⟨2185508768001011627981365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914011690668015503975153 2185508768001011627981365)
                ·
                  refine ⟨204891447000094840123253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185508768001011627981365 204891447000094840123253)
                  ·
                    rfl

theorem cell23_3591222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_3591222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591222 prefixEnd_3591222 := by exact prefixLift 3591222
  have htrace : WordTrace (prefixWord ++ tailWord_3591222) baseStart_3591222 baseEnd_3591222 := by
    simpa [prefixWord, tailWord_3591222, baseEnd_3591222] using wordTrace_append hprefix tailTrace_3591222
  have hstable : (prefixWord ++ tailWord_3591222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591222).length < 2 ^ (prefixWord ++ tailWord_3591222).sum := by decide
  have hdescent : baseEnd_3591222 < baseStart_3591222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591258 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_3591258 : Nat := 118140960795 + 3591258 * 2 ^ 59
def prefixEnd_3591258 : Nat := 4983230072969 + 3 ^ 40 * 3591258 * 2
def baseEnd_3591258 : Nat := 1844041508304415420259111

theorem tailTrace_3591258 : CollatzResearch.WordTrace tailWord_3591258 prefixEnd_3591258 1844041508304415420259111 := by
  unfold tailWord_3591258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745985005873269720293607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87322626682328719254116285 32745985005873269720293607)
  ·
    refine ⟨49118977508809904580440411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32745985005873269720293607 49118977508809904580440411)
    ·
      refine ⟨73678466263214856870660617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49118977508809904580440411 73678466263214856870660617)
      ·
        refine ⟨55258849697411142652995463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73678466263214856870660617 55258849697411142652995463)
        ·
          refine ⟨82888274546116713979493195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55258849697411142652995463 82888274546116713979493195)
          ·
            refine ⟨124332411819175070969239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82888274546116713979493195 124332411819175070969239793)
            ·
              refine ⟨93249308864381303226929845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124332411819175070969239793 93249308864381303226929845)
              ·
                refine ⟨8742122706035747177524673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93249308864381303226929845 8742122706035747177524673)
                ·
                  refine ⟨6556592029526810383143505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8742122706035747177524673 6556592029526810383143505)
                  ·
                    refine ⟨4917444022145107787357629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6556592029526810383143505 4917444022145107787357629)
                    ·
                      refine ⟨1844041508304415420259111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917444022145107787357629 1844041508304415420259111)
                      ·
                        rfl

theorem cell23_3591258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_3591258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591258 prefixEnd_3591258 := by exact prefixLift 3591258
  have htrace : WordTrace (prefixWord ++ tailWord_3591258) baseStart_3591258 baseEnd_3591258 := by
    simpa [prefixWord, tailWord_3591258, baseEnd_3591258] using wordTrace_append hprefix tailTrace_3591258
  have hstable : (prefixWord ++ tailWord_3591258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591258).length < 2 ^ (prefixWord ++ tailWord_3591258).sum := by decide
  have hdescent : baseEnd_3591258 < baseStart_3591258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591265 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3591265 : Nat := 118140960795 + 3591265 * 2 ^ 59
def prefixEnd_3591265 : Nat := 4983230072969 + 3 ^ 40 * 3591265 * 2
def baseEnd_3591265 : Nat := 614681700889665630957193

theorem tailTrace_3591265 : CollatzResearch.WordTrace tailWord_3591265 prefixEnd_3591265 614681700889665630957193 := by
  unfold tailWord_3591265
  simp only [CollatzResearch.WordTrace]
  refine ⟨130984195334467719076679249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87322796889645146051119499 130984195334467719076679249)
  ·
    refine ⟨98238146500850789307509437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130984195334467719076679249 98238146500850789307509437)
    ·
      refine ⟨36839304937819045990316039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98238146500850789307509437 36839304937819045990316039)
      ·
        refine ⟨55258957406728568985474059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36839304937819045990316039 55258957406728568985474059)
        ·
          refine ⟨82888436110092853478211089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55258957406728568985474059 82888436110092853478211089)
          ·
            refine ⟨62166327082569640108658317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82888436110092853478211089 62166327082569640108658317)
            ·
              refine ⟨23312372655963615040746869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62166327082569640108658317 23312372655963615040746869)
              ·
                refine ⟨2185534936496588910070019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23312372655963615040746869 2185534936496588910070019)
                ·
                  refine ⟨3278302404744883365105029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185534936496588910070019 3278302404744883365105029)
                  ·
                    refine ⟨614681700889665630957193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278302404744883365105029 614681700889665630957193)
                    ·
                      rfl

theorem cell23_3591265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3591265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591265 prefixEnd_3591265 := by exact prefixLift 3591265
  have htrace : WordTrace (prefixWord ++ tailWord_3591265) baseStart_3591265 baseEnd_3591265 := by
    simpa [prefixWord, tailWord_3591265, baseEnd_3591265] using wordTrace_append hprefix tailTrace_3591265
  have hstable : (prefixWord ++ tailWord_3591265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591265).length < 2 ^ (prefixWord ++ tailWord_3591265).sum := by decide
  have hdescent : baseEnd_3591265 < baseStart_3591265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591278 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_3591278 : Nat := 118140960795 + 3591278 * 2 ^ 59
def prefixEnd_3591278 : Nat := 4983230072969 + 3 ^ 40 * 3591278 * 2
def baseEnd_3591278 : Nat := 204894641990833926889891

theorem tailTrace_3591278 : CollatzResearch.WordTrace tailWord_3591278 prefixEnd_3591278 204894641990833926889891 := by
  unfold tailWord_3591278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373083685427577787112811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87323112988947081531268325 16373083685427577787112811)
  ·
    refine ⟨24559625528141366680669217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16373083685427577787112811 24559625528141366680669217)
    ·
      refine ⟨18419719146106025010501913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24559625528141366680669217 18419719146106025010501913)
      ·
        refine ⟨13814789359579518757876435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18419719146106025010501913 13814789359579518757876435)
        ·
          refine ⟨20722184039369278136814653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814789359579518757876435 20722184039369278136814653)
          ·
            refine ⟨7770819014763479301305495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20722184039369278136814653 7770819014763479301305495)
            ·
              refine ⟨11656228522145218951958243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770819014763479301305495 11656228522145218951958243)
              ·
                refine ⟨17484342783217828427937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11656228522145218951958243 17484342783217828427937365)
                ·
                  refine ⟨204894641990833926889891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17484342783217828427937365 204894641990833926889891)
                  ·
                    rfl

theorem cell23_3591278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_3591278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591278 prefixEnd_3591278 := by exact prefixLift 3591278
  have htrace : WordTrace (prefixWord ++ tailWord_3591278) baseStart_3591278 baseEnd_3591278 := by
    simpa [prefixWord, tailWord_3591278, baseEnd_3591278] using wordTrace_append hprefix tailTrace_3591278
  have hstable : (prefixWord ++ tailWord_3591278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591278).length < 2 ^ (prefixWord ++ tailWord_3591278).sum := by decide
  have hdescent : baseEnd_3591278 < baseStart_3591278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591291 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 5, 5]
def baseStart_3591291 : Nat := 118140960795 + 3591291 * 2 ^ 59
def prefixEnd_3591291 : Nat := 4983230072969 + 3 ^ 40 * 3591291 * 2
def baseEnd_3591291 : Nat := 614686151055337930382153

theorem tailTrace_3591291 : CollatzResearch.WordTrace tailWord_3591291 prefixEnd_3591291 614686151055337930382153 := by
  unfold tailWord_3591291
  simp only [CollatzResearch.WordTrace]
  refine ⟨130985143632373525517125727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87323429088249017011417151 130985143632373525517125727)
  ·
    refine ⟨196477715448560288275688591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130985143632373525517125727 196477715448560288275688591)
    ·
      refine ⟨294716573172840432413532887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196477715448560288275688591 294716573172840432413532887)
      ·
        refine ⟨442074859759260648620299331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294716573172840432413532887 442074859759260648620299331)
        ·
          refine ⟨663112289638890972930448997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442074859759260648620299331 663112289638890972930448997)
          ·
            refine ⟨124333554307292057424459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663112289638890972930448997 124333554307292057424459187)
            ·
              refine ⟨186500331460938086136688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124333554307292057424459187 186500331460938086136688781)
              ·
                refine ⟨69937624297851782301258293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186500331460938086136688781 69937624297851782301258293)
                ·
                  refine ⟨6556652277923604590742965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69937624297851782301258293 6556652277923604590742965)
                  ·
                    refine ⟨614686151055337930382153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6556652277923604590742965 614686151055337930382153)
                    ·
                      rfl

theorem cell23_3591291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].length) (baseStart_3591291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591291 prefixEnd_3591291 := by exact prefixLift 3591291
  have htrace : WordTrace (prefixWord ++ tailWord_3591291) baseStart_3591291 baseEnd_3591291 := by
    simpa [prefixWord, tailWord_3591291, baseEnd_3591291] using wordTrace_append hprefix tailTrace_3591291
  have hstable : (prefixWord ++ tailWord_3591291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591291).length < 2 ^ (prefixWord ++ tailWord_3591291).sum := by decide
  have hdescent : baseEnd_3591291 < baseStart_3591291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591305 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_3591305 : Nat := 118140960795 + 3591305 * 2 ^ 59
def prefixEnd_3591305 : Nat := 4983230072969 + 3 ^ 40 * 3591305 * 2
def baseEnd_3591305 : Nat := 1844065641895176736371395

theorem tailTrace_3591305 : CollatzResearch.WordTrace tailWord_3591305 prefixEnd_3591305 1844065641895176736371395 := by
  unfold tailWord_3591305
  simp only [CollatzResearch.WordTrace]
  refine ⟨130985654254322805908135369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87323769502881870605423579 130985654254322805908135369)
  ·
    refine ⟨98239240690742104431101527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130985654254322805908135369 98239240690742104431101527)
    ·
      refine ⟨147358861036113156646652291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98239240690742104431101527 147358861036113156646652291)
      ·
        refine ⟨221038291554169734969978437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147358861036113156646652291 221038291554169734969978437)
        ·
          refine ⟨41444679666406825306870957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221038291554169734969978437 41444679666406825306870957)
          ·
            refine ⟨15541754874902559490076609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41444679666406825306870957 15541754874902559490076609)
            ·
              refine ⟨11656316156176919617557457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15541754874902559490076609 11656316156176919617557457)
              ·
                refine ⟨8742237117132689713168093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11656316156176919617557457 8742237117132689713168093)
                ·
                  refine ⟨3278338918924758642438035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8742237117132689713168093 3278338918924758642438035)
                  ·
                    refine ⟨4917508378387137963657053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278338918924758642438035 4917508378387137963657053)
                    ·
                      refine ⟨1844065641895176736371395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917508378387137963657053 1844065641895176736371395)
                      ·
                        rfl

theorem cell23_3591305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_3591305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591305 prefixEnd_3591305 := by exact prefixLift 3591305
  have htrace : WordTrace (prefixWord ++ tailWord_3591305) baseStart_3591305 baseEnd_3591305 := by
    simpa [prefixWord, tailWord_3591305, baseEnd_3591305] using wordTrace_append hprefix tailTrace_3591305
  have hstable : (prefixWord ++ tailWord_3591305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591305).length < 2 ^ (prefixWord ++ tailWord_3591305).sum := by decide
  have hdescent : baseEnd_3591305 < baseStart_3591305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591332 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_3591332 : Nat := 118140960795 + 3591332 * 2 ^ 59
def prefixEnd_3591332 : Nat := 4983230072969 + 3 ^ 40 * 3591332 * 2
def baseEnd_3591332 : Nat := 1844079505872848130733771

theorem tailTrace_3591332 : CollatzResearch.WordTrace tailWord_3591332 prefixEnd_3591332 1844079505872848130733771 := by
  unfold tailWord_3591332
  simp only [CollatzResearch.WordTrace]
  refine ⟨65493319512612494759684125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87324426016816659679578833 65493319512612494759684125)
  ·
    refine ⟨24559994817229685534881547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65493319512612494759684125 24559994817229685534881547)
    ·
      refine ⟨36839992225844528302322321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24559994817229685534881547 36839992225844528302322321)
      ·
        refine ⟨27629994169383396226741741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36839992225844528302322321 27629994169383396226741741)
        ·
          refine ⟨10361247813518773585028153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27629994169383396226741741 10361247813518773585028153)
          ·
            refine ⟨7770935860139080188771115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361247813518773585028153 7770935860139080188771115)
            ·
              refine ⟨11656403790208620283156673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770935860139080188771115 11656403790208620283156673)
              ·
                refine ⟨8742302842656465212367505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11656403790208620283156673 8742302842656465212367505)
                ·
                  refine ⟨6556727131992348909275629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8742302842656465212367505 6556727131992348909275629)
                  ·
                    refine ⟨2458772674497130840978361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6556727131992348909275629 2458772674497130840978361)
                    ·
                      refine ⟨1844079505872848130733771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458772674497130840978361 1844079505872848130733771)
                      ·
                        rfl

theorem cell23_3591332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_3591332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591332 prefixEnd_3591332 := by exact prefixLift 3591332
  have htrace : WordTrace (prefixWord ++ tailWord_3591332) baseStart_3591332 baseEnd_3591332 := by
    simpa [prefixWord, tailWord_3591332, baseEnd_3591332] using wordTrace_append hprefix tailTrace_3591332
  have hstable : (prefixWord ++ tailWord_3591332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591332).length < 2 ^ (prefixWord ++ tailWord_3591332).sum := by decide
  have hdescent : baseEnd_3591332 < baseStart_3591332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591389 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3591389 : Nat := 118140960795 + 3591389 * 2 ^ 59
def prefixEnd_3591389 : Nat := 4983230072969 + 3 ^ 40 * 3591389 * 2
def baseEnd_3591389 : Nat := 614702924756718135907003

theorem tailTrace_3591389 : CollatzResearch.WordTrace tailWord_3591389 prefixEnd_3591389 614702924756718135907003 := by
  unfold tailWord_3591389
  simp only [CollatzResearch.WordTrace]
  refine ⟨130988717986018488254193221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87325811990678992169462147 130988717986018488254193221)
  ·
    refine ⟨24560384622378466547661229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130988717986018488254193221 24560384622378466547661229)
    ·
      refine ⟨9210144233391924955372961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24560384622378466547661229 9210144233391924955372961)
      ·
        refine ⟨6907608175043943716529721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9210144233391924955372961 6907608175043943716529721)
        ·
          refine ⟨5180706131282957787397291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6907608175043943716529721 5180706131282957787397291)
          ·
            refine ⟨7771059196924436681095937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180706131282957787397291 7771059196924436681095937)
            ·
              refine ⟨5828294397693327510821953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771059196924436681095937 5828294397693327510821953)
              ·
                refine ⟨4371220798269995633116465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828294397693327510821953 4371220798269995633116465)
                ·
                  refine ⟨3278415598702496724837349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371220798269995633116465 3278415598702496724837349)
                  ·
                    refine ⟨614702924756718135907003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278415598702496724837349 614702924756718135907003)
                    ·
                      rfl

theorem cell23_3591389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3591389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591389 prefixEnd_3591389 := by exact prefixLift 3591389
  have htrace : WordTrace (prefixWord ++ tailWord_3591389) baseStart_3591389 baseEnd_3591389 := by
    simpa [prefixWord, tailWord_3591389, baseEnd_3591389] using wordTrace_append hprefix tailTrace_3591389
  have hstable : (prefixWord ++ tailWord_3591389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591389).length < 2 ^ (prefixWord ++ tailWord_3591389).sum := by decide
  have hdescent : baseEnd_3591389 < baseStart_3591389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591396 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_3591396 : Nat := 118140960795 + 3591396 * 2 ^ 59
def prefixEnd_3591396 : Nat := 4983230072969 + 3 ^ 40 * 3591396 * 2
def baseEnd_3591396 : Nat := 1844112368634735880333477

theorem tailTrace_3591396 : CollatzResearch.WordTrace tailWord_3591396 prefixEnd_3591396 1844112368634735880333477 := by
  unfold tailWord_3591396
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494486648496564224849021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87325982197995418966465361 65494486648496564224849021)
  ·
    refine ⟨24560432493186211584318383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65494486648496564224849021 24560432493186211584318383)
    ·
      refine ⟨36840648739779317376477575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24560432493186211584318383 36840648739779317376477575)
      ·
        refine ⟨55260973109668976064716363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36840648739779317376477575 55260973109668976064716363)
        ·
          refine ⟨82891459664503464097074545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55260973109668976064716363 82891459664503464097074545)
          ·
            refine ⟨62168594748377598072805909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82891459664503464097074545 62168594748377598072805909)
            ·
              refine ⟨2914152878830199909662777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62168594748377598072805909 2914152878830199909662777)
              ·
                refine ⟨2185614659122649932247083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914152878830199909662777 2185614659122649932247083)
                ·
                  refine ⟨3278421988683974898370625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185614659122649932247083 3278421988683974898370625)
                  ·
                    refine ⟨2458816491512981173777969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3278421988683974898370625 2458816491512981173777969)
                    ·
                      refine ⟨1844112368634735880333477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2458816491512981173777969 1844112368634735880333477)
                      ·
                        rfl

theorem cell23_3591396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_3591396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591396 prefixEnd_3591396 := by exact prefixLift 3591396
  have htrace : WordTrace (prefixWord ++ tailWord_3591396) baseStart_3591396 baseEnd_3591396 := by
    simpa [prefixWord, tailWord_3591396, baseEnd_3591396] using wordTrace_append hprefix tailTrace_3591396
  have hstable : (prefixWord ++ tailWord_3591396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591396).length < 2 ^ (prefixWord ++ tailWord_3591396).sum := by decide
  have hdescent : baseEnd_3591396 < baseStart_3591396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591418 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_3591418 : Nat := 118140960795 + 3591418 * 2 ^ 59
def prefixEnd_3591418 : Nat := 4983230072969 + 3 ^ 40 * 3591418 * 2
def baseEnd_3591418 : Nat := 1844123665209134794258375

theorem tailTrace_3591418 : CollatzResearch.WordTrace tailWord_3591418 prefixEnd_3591418 1844123665209134794258375 := by
  unfold tailWord_3591418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747443925728356551749727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87326517135275617471332605 32747443925728356551749727)
  ·
    refine ⟨49121165888592534827624591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747443925728356551749727 49121165888592534827624591)
    ·
      refine ⟨73681748832888802241436887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49121165888592534827624591 73681748832888802241436887)
      ·
        refine ⟨110522623249333203362155331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73681748832888802241436887 110522623249333203362155331)
        ·
          refine ⟨165783934873999805043232997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110522623249333203362155331 165783934873999805043232997)
          ·
            refine ⟨31084487788874963445606187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165783934873999805043232997 31084487788874963445606187)
            ·
              refine ⟨46626731683312445168409281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31084487788874963445606187 46626731683312445168409281)
              ·
                refine ⟨34970048762484333876306961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46626731683312445168409281 34970048762484333876306961)
                ·
                  refine ⟨26227536571863250407230221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34970048762484333876306961 26227536571863250407230221)
                  ·
                    refine ⟨9835326214448718902711333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26227536571863250407230221 9835326214448718902711333)
                    ·
                      refine ⟨1844123665209134794258375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9835326214448718902711333 1844123665209134794258375)
                      ·
                        rfl

theorem cell23_3591418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_3591418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591418 prefixEnd_3591418 := by exact prefixLift 3591418
  have htrace : WordTrace (prefixWord ++ tailWord_3591418) baseStart_3591418 baseEnd_3591418 := by
    simpa [prefixWord, tailWord_3591418, baseEnd_3591418] using wordTrace_append hprefix tailTrace_3591418
  have hstable : (prefixWord ++ tailWord_3591418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591418).length < 2 ^ (prefixWord ++ tailWord_3591418).sum := by decide
  have hdescent : baseEnd_3591418 < baseStart_3591418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591488 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_3591488 : Nat := 118140960795 + 3591488 * 2 ^ 59
def prefixEnd_3591488 : Nat := 4983230072969 + 3 ^ 40 * 3591488 * 2
def baseEnd_3591488 : Nat := 614719869618316506794351

theorem tailTrace_3591488 : CollatzResearch.WordTrace tailWord_3591488 prefixEnd_3591488 614719869618316506794351 := by
  unfold tailWord_3591488
  simp only [CollatzResearch.WordTrace]
  refine ⟨65496164406329914081023559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87328219208439885441364745 65496164406329914081023559)
  ·
    refine ⟨98244246609494871121535339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65496164406329914081023559 98244246609494871121535339)
    ·
      refine ⟨147366369914242306682303009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98244246609494871121535339 147366369914242306682303009)
      ·
        refine ⟨110524777435681730011727257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147366369914242306682303009 110524777435681730011727257)
        ·
          refine ⟨82893583076761297508795443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110524777435681730011727257 82893583076761297508795443)
          ·
            refine ⟨124340374615141946263193165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82893583076761297508795443 124340374615141946263193165)
            ·
              refine ⟨46627640480678229848697437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124340374615141946263193165 46627640480678229848697437)
              ·
                refine ⟨17485365180254336193261539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46627640480678229848697437 17485365180254336193261539)
                ·
                  refine ⟨26228047770381504289892309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17485365180254336193261539 26228047770381504289892309)
                  ·
                    refine ⟨614719869618316506794351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26228047770381504289892309 614719869618316506794351)
                    ·
                      rfl

theorem cell23_3591488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_3591488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591488 prefixEnd_3591488 := by exact prefixLift 3591488
  have htrace : WordTrace (prefixWord ++ tailWord_3591488) baseStart_3591488 baseEnd_3591488 := by
    simpa [prefixWord, tailWord_3591488, baseEnd_3591488] using wordTrace_append hprefix tailTrace_3591488
  have hstable : (prefixWord ++ tailWord_3591488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591488).length < 2 ^ (prefixWord ++ tailWord_3591488).sum := by decide
  have hdescent : baseEnd_3591488 < baseStart_3591488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591498 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3591498 : Nat := 118140960795 + 3591498 * 2 ^ 59
def prefixEnd_3591498 : Nat := 4983230072969 + 3 ^ 40 * 3591498 * 2
def baseEnd_3591498 : Nat := 1844164743661494481258007

theorem tailTrace_3591498 : CollatzResearch.WordTrace tailWord_3591498 prefixEnd_3591498 1844164743661494481258007 := by
  unfold tailWord_3591498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32748173385655899967477787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87328462361749066579940765 32748173385655899967477787)
  ·
    refine ⟨49122260078483849951216681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32748173385655899967477787 49122260078483849951216681)
    ·
      refine ⟨36841695058862887463412511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49122260078483849951216681 36841695058862887463412511)
      ·
        refine ⟨55262542588294331195118767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36841695058862887463412511 55262542588294331195118767)
        ·
          refine ⟨82893813882441496792678151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55262542588294331195118767 82893813882441496792678151)
          ·
            refine ⟨124340720823662245189017227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82893813882441496792678151 124340720823662245189017227)
            ·
              refine ⟨186511081235493367783525841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124340720823662245189017227 186511081235493367783525841)
              ·
                refine ⟨139883310926620025837644381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186511081235493367783525841 139883310926620025837644381)
                ·
                  refine ⟨52456241597482509689116643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139883310926620025837644381 52456241597482509689116643)
                  ·
                    refine ⟨78684362396223764533674965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52456241597482509689116643 78684362396223764533674965)
                    ·
                      refine ⟨1844164743661494481258007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78684362396223764533674965 1844164743661494481258007)
                      ·
                        rfl

theorem cell23_3591498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3591498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591498 prefixEnd_3591498 := by exact prefixLift 3591498
  have htrace : WordTrace (prefixWord ++ tailWord_3591498) baseStart_3591498 baseEnd_3591498 := by
    simpa [prefixWord, tailWord_3591498, baseEnd_3591498] using wordTrace_append hprefix tailTrace_3591498
  have hstable : (prefixWord ++ tailWord_3591498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591498).length < 2 ^ (prefixWord ++ tailWord_3591498).sum := by decide
  have hdescent : baseEnd_3591498 < baseStart_3591498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591505 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3591505 : Nat := 118140960795 + 3591505 * 2 ^ 59
def prefixEnd_3591505 : Nat := 4983230072969 + 3 ^ 40 * 3591505 * 2
def baseEnd_3591505 : Nat := 614722779342025317956825

theorem tailTrace_3591505 : CollatzResearch.WordTrace tailWord_3591505 prefixEnd_3591505 614722779342025317956825 := by
  unfold tailWord_3591505
  simp only [CollatzResearch.WordTrace]
  refine ⟨130992948853598240065415969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87328632569065493376943979 130992948853598240065415969)
  ·
    refine ⟨98244711640198680049061977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130992948853598240065415969 98244711640198680049061977)
    ·
      refine ⟨73683533730149010036796483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98244711640198680049061977 73683533730149010036796483)
      ·
        refine ⟨110525300595223515055194725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73683533730149010036796483 110525300595223515055194725)
        ·
          refine ⟨20723493861604409072849011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110525300595223515055194725 20723493861604409072849011)
          ·
            refine ⟨31085240792406613609273517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20723493861604409072849011 31085240792406613609273517)
            ·
              refine ⟨11656965297152480103477569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31085240792406613609273517 11656965297152480103477569)
              ·
                refine ⟨8742723972864360077608177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11656965297152480103477569 8742723972864360077608177)
                ·
                  refine ⟨6557042979648270058206133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8742723972864360077608177 6557042979648270058206133)
                  ·
                    refine ⟨614722779342025317956825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6557042979648270058206133 614722779342025317956825)
                    ·
                      rfl

theorem cell23_3591505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3591505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591505 prefixEnd_3591505 := by exact prefixLift 3591505
  have htrace : WordTrace (prefixWord ++ tailWord_3591505) baseStart_3591505 baseEnd_3591505 := by
    simpa [prefixWord, tailWord_3591505, baseEnd_3591505] using wordTrace_append hprefix tailTrace_3591505
  have hstable : (prefixWord ++ tailWord_3591505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591505).length < 2 ^ (prefixWord ++ tailWord_3591505).sum := by decide
  have hdescent : baseEnd_3591505 < baseStart_3591505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591509 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 5]
def baseStart_3591509 : Nat := 118140960795 + 3591509 * 2 ^ 59
def prefixEnd_3591509 : Nat := 4983230072969 + 3 ^ 40 * 3591509 * 2
def baseEnd_3591509 : Nat := 204907821327632659802273

theorem tailTrace_3591509 : CollatzResearch.WordTrace tailWord_3591509 prefixEnd_3591509 204907821327632659802273 := by
  unfold tailWord_3591509
  simp only [CollatzResearch.WordTrace]
  refine ⟨130993094745583748748561581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87328729830389165832374387 130993094745583748748561581)
  ·
    refine ⟨49122410529593905780710593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130993094745583748748561581 49122410529593905780710593)
    ·
      refine ⟨36841807897195429335532945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49122410529593905780710593 36841807897195429335532945)
      ·
        refine ⟨27631355922896572001649709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36841807897195429335532945 27631355922896572001649709)
        ·
          refine ⟨10361758471086214500618641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27631355922896572001649709 10361758471086214500618641)
          ·
            refine ⟨7771318853314660875463981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361758471086214500618641 7771318853314660875463981)
            ·
              refine ⟨2914244569992997828298993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7771318853314660875463981 2914244569992997828298993)
              ·
                refine ⟨2185683427494748371224245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914244569992997828298993 2185683427494748371224245)
                ·
                  refine ⟨204907821327632659802273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185683427494748371224245 204907821327632659802273)
                  ·
                    rfl

theorem cell23_3591509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_3591509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591509 prefixEnd_3591509 := by exact prefixLift 3591509
  have htrace : WordTrace (prefixWord ++ tailWord_3591509) baseStart_3591509 baseEnd_3591509 := by
    simpa [prefixWord, tailWord_3591509, baseEnd_3591509] using wordTrace_append hprefix tailTrace_3591509
  have hstable : (prefixWord ++ tailWord_3591509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591509).length < 2 ^ (prefixWord ++ tailWord_3591509).sum := by decide
  have hdescent : baseEnd_3591509 < baseStart_3591509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591525 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3591525 : Nat := 118140960795 + 3591525 * 2 ^ 59
def prefixEnd_3591525 : Nat := 4983230072969 + 3 ^ 40 * 3591525 * 2
def baseEnd_3591525 : Nat := 1844178607639165875620383

theorem tailTrace_3591525 : CollatzResearch.WordTrace tailWord_3591525 prefixEnd_3591525 1844178607639165875620383 := by
  unfold tailWord_3591525
  simp only [CollatzResearch.WordTrace]
  refine ⟨130993678313525783481144029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87329118875683855654096019 130993678313525783481144029)
  ·
    refine ⟨49122629367572168805429011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130993678313525783481144029 49122629367572168805429011)
    ·
      refine ⟨73683944051358253208143517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49122629367572168805429011 73683944051358253208143517)
      ·
        refine ⟨27631479019259344953053819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73683944051358253208143517 27631479019259344953053819)
        ·
          refine ⟨41447218528889017429580729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27631479019259344953053819 41447218528889017429580729)
          ·
            refine ⟨31085413896666763072185547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41447218528889017429580729 31085413896666763072185547)
            ·
              refine ⟨46628120845000144608278321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31085413896666763072185547 46628120845000144608278321)
              ·
                refine ⟨34971090633750108456208741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46628120845000144608278321 34971090633750108456208741)
                ·
                  refine ⟨6557079493828145335539139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34971090633750108456208741 6557079493828145335539139)
                  ·
                    refine ⟨9835619240742218003308709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557079493828145335539139 9835619240742218003308709)
                    ·
                      refine ⟨1844178607639165875620383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9835619240742218003308709 1844178607639165875620383)
                      ·
                        rfl

theorem cell23_3591525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3591525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591525 prefixEnd_3591525 := by exact prefixLift 3591525
  have htrace : WordTrace (prefixWord ++ tailWord_3591525) baseStart_3591525 baseEnd_3591525 := by
    simpa [prefixWord, tailWord_3591525, baseEnd_3591525] using wordTrace_append hprefix tailTrace_3591525
  have hstable : (prefixWord ++ tailWord_3591525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591525).length < 2 ^ (prefixWord ++ tailWord_3591525).sum := by decide
  have hdescent : baseEnd_3591525 < baseStart_3591525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591535 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 5, 4]
def baseStart_3591535 : Nat := 118140960795 + 3591535 * 2 ^ 59
def prefixEnd_3591535 : Nat := 4983230072969 + 3 ^ 40 * 3591535 * 2
def baseEnd_3591535 : Nat := 614727914148570278831779

theorem tailTrace_3591535 : CollatzResearch.WordTrace tailWord_3591535 prefixEnd_3591535 614727914148570278831779 := by
  unfold tailWord_3591535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130994043043489555189008059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87329362028993036792672039 130994043043489555189008059)
  ·
    refine ⟨196491064565234332783512089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130994043043489555189008059 196491064565234332783512089)
    ·
      refine ⟨147368298423925749587634067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196491064565234332783512089 147368298423925749587634067)
      ·
        refine ⟨221052447635888624381451101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147368298423925749587634067 221052447635888624381451101)
        ·
          refine ⟨82894667863458234143044163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221052447635888624381451101 82894667863458234143044163)
          ·
            refine ⟨124342001795187351214566245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82894667863458234143044163 124342001795187351214566245)
            ·
              refine ⟨23314125336597628352731171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124342001795187351214566245 23314125336597628352731171)
              ·
                refine ⟨34971188004896442529096757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23314125336597628352731171 34971188004896442529096757)
                ·
                  refine ⟨3278548875459041487102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34971188004896442529096757 3278548875459041487102821)
                  ·
                    refine ⟨614727914148570278831779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278548875459041487102821 614727914148570278831779)
                    ·
                      rfl

theorem cell23_3591535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_3591535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591535 prefixEnd_3591535 := by exact prefixLift 3591535
  have htrace : WordTrace (prefixWord ++ tailWord_3591535) baseStart_3591535 baseEnd_3591535 := by
    simpa [prefixWord, tailWord_3591535, baseEnd_3591535] using wordTrace_append hprefix tailTrace_3591535
  have hstable : (prefixWord ++ tailWord_3591535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591535).length < 2 ^ (prefixWord ++ tailWord_3591535).sum := by decide
  have hdescent : baseEnd_3591535 < baseStart_3591535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591545 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3591545 : Nat := 118140960795 + 3591545 * 2 ^ 59
def prefixEnd_3591545 : Nat := 4983230072969 + 3 ^ 40 * 3591545 * 2
def baseEnd_3591545 : Nat := 1844188877252255797370291

theorem tailTrace_3591545 : CollatzResearch.WordTrace tailWord_3591545 prefixEnd_3591545 1844188877252255797370291 := by
  unfold tailWord_3591545
  simp only [CollatzResearch.WordTrace]
  refine ⟨130994407773453326896872089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87329605182302217931248059 130994407773453326896872089)
  ·
    refine ⟨98245805830089995172654067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130994407773453326896872089 98245805830089995172654067)
    ·
      refine ⟨147368708745134992758981101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98245805830089995172654067 147368708745134992758981101)
      ·
        refine ⟨55263265779425622284617913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147368708745134992758981101 55263265779425622284617913)
        ·
          refine ⟨41447449334569216713463435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55263265779425622284617913 41447449334569216713463435)
          ·
            refine ⟨62171174001853825070195153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41447449334569216713463435 62171174001853825070195153)
            ·
              refine ⟨46628380501390368802646365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62171174001853825070195153 46628380501390368802646365)
              ·
                refine ⟨17485642688021388300992387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46628380501390368802646365 17485642688021388300992387)
                ·
                  refine ⟨26228464032032082451488581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17485642688021388300992387 26228464032032082451488581)
                  ·
                    refine ⟨4917837006006015459654109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26228464032032082451488581 4917837006006015459654109)
                    ·
                      refine ⟨1844188877252255797370291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917837006006015459654109 1844188877252255797370291)
                      ·
                        rfl

theorem cell23_3591545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3591545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591545 prefixEnd_3591545 := by exact prefixLift 3591545
  have htrace : WordTrace (prefixWord ++ tailWord_3591545) baseStart_3591545 baseEnd_3591545 := by
    simpa [prefixWord, tailWord_3591545, baseEnd_3591545] using wordTrace_append hprefix tailTrace_3591545
  have hstable : (prefixWord ++ tailWord_3591545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591545).length < 2 ^ (prefixWord ++ tailWord_3591545).sum := by decide
  have hdescent : baseEnd_3591545 < baseStart_3591545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591575 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3591575 : Nat := 118140960795 + 3591575 * 2 ^ 59
def prefixEnd_3591575 : Nat := 4983230072969 + 3 ^ 40 * 3591575 * 2
def baseEnd_3591575 : Nat := 1844204281671890679995153

theorem tailTrace_3591575 : CollatzResearch.WordTrace tailWord_3591575 prefixEnd_3591575 1844204281671890679995153 := by
  unfold tailWord_3591575
  simp only [CollatzResearch.WordTrace]
  refine ⟨130995501963344642020464179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87330334642229761346976119 130995501963344642020464179)
  ·
    refine ⟨196493252945016963030696269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130995501963344642020464179 196493252945016963030696269)
    ·
      refine ⟨73684969854381361136511101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196493252945016963030696269 73684969854381361136511101)
      ·
        refine ⟨27631863695393010426191663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73684969854381361136511101 27631863695393010426191663)
        ·
          refine ⟨41447795543089515639287495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27631863695393010426191663 41447795543089515639287495)
          ·
            refine ⟨62171693314634273458931243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41447795543089515639287495 62171693314634273458931243)
            ·
              refine ⟨93257539971951410188396865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62171693314634273458931243 93257539971951410188396865)
              ·
                refine ⟨69943154978963557641297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93257539971951410188396865 69943154978963557641297649)
                ·
                  refine ⟨52457366234222668230973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69943154978963557641297649 52457366234222668230973237)
                  ·
                    refine ⟨4917878084458375146653741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52457366234222668230973237 4917878084458375146653741)
                    ·
                      refine ⟨1844204281671890679995153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917878084458375146653741 1844204281671890679995153)
                      ·
                        rfl

theorem cell23_3591575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3591575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591575 prefixEnd_3591575 := by exact prefixLift 3591575
  have htrace : WordTrace (prefixWord ++ tailWord_3591575) baseStart_3591575 baseEnd_3591575 := by
    simpa [prefixWord, tailWord_3591575, baseEnd_3591575] using wordTrace_append hprefix tailTrace_3591575
  have hstable : (prefixWord ++ tailWord_3591575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591575).length < 2 ^ (prefixWord ++ tailWord_3591575).sum := by decide
  have hdescent : baseEnd_3591575 < baseStart_3591575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591626 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_3591626 : Nat := 118140960795 + 3591626 * 2 ^ 59
def prefixEnd_3591626 : Nat := 4983230072969 + 3 ^ 40 * 3591626 * 2
def baseEnd_3591626 : Nat := 1844230469185269980457419

theorem tailTrace_3591626 : CollatzResearch.WordTrace tailWord_3591626 prefixEnd_3591626 1844230469185269980457419 := by
  unfold tailWord_3591626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749340521539969432642683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87331574724106585153713821 32749340521539969432642683)
  ·
    refine ⟨49124010782309954148964025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749340521539969432642683 49124010782309954148964025)
    ·
      refine ⟨36843008086732465611723019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49124010782309954148964025 36843008086732465611723019)
      ·
        refine ⟨55264512130098698417584529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36843008086732465611723019 55264512130098698417584529)
        ·
          refine ⟨41448384097574023813188397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55264512130098698417584529 41448384097574023813188397)
          ·
            refine ⟨15543144036590258929945649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41448384097574023813188397 15543144036590258929945649)
            ·
              refine ⟨11657358027442694197459237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15543144036590258929945649 11657358027442694197459237)
              ·
                refine ⟨2185754630145505162023607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11657358027442694197459237 2185754630145505162023607)
                ·
                  refine ⟨3278631945218257743035411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185754630145505162023607 3278631945218257743035411)
                  ·
                    refine ⟨4917947917827386614553117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278631945218257743035411 4917947917827386614553117)
                    ·
                      refine ⟨1844230469185269980457419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917947917827386614553117 1844230469185269980457419)
                      ·
                        rfl

theorem cell23_3591626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_3591626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591626 prefixEnd_3591626 := by exact prefixLift 3591626
  have htrace : WordTrace (prefixWord ++ tailWord_3591626) baseStart_3591626 baseEnd_3591626 := by
    simpa [prefixWord, tailWord_3591626, baseEnd_3591626] using wordTrace_append hprefix tailTrace_3591626
  have hstable : (prefixWord ++ tailWord_3591626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591626).length < 2 ^ (prefixWord ++ tailWord_3591626).sum := by decide
  have hdescent : baseEnd_3591626 < baseStart_3591626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591642 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_3591642 : Nat := 118140960795 + 3591642 * 2 ^ 59
def prefixEnd_3591642 : Nat := 4983230072969 + 3 ^ 40 * 3591642 * 2
def baseEnd_3591642 : Nat := 614746228291913972619115

theorem tailTrace_3591642 : CollatzResearch.WordTrace tailWord_3591642 prefixEnd_3591642 614746228291913972619115 := by
  unfold tailWord_3591642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749486413525478115788295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87331963769401274975435453 32749486413525478115788295)
  ·
    refine ⟨49124229620288217173682443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749486413525478115788295 49124229620288217173682443)
    ·
      refine ⟨73686344430432325760523665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124229620288217173682443 73686344430432325760523665)
      ·
        refine ⟨55264758322824244320392749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73686344430432325760523665 55264758322824244320392749)
        ·
          refine ⟨20724284371059091620147281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55264758322824244320392749 20724284371059091620147281)
          ·
            refine ⟨15543213278294318715110461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20724284371059091620147281 15543213278294318715110461)
            ·
              refine ⟨5828704979360369518166423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15543213278294318715110461 5828704979360369518166423)
              ·
                refine ⟨8743057469040554277249635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828704979360369518166423 8743057469040554277249635)
                ·
                  refine ⟨13114586203560831415874453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743057469040554277249635 13114586203560831415874453)
                  ·
                    refine ⟨614746228291913972619115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13114586203560831415874453 614746228291913972619115)
                    ·
                      rfl

theorem cell23_3591642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_3591642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591642 prefixEnd_3591642 := by exact prefixLift 3591642
  have htrace : WordTrace (prefixWord ++ tailWord_3591642) baseStart_3591642 baseEnd_3591642 := by
    simpa [prefixWord, tailWord_3591642, baseEnd_3591642] using wordTrace_append hprefix tailTrace_3591642
  have hstable : (prefixWord ++ tailWord_3591642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591642).length < 2 ^ (prefixWord ++ tailWord_3591642).sum := by decide
  have hdescent : baseEnd_3591642 < baseStart_3591642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591649 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3591649 : Nat := 118140960795 + 3591649 * 2 ^ 59
def prefixEnd_3591649 : Nat := 4983230072969 + 3 ^ 40 * 3591649 * 2
def baseEnd_3591649 : Nat := 1844242279240323390469813

theorem tailTrace_3591649 : CollatzResearch.WordTrace tailWord_3591649 prefixEnd_3591649 1844242279240323390469813 := by
  unfold tailWord_3591649
  simp only [CollatzResearch.WordTrace]
  refine ⟨130998200965076552658658001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87332133976717701772438667 130998200965076552658658001)
  ·
    refine ⟨98248650723807414493993501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130998200965076552658658001 98248650723807414493993501)
    ·
      refine ⟨36843244021427780435247563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98248650723807414493993501 36843244021427780435247563)
      ·
        refine ⟨55264866032141670652871345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36843244021427780435247563 55264866032141670652871345)
        ·
          refine ⟨41448649524106252989653509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55264866032141670652871345 41448649524106252989653509)
          ·
            refine ⟨7771621785769922435560033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41448649524106252989653509 7771621785769922435560033)
            ·
              refine ⟨5828716339327441826670025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771621785769922435560033 5828716339327441826670025)
              ·
                refine ⟨4371537254495581370002519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828716339327441826670025 4371537254495581370002519)
                ·
                  refine ⟨6557305881743372055003779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371537254495581370002519 6557305881743372055003779)
                  ·
                    refine ⟨9835958822615058082505669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557305881743372055003779 9835958822615058082505669)
                    ·
                      refine ⟨1844242279240323390469813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9835958822615058082505669 1844242279240323390469813)
                      ·
                        rfl

theorem cell23_3591649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3591649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591649 prefixEnd_3591649 := by exact prefixLift 3591649
  have htrace : WordTrace (prefixWord ++ tailWord_3591649) baseStart_3591649 baseEnd_3591649 := by
    simpa [prefixWord, tailWord_3591649, baseEnd_3591649] using wordTrace_append hprefix tailTrace_3591649
  have hstable : (prefixWord ++ tailWord_3591649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591649).length < 2 ^ (prefixWord ++ tailWord_3591649).sum := by decide
  have hdescent : baseEnd_3591649 < baseStart_3591649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591652 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_3591652 : Nat := 118140960795 + 3591652 * 2 ^ 59
def prefixEnd_3591652 : Nat := 4983230072969 + 3 ^ 40 * 3591652 * 2
def baseEnd_3591652 : Nat := 1844243819682286878732299

theorem tailTrace_3591652 : CollatzResearch.WordTrace tailWord_3591652 prefixEnd_3591652 1844243819682286878732299 := by
  unfold tailWord_3591652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65499155192032842085508605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87332206922710456114011473 65499155192032842085508605)
  ·
    refine ⟨24562183197012315782065727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65499155192032842085508605 24562183197012315782065727)
    ·
      refine ⟨36843274795518473673098591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24562183197012315782065727 36843274795518473673098591)
      ·
        refine ⟨55264912193277710509647887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36843274795518473673098591 55264912193277710509647887)
        ·
          refine ⟨82897368289916565764471831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55264912193277710509647887 82897368289916565764471831)
          ·
            refine ⟨124346052434874848646707747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82897368289916565764471831 124346052434874848646707747)
            ·
              refine ⟨186519078652312272970061621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124346052434874848646707747 186519078652312272970061621)
              ·
                refine ⟨17486163623654275590943277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186519078652312272970061621 17486163623654275590943277)
                ·
                  refine ⟨6557311358870353346603729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17486163623654275590943277 6557311358870353346603729)
                  ·
                    refine ⟨4917983519152765009952797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6557311358870353346603729 4917983519152765009952797)
                    ·
                      refine ⟨1844243819682286878732299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4917983519152765009952797 1844243819682286878732299)
                      ·
                        rfl

theorem cell23_3591652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_3591652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591652 prefixEnd_3591652 := by exact prefixLift 3591652
  have htrace : WordTrace (prefixWord ++ tailWord_3591652) baseStart_3591652 baseEnd_3591652 := by
    simpa [prefixWord, tailWord_3591652, baseEnd_3591652] using wordTrace_append hprefix tailTrace_3591652
  have hstable : (prefixWord ++ tailWord_3591652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591652).length < 2 ^ (prefixWord ++ tailWord_3591652).sum := by decide
  have hdescent : baseEnd_3591652 < baseStart_3591652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591662 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3591662 : Nat := 118140960795 + 3591662 * 2 ^ 59
def prefixEnd_3591662 : Nat := 4983230072969 + 3 ^ 40 * 3591662 * 2
def baseEnd_3591662 : Nat := 1844248954488831839607253

theorem tailTrace_3591662 : CollatzResearch.WordTrace tailWord_3591662 prefixEnd_3591662 1844248954488831839607253 := by
  unfold tailWord_3591662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16374834389253681984860155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87332450076019637252587493 16374834389253681984860155)
  ·
    refine ⟨24562251583880522977290233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16374834389253681984860155 24562251583880522977290233)
    ·
      refine ⟨18421688687910392232967675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24562251583880522977290233 18421688687910392232967675)
      ·
        refine ⟨27632533031865588349451513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18421688687910392232967675 27632533031865588349451513)
        ·
          refine ⟨20724399773899191262088635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27632533031865588349451513 20724399773899191262088635)
          ·
            refine ⟨31086599660848786893132953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724399773899191262088635 31086599660848786893132953)
            ·
              refine ⟨23314949745636590169849715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31086599660848786893132953 23314949745636590169849715)
              ·
                refine ⟨34972424618454885254774573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23314949745636590169849715 34972424618454885254774573)
                ·
                  refine ⟨13114659231920581970540465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34972424618454885254774573 13114659231920581970540465)
                  ·
                    refine ⟨9835994423940436477905349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13114659231920581970540465 9835994423940436477905349)
                    ·
                      refine ⟨1844248954488831839607253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9835994423940436477905349 1844248954488831839607253)
                      ·
                        rfl

theorem cell23_3591662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3591662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591662 prefixEnd_3591662 := by exact prefixLift 3591662
  have htrace : WordTrace (prefixWord ++ tailWord_3591662) baseStart_3591662 baseEnd_3591662 := by
    simpa [prefixWord, tailWord_3591662, baseEnd_3591662] using wordTrace_append hprefix tailTrace_3591662
  have hstable : (prefixWord ++ tailWord_3591662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591662).length < 2 ^ (prefixWord ++ tailWord_3591662).sum := by decide
  have hdescent : baseEnd_3591662 < baseStart_3591662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591669 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3591669 : Nat := 118140960795 + 3591669 * 2 ^ 59
def prefixEnd_3591669 : Nat := 4983230072969 + 3 ^ 40 * 3591669 * 2
def baseEnd_3591669 : Nat := 1844252548853413312219721

theorem tailTrace_3591669 : CollatzResearch.WordTrace tailWord_3591669 prefixEnd_3591669 1844252548853413312219721 := by
  unfold tailWord_3591669
  simp only [CollatzResearch.WordTrace]
  refine ⟨130998930425004096074386061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87332620283336064049590707 130998930425004096074386061)
  ·
    refine ⟨49124598909376536027894773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130998930425004096074386061 49124598909376536027894773)
    ·
      refine ⟨4605431147754050252615135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49124598909376536027894773 4605431147754050252615135)
      ·
        refine ⟨6908146721631075378922703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605431147754050252615135 6908146721631075378922703)
        ·
          refine ⟨10362220082446613068384055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908146721631075378922703 10362220082446613068384055)
          ·
            refine ⟨15543330123669919602576083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362220082446613068384055 15543330123669919602576083)
            ·
              refine ⟨23314995185504879403864125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543330123669919602576083 23314995185504879403864125)
              ·
                refine ⟨8743123194564329776449047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23314995185504879403864125 8743123194564329776449047)
                ·
                  refine ⟨13114684791846494664673571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743123194564329776449047 13114684791846494664673571)
                  ·
                    refine ⟨19672027187769741997010357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13114684791846494664673571 19672027187769741997010357)
                    ·
                      refine ⟨1844252548853413312219721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19672027187769741997010357 1844252548853413312219721)
                      ·
                        rfl

theorem cell23_3591669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3591669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591669 prefixEnd_3591669 := by exact prefixLift 3591669
  have htrace : WordTrace (prefixWord ++ tailWord_3591669) baseStart_3591669 baseEnd_3591669 := by
    simpa [prefixWord, tailWord_3591669, baseEnd_3591669] using wordTrace_append hprefix tailTrace_3591669
  have hstable : (prefixWord ++ tailWord_3591669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591669).length < 2 ^ (prefixWord ++ tailWord_3591669).sum := by decide
  have hdescent : baseEnd_3591669 < baseStart_3591669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591685 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3591685 : Nat := 118140960795 + 3591685 * 2 ^ 59
def prefixEnd_3591685 : Nat := 4983230072969 + 3 ^ 40 * 3591685 * 2
def baseEnd_3591685 : Nat := 614753588181295083206549

theorem tailTrace_3591685 : CollatzResearch.WordTrace tailWord_3591685 prefixEnd_3591685 614753588181295083206549 := by
  unfold tailWord_3591685
  simp only [CollatzResearch.WordTrace]
  refine ⟨130999513992946130806968509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87333009328630753871312339 130999513992946130806968509)
  ·
    refine ⟨49124817747354799052613191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130999513992946130806968509 49124817747354799052613191)
    ·
      refine ⟨73687226621032198578919787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124817747354799052613191 73687226621032198578919787)
      ·
        refine ⟨110530839931548297868379681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73687226621032198578919787 110530839931548297868379681)
        ·
          refine ⟨82898129948661223401284761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110530839931548297868379681 82898129948661223401284761)
          ·
            refine ⟨62173597461495917550963571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82898129948661223401284761 62173597461495917550963571)
            ·
              refine ⟨93260396192243876326445357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62173597461495917550963571 93260396192243876326445357)
              ·
                refine ⟨34972648572091453622417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93260396192243876326445357 34972648572091453622417009)
                ·
                  refine ⟨26229486429068590216812757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34972648572091453622417009 26229486429068590216812757)
                  ·
                    refine ⟨614753588181295083206549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26229486429068590216812757 614753588181295083206549)
                    ·
                      rfl

theorem cell23_3591685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3591685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591685 prefixEnd_3591685 := by exact prefixLift 3591685
  have htrace : WordTrace (prefixWord ++ tailWord_3591685) baseStart_3591685 baseEnd_3591685 := by
    simpa [prefixWord, tailWord_3591685, baseEnd_3591685] using wordTrace_append hprefix tailTrace_3591685
  have hstable : (prefixWord ++ tailWord_3591685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591685).length < 2 ^ (prefixWord ++ tailWord_3591685).sum := by decide
  have hdescent : baseEnd_3591685 < baseStart_3591685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591700 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3591700 : Nat := 118140960795 + 3591700 * 2 ^ 59
def prefixEnd_3591700 : Nat := 4983230072969 + 3 ^ 40 * 3591700 * 2
def baseEnd_3591700 : Nat := 1844268466753702690932079

theorem tailTrace_3591700 : CollatzResearch.WordTrace tailWord_3591700 prefixEnd_3591700 1844268466753702690932079 := by
  unfold tailWord_3591700
  simp only [CollatzResearch.WordTrace]
  refine ⟨65500030543945894184382277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87333374058594525579176369 65500030543945894184382277)
  ·
    refine ⟨12281255726989855159571677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65500030543945894184382277 12281255726989855159571677)
    ·
      refine ⟨4605470897621195684839379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12281255726989855159571677 4605470897621195684839379)
      ·
        refine ⟨6908206346431793527259069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605470897621195684839379 6908206346431793527259069)
        ·
          refine ⟨2590577379911922572722151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6908206346431793527259069 2590577379911922572722151)
          ·
            refine ⟨3885866069867883859083227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590577379911922572722151 3885866069867883859083227)
            ·
              refine ⟨5828799104801825788624841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885866069867883859083227 5828799104801825788624841)
              ·
                refine ⟨4371599328601369341468631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828799104801825788624841 4371599328601369341468631)
                ·
                  refine ⟨6557398992902054012202947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371599328601369341468631 6557398992902054012202947)
                  ·
                    refine ⟨9836098489353081018304421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557398992902054012202947 9836098489353081018304421)
                    ·
                      refine ⟨1844268466753702690932079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9836098489353081018304421 1844268466753702690932079)
                      ·
                        rfl

theorem cell23_3591700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3591700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591700 prefixEnd_3591700 := by exact prefixLift 3591700
  have htrace : WordTrace (prefixWord ++ tailWord_3591700) baseStart_3591700 baseEnd_3591700 := by
    simpa [prefixWord, tailWord_3591700, baseEnd_3591700] using wordTrace_append hprefix tailTrace_3591700
  have hstable : (prefixWord ++ tailWord_3591700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591700).length < 2 ^ (prefixWord ++ tailWord_3591700).sum := by decide
  have hdescent : baseEnd_3591700 < baseStart_3591700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591734 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3591734 : Nat := 118140960795 + 3591734 * 2 ^ 59
def prefixEnd_3591734 : Nat := 4983230072969 + 3 ^ 40 * 3591734 * 2
def baseEnd_3591734 : Nat := 1844285925095955557906923

theorem tailTrace_3591734 : CollatzResearch.WordTrace tailWord_3591734 prefixEnd_3591734 1844285925095955557906923 := by
  unfold tailWord_3591734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187581323110538260968891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87334200779845741450334837 8187581323110538260968891)
  ·
    refine ⟨12281371984665807391453337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8187581323110538260968891 12281371984665807391453337)
    ·
      refine ⟨9211028988499355543590003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12281371984665807391453337 9211028988499355543590003)
      ·
        refine ⟨13816543482749033315385005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211028988499355543590003 13816543482749033315385005)
        ·
          refine ⟨5181203806030887493269377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13816543482749033315385005 5181203806030887493269377)
          ·
            refine ⟨3885902854523165619952033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181203806030887493269377 3885902854523165619952033)
            ·
              refine ⟨2914427140892374214964025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885902854523165619952033 2914427140892374214964025)
              ·
                refine ⟨2185820355669280661223019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914427140892374214964025 2185820355669280661223019)
                ·
                  refine ⟨3278730533503920991834529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185820355669280661223019 3278730533503920991834529)
                  ·
                    refine ⟨2459047900127940743875897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3278730533503920991834529 2459047900127940743875897)
                    ·
                      refine ⟨1844285925095955557906923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459047900127940743875897 1844285925095955557906923)
                      ·
                        rfl

theorem cell23_3591734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3591734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591734 prefixEnd_3591734 := by exact prefixLift 3591734
  have htrace : WordTrace (prefixWord ++ tailWord_3591734) baseStart_3591734 baseEnd_3591734 := by
    simpa [prefixWord, tailWord_3591734, baseEnd_3591734] using wordTrace_append hprefix tailTrace_3591734
  have hstable : (prefixWord ++ tailWord_3591734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591734).length < 2 ^ (prefixWord ++ tailWord_3591734).sum := by decide
  have hdescent : baseEnd_3591734 < baseStart_3591734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591756 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3591756 : Nat := 118140960795 + 3591756 * 2 ^ 59
def prefixEnd_3591756 : Nat := 4983230072969 + 3 ^ 40 * 3591756 * 2
def baseEnd_3591756 : Nat := 1844297221670354471831821

theorem tailTrace_3591756 : CollatzResearch.WordTrace tailWord_3591756 prefixEnd_3591756 1844297221670354471831821 := by
  unfold tailWord_3591756
  simp only [CollatzResearch.WordTrace]
  refine ⟨65501051787844454966401561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87334735717125939955202081 65501051787844454966401561)
  ·
    refine ⟨49125788840883341224801171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65501051787844454966401561 49125788840883341224801171)
    ·
      refine ⟨73688683261325011837201757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49125788840883341224801171 73688683261325011837201757)
      ·
        refine ⟨27633256222996879438950659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73688683261325011837201757 27633256222996879438950659)
        ·
          refine ⟨41449884334495319158425989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27633256222996879438950659 41449884334495319158425989)
          ·
            refine ⟨7771853312717872342204873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41449884334495319158425989 7771853312717872342204873)
            ·
              refine ⟨5828889984538404256653655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771853312717872342204873 5828889984538404256653655)
              ·
                refine ⟨8743334976807606384980483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828889984538404256653655 8743334976807606384980483)
                ·
                  refine ⟨13115002465211409577470725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743334976807606384980483 13115002465211409577470725)
                  ·
                    refine ⟨2459062962227139295775761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13115002465211409577470725 2459062962227139295775761)
                    ·
                      refine ⟨1844297221670354471831821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459062962227139295775761 1844297221670354471831821)
                      ·
                        rfl

theorem cell23_3591756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3591756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591756 prefixEnd_3591756 := by exact prefixLift 3591756
  have htrace : WordTrace (prefixWord ++ tailWord_3591756) baseStart_3591756 baseEnd_3591756 := by
    simpa [prefixWord, tailWord_3591756, baseEnd_3591756] using wordTrace_append hprefix tailTrace_3591756
  have hstable : (prefixWord ++ tailWord_3591756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591756).length < 2 ^ (prefixWord ++ tailWord_3591756).sum := by decide
  have hdescent : baseEnd_3591756 < baseStart_3591756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591762 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_3591762 : Nat := 118140960795 + 3591762 * 2 ^ 59
def prefixEnd_3591762 : Nat := 4983230072969 + 3 ^ 40 * 3591762 * 2
def baseEnd_3591762 : Nat := 204922255839364605372977

theorem tailTrace_3591762 : CollatzResearch.WordTrace tailWord_3591762 prefixEnd_3591762 204922255839364605372977 := by
  unfold tailWord_3591762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750580603416793239380385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87334881609111448638347693 32750580603416793239380385)
  ·
    refine ⟨24562935452562594929535289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32750580603416793239380385 24562935452562594929535289)
    ·
      refine ⟨18422201589421946197151467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24562935452562594929535289 18422201589421946197151467)
      ·
        refine ⟨27633302384132919295727201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18422201589421946197151467 27633302384132919295727201)
        ·
          refine ⟨20724976788099689471795401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27633302384132919295727201 20724976788099689471795401)
          ·
            refine ⟨15543732591074767103846551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20724976788099689471795401 15543732591074767103846551)
            ·
              refine ⟨23315598886612150655769827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543732591074767103846551 23315598886612150655769827)
              ·
                refine ⟨34973398329918225983654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23315598886612150655769827 34973398329918225983654741)
                ·
                  refine ⟨204922255839364605372977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34973398329918225983654741 204922255839364605372977)
                  ·
                    rfl

theorem cell23_3591762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_3591762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591762 prefixEnd_3591762 := by exact prefixLift 3591762
  have htrace : WordTrace (prefixWord ++ tailWord_3591762) baseStart_3591762 baseEnd_3591762 := by
    simpa [prefixWord, tailWord_3591762, baseEnd_3591762] using wordTrace_append hprefix tailTrace_3591762
  have hstable : (prefixWord ++ tailWord_3591762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591762).length < 2 ^ (prefixWord ++ tailWord_3591762).sum := by decide
  have hdescent : baseEnd_3591762 < baseStart_3591762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591779 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 5]
def baseStart_3591779 : Nat := 118140960795 + 3591779 * 2 ^ 59
def prefixEnd_3591779 : Nat := 4983230072969 + 3 ^ 40 * 3591779 * 2
def baseEnd_3591779 : Nat := 204923225747267542427135

theorem tailTrace_3591779 : CollatzResearch.WordTrace tailWord_3591779 prefixEnd_3591779 204923225747267542427135 := by
  unfold tailWord_3591779
  simp only [CollatzResearch.WordTrace]
  refine ⟨131002942454605584860890391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87335294969737056573926927 131002942454605584860890391)
  ·
    refine ⟨196504413681908377291335587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131002942454605584860890391 196504413681908377291335587)
    ·
      refine ⟨294756620522862565937003381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196504413681908377291335587 294756620522862565937003381)
      ·
        refine ⟨27633433174018365556594067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294756620522862565937003381 27633433174018365556594067)
        ·
          refine ⟨41450149761027548334891101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27633433174018365556594067 41450149761027548334891101)
          ·
            refine ⟨15543806160385330625584163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41450149761027548334891101 15543806160385330625584163)
            ·
              refine ⟨23315709240577995938376245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543806160385330625584163 23315709240577995938376245)
              ·
                refine ⟨2185847741304187119222773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23315709240577995938376245 2185847741304187119222773)
                ·
                  refine ⟨204923225747267542427135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185847741304187119222773 204923225747267542427135)
                  ·
                    rfl

theorem cell23_3591779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 5].length) (baseStart_3591779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591779 prefixEnd_3591779 := by exact prefixLift 3591779
  have htrace : WordTrace (prefixWord ++ tailWord_3591779) baseStart_3591779 baseEnd_3591779 := by
    simpa [prefixWord, tailWord_3591779, baseEnd_3591779] using wordTrace_append hprefix tailTrace_3591779
  have hstable : (prefixWord ++ tailWord_3591779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591779).length < 2 ^ (prefixWord ++ tailWord_3591779).sum := by decide
  have hdescent : baseEnd_3591779 < baseStart_3591779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591829 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_3591829 : Nat := 118140960795 + 3591829 * 2 ^ 59
def prefixEnd_3591829 : Nat := 4983230072969 + 3 ^ 40 * 3591829 * 2
def baseEnd_3591829 : Nat := 1844334705758132686218985

theorem tailTrace_3591829 : CollatzResearch.WordTrace tailWord_3591829 prefixEnd_3591829 1844334705758132686218985 := by
  unfold tailWord_3591829
  simp only [CollatzResearch.WordTrace]
  refine ⟨131004766104424443400210541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87336510736282962266807027 131004766104424443400210541)
  ·
    refine ⟨49126787289159166275078953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131004766104424443400210541 49126787289159166275078953)
    ·
      refine ⟨36845090466869374706309215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49126787289159166275078953 36845090466869374706309215)
      ·
        refine ⟨55267635700304062059463823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36845090466869374706309215 55267635700304062059463823)
        ·
          refine ⟨82901453550456093089195735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55267635700304062059463823 82901453550456093089195735)
          ·
            refine ⟨124352180325684139633793603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82901453550456093089195735 124352180325684139633793603)
            ·
              refine ⟨186528270488526209450690405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124352180325684139633793603 186528270488526209450690405)
              ·
                refine ⟨34974050716598664272004451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186528270488526209450690405 34974050716598664272004451)
                ·
                  refine ⟨52461076074897996408006677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34974050716598664272004451 52461076074897996408006677)
                  ·
                    refine ⟨2459112941010843581625313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52461076074897996408006677 2459112941010843581625313)
                    ·
                      refine ⟨1844334705758132686218985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459112941010843581625313 1844334705758132686218985)
                      ·
                        rfl

theorem cell23_3591829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_3591829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591829 prefixEnd_3591829 := by exact prefixLift 3591829
  have htrace : WordTrace (prefixWord ++ tailWord_3591829) baseStart_3591829 baseEnd_3591829 := by
    simpa [prefixWord, tailWord_3591829, baseEnd_3591829] using wordTrace_append hprefix tailTrace_3591829
  have hstable : (prefixWord ++ tailWord_3591829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591829).length < 2 ^ (prefixWord ++ tailWord_3591829).sum := by decide
  have hdescent : baseEnd_3591829 < baseStart_3591829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591856 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 1, 4]
def baseStart_3591856 : Nat := 118140960795 + 3591856 * 2 ^ 59
def prefixEnd_3591856 : Nat := 4983230072969 + 3 ^ 40 * 3591856 * 2
def baseEnd_3591856 : Nat := 614782856578601360193787

theorem tailTrace_3591856 : CollatzResearch.WordTrace tailWord_3591856 prefixEnd_3591856 614782856578601360193787 := by
  unfold tailWord_3591856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65502875437663313505721711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87337167250217751340962281 65502875437663313505721711)
  ·
    refine ⟨98254313156494970258582567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65502875437663313505721711 98254313156494970258582567)
    ·
      refine ⟨147381469734742455387873851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98254313156494970258582567 147381469734742455387873851)
      ·
        refine ⟨221072204602113683081810777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147381469734742455387873851 221072204602113683081810777)
        ·
          refine ⟨165804153451585262311358083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221072204602113683081810777 165804153451585262311358083)
          ·
            refine ⟨248706230177377893467037125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165804153451585262311358083 248706230177377893467037125)
            ·
              refine ⟨46632418158258355025069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248706230177377893467037125 46632418158258355025069461)
              ·
                refine ⟨2185894601168360391800131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46632418158258355025069461 2185894601168360391800131)
                ·
                  refine ⟨3278841901752540587700197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185894601168360391800131 3278841901752540587700197)
                  ·
                    refine ⟨614782856578601360193787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278841901752540587700197 614782856578601360193787)
                    ·
                      rfl

theorem cell23_3591856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_3591856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591856 prefixEnd_3591856 := by exact prefixLift 3591856
  have htrace : WordTrace (prefixWord ++ tailWord_3591856) baseStart_3591856 baseEnd_3591856 := by
    simpa [prefixWord, tailWord_3591856, baseEnd_3591856] using wordTrace_append hprefix tailTrace_3591856
  have hstable : (prefixWord ++ tailWord_3591856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591856).length < 2 ^ (prefixWord ++ tailWord_3591856).sum := by decide
  have hdescent : baseEnd_3591856 < baseStart_3591856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591869 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 6]
def baseStart_3591869 : Nat := 118140960795 + 3591869 * 2 ^ 59
def prefixEnd_3591869 : Nat := 4983230072969 + 3 ^ 40 * 3591869 * 2
def baseEnd_3591869 : Nat := 204928360553812503302089

theorem tailTrace_3591869 : CollatzResearch.WordTrace tailWord_3591869 prefixEnd_3591869 204928360553812503302089 := by
  unfold tailWord_3591869
  simp only [CollatzResearch.WordTrace]
  refine ⟨131006225024279530231666661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87337483349519686821111107 131006225024279530231666661)
  ·
    refine ⟨24563667192052411918437499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131006225024279530231666661 24563667192052411918437499)
    ·
      refine ⟨36845500788078617877656249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24563667192052411918437499 36845500788078617877656249)
      ·
        refine ⟨27634125591058963408242187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36845500788078617877656249 27634125591058963408242187)
        ·
          refine ⟨41451188386588445112363281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27634125591058963408242187 41451188386588445112363281)
          ·
            refine ⟨31088391289941333834272461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41451188386588445112363281 31088391289941333834272461)
            ·
              refine ⟨11658146733728000187852173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31088391289941333834272461 11658146733728000187852173)
              ·
                refine ⟨4371805025148000070444565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11658146733728000187852173 4371805025148000070444565)
                ·
                  refine ⟨204928360553812503302089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4371805025148000070444565 204928360553812503302089)
                  ·
                    rfl

theorem cell23_3591869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_3591869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591869 prefixEnd_3591869 := by exact prefixLift 3591869
  have htrace : WordTrace (prefixWord ++ tailWord_3591869) baseStart_3591869 baseEnd_3591869 := by
    simpa [prefixWord, tailWord_3591869, baseEnd_3591869] using wordTrace_append hprefix tailTrace_3591869
  have hstable : (prefixWord ++ tailWord_3591869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591869).length < 2 ^ (prefixWord ++ tailWord_3591869).sum := by decide
  have hdescent : baseEnd_3591869 < baseStart_3591869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591907 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 1, 4]
def baseStart_3591907 : Nat := 118140960795 + 3591907 * 2 ^ 59
def prefixEnd_3591907 : Nat := 4983230072969 + 3 ^ 40 * 3591907 * 2
def baseEnd_3591907 : Nat := 614791585749727793681209

theorem tailTrace_3591907 : CollatzResearch.WordTrace tailWord_3591907 prefixEnd_3591907 614791585749727793681209 := by
  unfold tailWord_3591907
  simp only [CollatzResearch.WordTrace]
  refine ⟨131007610998141862721549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87338407332094575147699983 131007610998141862721549975)
  ·
    refine ⟨196511416497212794082324963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131007610998141862721549975 196511416497212794082324963)
    ·
      refine ⟨294767124745819191123487445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196511416497212794082324963 294767124745819191123487445)
      ·
        refine ⟨6908604486230137291956737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 294767124745819191123487445 6908604486230137291956737)
        ·
          refine ⟨5181453364672602968967553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6908604486230137291956737 5181453364672602968967553)
          ·
            refine ⟨3886090023504452226725665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181453364672602968967553 3886090023504452226725665)
            ·
              refine ⟨2914567517628339170044249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886090023504452226725665 2914567517628339170044249)
              ·
                refine ⟨2185925638221254377533187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914567517628339170044249 2185925638221254377533187)
                ·
                  refine ⟨3278888457331881566299781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185925638221254377533187 3278888457331881566299781)
                  ·
                    refine ⟨614791585749727793681209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278888457331881566299781 614791585749727793681209)
                    ·
                      rfl

theorem cell23_3591907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 4].length) (baseStart_3591907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591907 prefixEnd_3591907 := by exact prefixLift 3591907
  have htrace : WordTrace (prefixWord ++ tailWord_3591907) baseStart_3591907 baseEnd_3591907 := by
    simpa [prefixWord, tailWord_3591907, baseEnd_3591907] using wordTrace_append hprefix tailTrace_3591907
  have hstable : (prefixWord ++ tailWord_3591907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591907).length < 2 ^ (prefixWord ++ tailWord_3591907).sum := by decide
  have hdescent : baseEnd_3591907 < baseStart_3591907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591919 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_3591919 : Nat := 118140960795 + 3591919 * 2 ^ 59
def prefixEnd_3591919 : Nat := 4983230072969 + 3 ^ 40 * 3591919 * 2
def baseEnd_3591919 : Nat := 1844380919017037334093571

theorem tailTrace_3591919 : CollatzResearch.WordTrace tailWord_3591919 prefixEnd_3591919 1844380919017037334093571 := by
  unfold tailWord_3591919
  simp only [CollatzResearch.WordTrace]
  refine ⟨131008048674098388770986811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87338699116065592513991207 131008048674098388770986811)
  ·
    refine ⟨196512073011147583156480217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131008048674098388770986811 196512073011147583156480217)
    ·
      refine ⟨147384054758360687367360163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196512073011147583156480217 147384054758360687367360163)
      ·
        refine ⟨221076082137541031051040245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147384054758360687367360163 221076082137541031051040245)
        ·
          refine ⟨20725882700394471661035023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221076082137541031051040245 20725882700394471661035023)
          ·
            refine ⟨31088824050591707491552535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20725882700394471661035023 31088824050591707491552535)
            ·
              refine ⟨46633236075887561237328803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31088824050591707491552535 46633236075887561237328803)
              ·
                refine ⟨69949854113831341855993205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46633236075887561237328803 69949854113831341855993205)
                ·
                  refine ⟨6557798823171688298999363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69949854113831341855993205 6557798823171688298999363)
                  ·
                    refine ⟨9836698234757532448499045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557798823171688298999363 9836698234757532448499045)
                    ·
                      refine ⟨1844380919017037334093571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9836698234757532448499045 1844380919017037334093571)
                      ·
                        rfl

theorem cell23_3591919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_3591919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591919 prefixEnd_3591919 := by exact prefixLift 3591919
  have htrace : WordTrace (prefixWord ++ tailWord_3591919) baseStart_3591919 baseEnd_3591919 := by
    simpa [prefixWord, tailWord_3591919, baseEnd_3591919] using wordTrace_append hprefix tailTrace_3591919
  have hstable : (prefixWord ++ tailWord_3591919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591919).length < 2 ^ (prefixWord ++ tailWord_3591919).sum := by decide
  have hdescent : baseEnd_3591919 < baseStart_3591919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591929 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_3591929 : Nat := 118140960795 + 3591929 * 2 ^ 59
def prefixEnd_3591929 : Nat := 4983230072969 + 3 ^ 40 * 3591929 * 2
def baseEnd_3591929 : Nat := 614795351274527431656175

theorem tailTrace_3591929 : CollatzResearch.WordTrace tailWord_3591929 prefixEnd_3591929 614795351274527431656175 := by
  unfold tailWord_3591929
  simp only [CollatzResearch.WordTrace]
  refine ⟨131008413404062160478850841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87338942269374773652567227 131008413404062160478850841)
  ·
    refine ⟨98256310053046620359138131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131008413404062160478850841 98256310053046620359138131)
    ·
      refine ⟨147384465079569930538707197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98256310053046620359138131 147384465079569930538707197)
      ·
        refine ⟨55269174404838723952015199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147384465079569930538707197 55269174404838723952015199)
        ·
          refine ⟨82903761607258085928022799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55269174404838723952015199 82903761607258085928022799)
          ·
            refine ⟨124355642410887128892034199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82903761607258085928022799 124355642410887128892034199)
            ·
              refine ⟨186533463616330693338051299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124355642410887128892034199 186533463616330693338051299)
              ·
                refine ⟨279800195424496040007076949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186533463616330693338051299 279800195424496040007076949)
                ·
                  refine ⟨3278908540130812968832933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 279800195424496040007076949 3278908540130812968832933)
                  ·
                    refine ⟨614795351274527431656175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3278908540130812968832933 614795351274527431656175)
                    ·
                      rfl

theorem cell23_3591929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_3591929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591929 prefixEnd_3591929 := by exact prefixLift 3591929
  have htrace : WordTrace (prefixWord ++ tailWord_3591929) baseStart_3591929 baseEnd_3591929 := by
    simpa [prefixWord, tailWord_3591929, baseEnd_3591929] using wordTrace_append hprefix tailTrace_3591929
  have hstable : (prefixWord ++ tailWord_3591929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591929).length < 2 ^ (prefixWord ++ tailWord_3591929).sum := by decide
  have hdescent : baseEnd_3591929 < baseStart_3591929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591940 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3591940 : Nat := 118140960795 + 3591940 * 2 ^ 59
def prefixEnd_3591940 : Nat := 4983230072969 + 3 ^ 40 * 3591940 * 2
def baseEnd_3591940 : Nat := 1844391702110781751930975

theorem tailTrace_3591940 : CollatzResearch.WordTrace tailWord_3591940 prefixEnd_3591940 1844391702110781751930975 := by
  unfold tailWord_3591940
  simp only [CollatzResearch.WordTrace]
  refine ⟨65504407303511154678750637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87339209738014872905000849 65504407303511154678750637)
  ·
    refine ⟨24564152738816683004531489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65504407303511154678750637 24564152738816683004531489)
    ·
      refine ⟨18423114554112512253398617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24564152738816683004531489 18423114554112512253398617)
      ·
        refine ⟨13817335915584384190048963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423114554112512253398617 13817335915584384190048963)
        ·
          refine ⟨20726003873376576285073445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817335915584384190048963 20726003873376576285073445)
          ·
            refine ⟨3886125726258108053451271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20726003873376576285073445 3886125726258108053451271)
            ·
              refine ⟨5829188589387162080176907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886125726258108053451271 5829188589387162080176907)
              ·
                refine ⟨8743782884080743120265361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829188589387162080176907 8743782884080743120265361)
                ·
                  refine ⟨6557837163060557340199021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8743782884080743120265361 6557837163060557340199021)
                  ·
                    refine ⟨2459188936147709002574633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6557837163060557340199021 2459188936147709002574633)
                    ·
                      refine ⟨1844391702110781751930975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459188936147709002574633 1844391702110781751930975)
                      ·
                        rfl

theorem cell23_3591940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3591940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591940 prefixEnd_3591940 := by exact prefixLift 3591940
  have htrace : WordTrace (prefixWord ++ tailWord_3591940) baseStart_3591940 baseEnd_3591940 := by
    simpa [prefixWord, tailWord_3591940, baseEnd_3591940] using wordTrace_append hprefix tailTrace_3591940
  have hstable : (prefixWord ++ tailWord_3591940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591940).length < 2 ^ (prefixWord ++ tailWord_3591940).sum := by decide
  have hdescent : baseEnd_3591940 < baseStart_3591940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591959 : List Nat := [1, 1, 3, 4, 2, 2, 10]
def baseStart_3591959 : Nat := 118140960795 + 3591959 * 2 ^ 59
def prefixEnd_3591959 : Nat := 4983230072969 + 3 ^ 40 * 3591959 * 2
def baseEnd_3591959 : Nat := 22770388373373051575227

theorem tailTrace_3591959 : CollatzResearch.WordTrace tailWord_3591959 prefixEnd_3591959 22770388373373051575227 := by
  unfold tailWord_3591959
  simp only [CollatzResearch.WordTrace]
  refine ⟨131009507593953475602442931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87339671729302317068295287 131009507593953475602442931)
  ·
    refine ⟨196514261390930213403664397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131009507593953475602442931 196514261390930213403664397)
    ·
      refine ⟨73692848021598830026374149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196514261390930213403664397 73692848021598830026374149)
      ·
        refine ⟨13817409004049780629945153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73692848021598830026374149 13817409004049780629945153)
        ·
          refine ⟨10363056753037335472458865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13817409004049780629945153 10363056753037335472458865)
          ·
            refine ⟨7772292564778001604344149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10363056753037335472458865 7772292564778001604344149)
            ·
              refine ⟨22770388373373051575227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7772292564778001604344149 22770388373373051575227)
              ·
                rfl

theorem cell23_3591959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 10].length) (baseStart_3591959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591959 prefixEnd_3591959 := by exact prefixLift 3591959
  have htrace : WordTrace (prefixWord ++ tailWord_3591959) baseStart_3591959 baseEnd_3591959 := by
    simpa [prefixWord, tailWord_3591959, baseEnd_3591959] using wordTrace_append hprefix tailTrace_3591959
  have hstable : (prefixWord ++ tailWord_3591959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591959).length < 2 ^ (prefixWord ++ tailWord_3591959).sum := by decide
  have hdescent : baseEnd_3591959 < baseStart_3591959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591970 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_3591970 : Nat := 118140960795 + 3591970 * 2 ^ 59
def prefixEnd_3591970 : Nat := 4983230072969 + 3 ^ 40 * 3591970 * 2
def baseEnd_3591970 : Nat := 1844407106530416634555837

theorem tailTrace_3591970 : CollatzResearch.WordTrace tailWord_3591970 prefixEnd_3591970 1844407106530416634555837 := by
  unfold tailWord_3591970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752477199228406120273341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87339939197942416320728909 32752477199228406120273341)
  ·
    refine ⟨12282178949710652295102503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32752477199228406120273341 12282178949710652295102503)
    ·
      refine ⟨18423268424565978442653755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12282178949710652295102503 18423268424565978442653755)
      ·
        refine ⟨27634902636848967663980633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18423268424565978442653755 27634902636848967663980633)
        ·
          refine ⟨20726176977636725747985475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27634902636848967663980633 20726176977636725747985475)
          ·
            refine ⟨31089265466455088621978213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726176977636725747985475 31089265466455088621978213)
            ·
              refine ⟨5829237274960329116620915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31089265466455088621978213 5829237274960329116620915)
              ·
                refine ⟨8743855912440493674931373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829237274960329116620915 8743855912440493674931373)
                ·
                  refine ⟨3278945967165185128099265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8743855912440493674931373 3278945967165185128099265)
                  ·
                    refine ⟨2459209475373888846074449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3278945967165185128099265 2459209475373888846074449)
                    ·
                      refine ⟨1844407106530416634555837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459209475373888846074449 1844407106530416634555837)
                      ·
                        rfl

theorem cell23_3591970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_3591970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591970 prefixEnd_3591970 := by exact prefixLift 3591970
  have htrace : WordTrace (prefixWord ++ tailWord_3591970) baseStart_3591970 baseEnd_3591970 := by
    simpa [prefixWord, tailWord_3591970, baseEnd_3591970] using wordTrace_append hprefix tailTrace_3591970
  have hstable : (prefixWord ++ tailWord_3591970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591970).length < 2 ^ (prefixWord ++ tailWord_3591970).sum := by decide
  have hdescent : baseEnd_3591970 < baseStart_3591970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591990 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3591990 : Nat := 118140960795 + 3591990 * 2 ^ 59
def prefixEnd_3591990 : Nat := 4983230072969 + 3 ^ 40 * 3591990 * 2
def baseEnd_3591990 : Nat := 1844417376143506556305745

theorem tailTrace_3591990 : CollatzResearch.WordTrace tailWord_3591990 prefixEnd_3591990 1844417376143506556305745 := by
  unfold tailWord_3591990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188164891052572993551339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87340425504560778597880949 8188164891052572993551339)
  ·
    refine ⟨12282247336578859490327009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188164891052572993551339 12282247336578859490327009)
    ·
      refine ⟨9211685502434144617745257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282247336578859490327009 9211685502434144617745257)
      ·
        refine ⟨6908764126825608463308943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9211685502434144617745257 6908764126825608463308943)
        ·
          refine ⟨10363146190238412694963415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908764126825608463308943 10363146190238412694963415)
          ·
            refine ⟨15544719285357619042445123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363146190238412694963415 15544719285357619042445123)
            ·
              refine ⟨23317078928036428563667685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15544719285357619042445123 23317078928036428563667685)
              ·
                refine ⟨4371952299006830355687691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23317078928036428563667685 4371952299006830355687691)
                ·
                  refine ⟨6557928448510245533531537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371952299006830355687691 6557928448510245533531537)
                  ·
                    refine ⟨4918446336382684150148653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6557928448510245533531537 4918446336382684150148653)
                    ·
                      refine ⟨1844417376143506556305745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4918446336382684150148653 1844417376143506556305745)
                      ·
                        rfl

theorem cell23_3591990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3591990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3591990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3591990 prefixEnd_3591990 := by exact prefixLift 3591990
  have htrace : WordTrace (prefixWord ++ tailWord_3591990) baseStart_3591990 baseEnd_3591990 := by
    simpa [prefixWord, tailWord_3591990, baseEnd_3591990] using wordTrace_append hprefix tailTrace_3591990
  have hstable : (prefixWord ++ tailWord_3591990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591990).length < 2 ^ (prefixWord ++ tailWord_3591990).sum := by decide
  have hdescent : baseEnd_3591990 < baseStart_3591990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592049 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 9]
def baseStart_3592049 : Nat := 118140960795 + 3592049 * 2 ^ 59
def prefixEnd_3592049 : Nat := 4983230072969 + 3 ^ 40 * 3592049 * 2
def baseEnd_3592049 : Nat := 204938630166902425051997

theorem tailTrace_3592049 : CollatzResearch.WordTrace tailWord_3592049 prefixEnd_3592049 204938630166902425051997 := by
  unfold tailWord_3592049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131012790163627420973219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87341860109084947315479467 131012790163627420973219201)
  ·
    refine ⟨98259592622720565729914401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131012790163627420973219201 98259592622720565729914401)
    ·
      refine ⟨73694694467040424297435801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98259592622720565729914401 73694694467040424297435801)
      ·
        refine ⟨55271020850280318223076851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73694694467040424297435801 55271020850280318223076851)
        ·
          refine ⟨82906531275420477334615277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55271020850280318223076851 82906531275420477334615277)
          ·
            refine ⟨31089949228282679000480729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82906531275420477334615277 31089949228282679000480729)
            ·
              refine ⟨23317461921212009250360547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31089949228282679000480729 23317461921212009250360547)
              ·
                refine ⟨34976192881818013875540821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23317461921212009250360547 34976192881818013875540821)
                ·
                  refine ⟨204938630166902425051997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34976192881818013875540821 204938630166902425051997)
                  ·
                    rfl

theorem cell23_3592049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_3592049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592049 prefixEnd_3592049 := by exact prefixLift 3592049
  have htrace : WordTrace (prefixWord ++ tailWord_3592049) baseStart_3592049 baseEnd_3592049 := by
    simpa [prefixWord, tailWord_3592049, baseEnd_3592049] using wordTrace_append hprefix tailTrace_3592049
  have hstable : (prefixWord ++ tailWord_3592049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592049).length < 2 ^ (prefixWord ++ tailWord_3592049).sum := by decide
  have hdescent : baseEnd_3592049 < baseStart_3592049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592076 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3592076 : Nat := 118140960795 + 3592076 * 2 ^ 59
def prefixEnd_3592076 : Nat := 4983230072969 + 3 ^ 40 * 3592076 * 2
def baseEnd_3592076 : Nat := 1844461535479793219830349

theorem tailTrace_3592076 : CollatzResearch.WordTrace tailWord_3592076 prefixEnd_3592076 1844461535479793219830349 := by
  unfold tailWord_3592076
  simp only [CollatzResearch.WordTrace]
  refine ⟨65506887467264802292226041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87342516623019736389634721 65506887467264802292226041)
  ·
    refine ⟨49130165600448601719169531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65506887467264802292226041 49130165600448601719169531)
    ·
      refine ⟨73695248400672902578754297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49130165600448601719169531 73695248400672902578754297)
      ·
        refine ⟨55271436300504676934065723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73695248400672902578754297 55271436300504676934065723)
        ·
          refine ⟨82907154450757015401098585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55271436300504676934065723 82907154450757015401098585)
          ·
            refine ⟨62180365838067761550823939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82907154450757015401098585 62180365838067761550823939)
            ·
              refine ⟨93270548757101642326235909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62180365838067761550823939 93270548757101642326235909)
              ·
                refine ⟨17488227891956557936169233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93270548757101642326235909 17488227891956557936169233)
                ·
                  refine ⟨13116170918967418452126925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488227891956557936169233 13116170918967418452126925)
                  ·
                    refine ⟨4918564094612781919547597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13116170918967418452126925 4918564094612781919547597)
                    ·
                      refine ⟨1844461535479793219830349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4918564094612781919547597 1844461535479793219830349)
                      ·
                        rfl

theorem cell23_3592076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3592076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592076 prefixEnd_3592076 := by exact prefixLift 3592076
  have htrace : WordTrace (prefixWord ++ tailWord_3592076) baseStart_3592076 baseEnd_3592076 := by
    simpa [prefixWord, tailWord_3592076, baseEnd_3592076] using wordTrace_append hprefix tailTrace_3592076
  have hstable : (prefixWord ++ tailWord_3592076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592076).length < 2 ^ (prefixWord ++ tailWord_3592076).sum := by decide
  have hdescent : baseEnd_3592076 < baseStart_3592076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592093 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3592093 : Nat := 118140960795 + 3592093 * 2 ^ 59
def prefixEnd_3592093 : Nat := 4983230072969 + 3 ^ 40 * 3592093 * 2
def baseEnd_3592093 : Nat := 1844470264650919653317771

theorem tailTrace_3592093 : CollatzResearch.WordTrace tailWord_3592093 prefixEnd_3592093 1844470264650919653317771 := by
  unfold tailWord_3592093
  simp only [CollatzResearch.WordTrace]
  refine ⟨131014394975468016487820933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87342929983645344325213955 131014394975468016487820933)
  ·
    refine ⟨24565199057900253091466425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131014394975468016487820933 24565199057900253091466425)
    ·
      refine ⟨18423899293425189818599819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24565199057900253091466425 18423899293425189818599819)
      ·
        refine ⟨27635848940137784727899729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18423899293425189818599819 27635848940137784727899729)
        ·
          refine ⟨20726886705103338545924797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27635848940137784727899729 20726886705103338545924797)
          ·
            refine ⟨7772582514413751954721799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20726886705103338545924797 7772582514413751954721799)
            ·
              refine ⟨11658873771620627932082699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772582514413751954721799 11658873771620627932082699)
              ·
                refine ⟨17488310657430941898124049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658873771620627932082699 17488310657430941898124049)
                ·
                  refine ⟨13116232993073206423593037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488310657430941898124049 13116232993073206423593037)
                  ·
                    refine ⟨4918587372402452408847389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13116232993073206423593037 4918587372402452408847389)
                    ·
                      refine ⟨1844470264650919653317771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4918587372402452408847389 1844470264650919653317771)
                      ·
                        rfl

theorem cell23_3592093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3592093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592093 prefixEnd_3592093 := by exact prefixLift 3592093
  have htrace : WordTrace (prefixWord ++ tailWord_3592093) baseStart_3592093 baseEnd_3592093 := by
    simpa [prefixWord, tailWord_3592093, baseEnd_3592093] using wordTrace_append hprefix tailTrace_3592093
  have hstable : (prefixWord ++ tailWord_3592093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592093).length < 2 ^ (prefixWord ++ tailWord_3592093).sum := by decide
  have hdescent : baseEnd_3592093 < baseStart_3592093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592094 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3592094 : Nat := 118140960795 + 3592094 * 2 ^ 59
def prefixEnd_3592094 : Nat := 4983230072969 + 3 ^ 40 * 3592094 * 2
def baseEnd_3592094 : Nat := 1844470778131574149405267

theorem tailTrace_3592094 : CollatzResearch.WordTrace tailWord_3592094 prefixEnd_3592094 1844470778131574149405267 := by
  unfold tailWord_3592094
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376803931058049207325917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87342954298976262439071557 16376803931058049207325917)
  ·
    refine ⟨6141301474146768452747219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16376803931058049207325917 6141301474146768452747219)
    ·
      refine ⟨9211952211220152679120829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6141301474146768452747219 9211952211220152679120829)
      ·
        refine ⟨3454482079207557254670311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9211952211220152679120829 3454482079207557254670311)
        ·
          refine ⟨5181723118811335882005467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454482079207557254670311 5181723118811335882005467)
          ·
            refine ⟨7772584678217003823008201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181723118811335882005467 7772584678217003823008201)
            ·
              refine ⟨5829438508662752867256151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772584678217003823008201 5829438508662752867256151)
              ·
                refine ⟨8744157762994129300884227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829438508662752867256151 8744157762994129300884227)
                ·
                  refine ⟨13116236644491193951326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744157762994129300884227 13116236644491193951326341)
                  ·
                    refine ⟨2459294370842098865873689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13116236644491193951326341 2459294370842098865873689)
                    ·
                      refine ⟨1844470778131574149405267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459294370842098865873689 1844470778131574149405267)
                      ·
                        rfl

theorem cell23_3592094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3592094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592094 prefixEnd_3592094 := by exact prefixLift 3592094
  have htrace : WordTrace (prefixWord ++ tailWord_3592094) baseStart_3592094 baseEnd_3592094 := by
    simpa [prefixWord, tailWord_3592094, baseEnd_3592094] using wordTrace_append hprefix tailTrace_3592094
  have hstable : (prefixWord ++ tailWord_3592094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592094).length < 2 ^ (prefixWord ++ tailWord_3592094).sum := by decide
  have hdescent : baseEnd_3592094 < baseStart_3592094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592113 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_3592113 : Nat := 118140960795 + 3592113 * 2 ^ 59
def prefixEnd_3592113 : Nat := 4983230072969 + 3 ^ 40 * 3592113 * 2
def baseEnd_3592113 : Nat := 614826844754669858355893

theorem tailTrace_3592113 : CollatzResearch.WordTrace tailWord_3592113 prefixEnd_3592113 614826844754669858355893 := by
  unfold tailWord_3592113
  simp only [CollatzResearch.WordTrace]
  refine ⟨131015124435395559903548993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87343416290263706602365995 131015124435395559903548993)
  ·
    refine ⟨98261343326546669927661745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131015124435395559903548993 98261343326546669927661745)
    ·
      refine ⟨73696007494910002445746309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98261343326546669927661745 73696007494910002445746309)
      ·
        refine ⟨13818001405295625458577433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73696007494910002445746309 13818001405295625458577433)
        ·
          refine ⟨10363501053971719093933075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13818001405295625458577433 10363501053971719093933075)
          ·
            refine ⟨15545251580957578640899613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363501053971719093933075 15545251580957578640899613)
            ·
              refine ⟨5829469342859091990337355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15545251580957578640899613 5829469342859091990337355)
              ·
                refine ⟨8744204014288637985506033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829469342859091990337355 8744204014288637985506033)
                ·
                  refine ⟨6558153010716478489129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8744204014288637985506033 6558153010716478489129525)
                  ·
                    refine ⟨614826844754669858355893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558153010716478489129525 614826844754669858355893)
                    ·
                      rfl

theorem cell23_3592113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_3592113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592113 prefixEnd_3592113 := by exact prefixLift 3592113
  have htrace : WordTrace (prefixWord ++ tailWord_3592113) baseStart_3592113 baseEnd_3592113 := by
    simpa [prefixWord, tailWord_3592113, baseEnd_3592113] using wordTrace_append hprefix tailTrace_3592113
  have hstable : (prefixWord ++ tailWord_3592113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592113).length < 2 ^ (prefixWord ++ tailWord_3592113).sum := by decide
  have hdescent : baseEnd_3592113 < baseStart_3592113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592143 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 3, 4]
def baseStart_3592143 : Nat := 118140960795 + 3592143 * 2 ^ 59
def prefixEnd_3592143 : Nat := 4983230072969 + 3 ^ 40 * 3592143 * 2
def baseEnd_3592143 : Nat := 614831979561214819230847

theorem tailTrace_3592143 : CollatzResearch.WordTrace tailWord_3592143 prefixEnd_3592143 614831979561214819230847 := by
  unfold tailWord_3592143
  simp only [CollatzResearch.WordTrace]
  refine ⟨131016218625286875027141083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87344145750191250018094055 131016218625286875027141083)
  ·
    refine ⟨196524327937930312540711625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131016218625286875027141083 196524327937930312540711625)
    ·
      refine ⟨147393245953447734405533719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196524327937930312540711625 147393245953447734405533719)
      ·
        refine ⟨221089868930171601608300579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147393245953447734405533719 221089868930171601608300579)
        ·
          refine ⟨331634803395257402412450869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221089868930171601608300579 331634803395257402412450869)
          ·
            refine ⟨31090762818305381476167269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331634803395257402412450869 31090762818305381476167269)
            ·
              refine ⟨5829518028432259026781363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31090762818305381476167269 5829518028432259026781363)
              ·
                refine ⟨8744277042648388540172045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829518028432259026781363 8744277042648388540172045)
                ·
                  refine ⟨3279103890993145702564517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8744277042648388540172045 3279103890993145702564517)
                  ·
                    refine ⟨614831979561214819230847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279103890993145702564517 614831979561214819230847)
                    ·
                      rfl

theorem cell23_3592143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_3592143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592143 prefixEnd_3592143 := by exact prefixLift 3592143
  have htrace : WordTrace (prefixWord ++ tailWord_3592143) baseStart_3592143 baseEnd_3592143 := by
    simpa [prefixWord, tailWord_3592143, baseEnd_3592143] using wordTrace_append hprefix tailTrace_3592143
  have hstable : (prefixWord ++ tailWord_3592143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592143).length < 2 ^ (prefixWord ++ tailWord_3592143).sum := by decide
  have hdescent : baseEnd_3592143 < baseStart_3592143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592186 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_3592186 : Nat := 118140960795 + 3592186 * 2 ^ 59
def prefixEnd_3592186 : Nat := 4983230072969 + 3 ^ 40 * 3592186 * 2
def baseEnd_3592186 : Nat := 614839339450595929818281

theorem tailTrace_3592186 : CollatzResearch.WordTrace tailWord_3592186 prefixEnd_3592186 614839339450595929818281 := by
  unfold tailWord_3592186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32754446741032773342739103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87345191309420728913970941 32754446741032773342739103)
  ·
    refine ⟨49131670111549160014108655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32754446741032773342739103 49131670111549160014108655)
    ·
      refine ⟨73697505167323740021162983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49131670111549160014108655 73697505167323740021162983)
      ·
        refine ⟨110546257750985610031744475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73697505167323740021162983 110546257750985610031744475)
        ·
          refine ⟨165819386626478415047616713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110546257750985610031744475 165819386626478415047616713)
          ·
            refine ⟨124364539969858811285712535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165819386626478415047616713 124364539969858811285712535)
            ·
              refine ⟨186546809954788216928568803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124364539969858811285712535 186546809954788216928568803)
              ·
                refine ⟨279820214932182325392853205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186546809954788216928568803 279820214932182325392853205)
                ·
                  refine ⟨6558286287473023251394997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 279820214932182325392853205 6558286287473023251394997)
                  ·
                    refine ⟨614839339450595929818281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558286287473023251394997 614839339450595929818281)
                    ·
                      rfl

theorem cell23_3592186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_3592186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592186 prefixEnd_3592186 := by exact prefixLift 3592186
  have htrace : WordTrace (prefixWord ++ tailWord_3592186) baseStart_3592186 baseEnd_3592186 := by
    simpa [prefixWord, tailWord_3592186, baseEnd_3592186] using wordTrace_append hprefix tailTrace_3592186
  have hstable : (prefixWord ++ tailWord_3592186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592186).length < 2 ^ (prefixWord ++ tailWord_3592186).sum := by decide
  have hdescent : baseEnd_3592186 < baseStart_3592186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592220 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3592220 : Nat := 118140960795 + 3592220 * 2 ^ 59
def prefixEnd_3592220 : Nat := 4983230072969 + 3 ^ 40 * 3592220 * 2
def baseEnd_3592220 : Nat := 614845158898013552143229

theorem tailTrace_3592220 : CollatzResearch.WordTrace tailWord_3592220 prefixEnd_3592220 614845158898013552143229 := by
  unfold tailWord_3592220
  simp only [CollatzResearch.WordTrace]
  refine ⟨65509513523003958588847057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87346018030671944785129409 65509513523003958588847057)
  ·
    refine ⟨49132135142252968941635293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65509513523003958588847057 49132135142252968941635293)
    ·
      refine ⟨18424550678344863353113235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49132135142252968941635293 18424550678344863353113235)
      ·
        refine ⟨27636826017517295029669853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424550678344863353113235 27636826017517295029669853)
        ·
          refine ⟨10363809756568985636126195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27636826017517295029669853 10363809756568985636126195)
          ·
            refine ⟨15545714634853478454189293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363809756568985636126195 15545714634853478454189293)
            ·
              refine ⟨5829642988070054420320985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15545714634853478454189293 5829642988070054420320985)
              ·
                refine ⟨4372232241052540815240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829642988070054420320985 4372232241052540815240739)
                ·
                  refine ⟨6558348361578811222861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372232241052540815240739 6558348361578811222861109)
                  ·
                    refine ⟨614845158898013552143229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558348361578811222861109 614845158898013552143229)
                    ·
                      rfl

theorem cell23_3592220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3592220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592220 prefixEnd_3592220 := by exact prefixLift 3592220
  have htrace : WordTrace (prefixWord ++ tailWord_3592220) baseStart_3592220 baseEnd_3592220 := by
    simpa [prefixWord, tailWord_3592220, baseEnd_3592220] using wordTrace_append hprefix tailTrace_3592220
  have hstable : (prefixWord ++ tailWord_3592220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592220).length < 2 ^ (prefixWord ++ tailWord_3592220).sum := by decide
  have hdescent : baseEnd_3592220 < baseStart_3592220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592223 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3592223 : Nat := 118140960795 + 3592223 * 2 ^ 59
def prefixEnd_3592223 : Nat := 4983230072969 + 3 ^ 40 * 3592223 * 2
def baseEnd_3592223 : Nat := 1844537017136004144692173

theorem tailTrace_3592223 : CollatzResearch.WordTrace tailWord_3592223 prefixEnd_3592223 1844537017136004144692173 := by
  unfold tailWord_3592223
  simp only [CollatzResearch.WordTrace]
  refine ⟨131019136464997048690053323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87346090976664699126702215 131019136464997048690053323)
  ·
    refine ⟨196528704697495573035079985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131019136464997048690053323 196528704697495573035079985)
    ·
      refine ⟨147396528523121679776309989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196528704697495573035079985 147396528523121679776309989)
      ·
        refine ⟨27636849098085314958058123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147396528523121679776309989 27636849098085314958058123)
        ·
          refine ⟨41455273647127972437087185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27636849098085314958058123 41455273647127972437087185)
          ·
            refine ⟨31091455235345979327815389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41455273647127972437087185 31091455235345979327815389)
            ·
              refine ⟨11659295713254742247930771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31091455235345979327815389 11659295713254742247930771)
              ·
                refine ⟨17488943569882113371896157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659295713254742247930771 17488943569882113371896157)
                ·
                  refine ⟨6558353838705792514461059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17488943569882113371896157 6558353838705792514461059)
                  ·
                    refine ⟨9837530758058688771691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558353838705792514461059 9837530758058688771691589)
                    ·
                      refine ⟨1844537017136004144692173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9837530758058688771691589 1844537017136004144692173)
                      ·
                        rfl

theorem cell23_3592223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3592223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592223 prefixEnd_3592223 := by exact prefixLift 3592223
  have htrace : WordTrace (prefixWord ++ tailWord_3592223) baseStart_3592223 baseEnd_3592223 := by
    simpa [prefixWord, tailWord_3592223, baseEnd_3592223] using wordTrace_append hprefix tailTrace_3592223
  have hstable : (prefixWord ++ tailWord_3592223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592223).length < 2 ^ (prefixWord ++ tailWord_3592223).sum := by decide
  have hdescent : baseEnd_3592223 < baseStart_3592223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592236 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3592236 : Nat := 118140960795 + 3592236 * 2 ^ 59
def prefixEnd_3592236 : Nat := 4983230072969 + 3 ^ 40 * 3592236 * 2
def baseEnd_3592236 : Nat := 1844543692384512593829613

theorem tailTrace_3592236 : CollatzResearch.WordTrace tailWord_3592236 prefixEnd_3592236 1844543692384512593829613 := by
  unfold tailWord_3592236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65509805306974975955138281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87346407075966634606851041 65509805306974975955138281)
  ·
    refine ⟨49132353980231231966353711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65509805306974975955138281 49132353980231231966353711)
    ·
      refine ⟨73698530970346847949530567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49132353980231231966353711 73698530970346847949530567)
      ·
        refine ⟨110547796455520271924295851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73698530970346847949530567 110547796455520271924295851)
        ·
          refine ⟨165821694683280407886443777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110547796455520271924295851 165821694683280407886443777)
          ·
            refine ⟨124366271012460305914832833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165821694683280407886443777 124366271012460305914832833)
            ·
              refine ⟨93274703259345229436124625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124366271012460305914832833 93274703259345229436124625)
              ·
                refine ⟨69956027444508922077093469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93274703259345229436124625 69956027444508922077093469)
                ·
                  refine ⟨26233510291690845778910051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69956027444508922077093469 26233510291690845778910051)
                  ·
                    refine ⟨39350265437536268668365077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26233510291690845778910051 39350265437536268668365077)
                    ·
                      refine ⟨1844543692384512593829613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39350265437536268668365077 1844543692384512593829613)
                      ·
                        rfl

theorem cell23_3592236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3592236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592236 prefixEnd_3592236 := by exact prefixLift 3592236
  have htrace : WordTrace (prefixWord ++ tailWord_3592236) baseStart_3592236 baseEnd_3592236 := by
    simpa [prefixWord, tailWord_3592236, baseEnd_3592236] using wordTrace_append hprefix tailTrace_3592236
  have hstable : (prefixWord ++ tailWord_3592236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592236).length < 2 ^ (prefixWord ++ tailWord_3592236).sum := by decide
  have hdescent : baseEnd_3592236 < baseStart_3592236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592243 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5]
def baseStart_3592243 : Nat := 118140960795 + 3592243 * 2 ^ 59
def prefixEnd_3592243 : Nat := 4983230072969 + 3 ^ 40 * 3592243 * 2
def baseEnd_3592243 : Nat := 1844547286749094066442081

theorem tailTrace_3592243 : CollatzResearch.WordTrace tailWord_3592243 prefixEnd_3592243 1844547286749094066442081 := by
  unfold tailWord_3592243
  simp only [CollatzResearch.WordTrace]
  refine ⟨131019865924924592105781383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87346577283283061403854255 131019865924924592105781383)
  ·
    refine ⟨196529798887386888158672075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131019865924924592105781383 196529798887386888158672075)
    ·
      refine ⟨294794698331080332238008113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196529798887386888158672075 294794698331080332238008113)
      ·
        refine ⟨221096023748310249178506085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294794698331080332238008113 221096023748310249178506085)
        ·
          refine ⟨41455504452808171720969891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221096023748310249178506085 41455504452808171720969891)
          ·
            refine ⟨62183256679212257581454837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41455504452808171720969891 62183256679212257581454837)
            ·
              refine ⟨5829680313676149148261391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62183256679212257581454837 5829680313676149148261391)
              ·
                refine ⟨8744520470514223722392087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829680313676149148261391 8744520470514223722392087)
                ·
                  refine ⟨13116780705771335583588131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744520470514223722392087 13116780705771335583588131)
                  ·
                    refine ⟨19675171058657003375382197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13116780705771335583588131 19675171058657003375382197)
                    ·
                      refine ⟨1844547286749094066442081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19675171058657003375382197 1844547286749094066442081)
                      ·
                        rfl

theorem cell23_3592243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_3592243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592243 prefixEnd_3592243 := by exact prefixLift 3592243
  have htrace : WordTrace (prefixWord ++ tailWord_3592243) baseStart_3592243 baseEnd_3592243 := by
    simpa [prefixWord, tailWord_3592243, baseEnd_3592243] using wordTrace_append hprefix tailTrace_3592243
  have hstable : (prefixWord ++ tailWord_3592243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592243).length < 2 ^ (prefixWord ++ tailWord_3592243).sum := by decide
  have hdescent : baseEnd_3592243 < baseStart_3592243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592253 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3592253 : Nat := 118140960795 + 3592253 * 2 ^ 59
def prefixEnd_3592253 : Nat := 4983230072969 + 3 ^ 40 * 3592253 * 2
def baseEnd_3592253 : Nat := 1844552421555639027317035

theorem tailTrace_3592253 : CollatzResearch.WordTrace tailWord_3592253 prefixEnd_3592253 1844552421555639027317035 := by
  unfold tailWord_3592253
  simp only [CollatzResearch.WordTrace]
  refine ⟨131020230654888363813645413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87346820436592242542430275 131020230654888363813645413)
  ·
    refine ⟨24566293247791568215058515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131020230654888363813645413 24566293247791568215058515)
    ·
      refine ⟨36849439871687352322587773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24566293247791568215058515 36849439871687352322587773)
      ·
        refine ⟨13818539951882757120970415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36849439871687352322587773 13818539951882757120970415)
        ·
          refine ⟨20727809927824135681455623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13818539951882757120970415 20727809927824135681455623)
          ·
            refine ⟨31091714891736203522183435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20727809927824135681455623 31091714891736203522183435)
            ·
              refine ⟨46637572337604305283275153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31091714891736203522183435 46637572337604305283275153)
              ·
                refine ⟨34978179253203228962456365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46637572337604305283275153 34978179253203228962456365)
                ·
                  refine ⟨13116817219951210860921137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34978179253203228962456365 13116817219951210860921137)
                  ·
                    refine ⟨9837612914963408145690853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13116817219951210860921137 9837612914963408145690853)
                    ·
                      refine ⟨1844552421555639027317035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9837612914963408145690853 1844552421555639027317035)
                      ·
                        rfl

theorem cell23_3592253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3592253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592253 prefixEnd_3592253 := by exact prefixLift 3592253
  have htrace : WordTrace (prefixWord ++ tailWord_3592253) baseStart_3592253 baseEnd_3592253 := by
    simpa [prefixWord, tailWord_3592253, baseEnd_3592253] using wordTrace_append hprefix tailTrace_3592253
  have hstable : (prefixWord ++ tailWord_3592253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592253).length < 2 ^ (prefixWord ++ tailWord_3592253).sum := by decide
  have hdescent : baseEnd_3592253 < baseStart_3592253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592270 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3592270 : Nat := 118140960795 + 3592270 * 2 ^ 59
def prefixEnd_3592270 : Nat := 4983230072969 + 3 ^ 40 * 3592270 * 2
def baseEnd_3592270 : Nat := 1844561150726765460804457

theorem tailTrace_3592270 : CollatzResearch.WordTrace tailWord_3592270 prefixEnd_3592270 1844561150726765460804457 := by
  unfold tailWord_3592270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377606336978346964626783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87347233797217850478009509 16377606336978346964626783)
  ·
    refine ⟨24566409505467520446940175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377606336978346964626783 24566409505467520446940175)
    ·
      refine ⟨36849614258201280670410263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24566409505467520446940175 36849614258201280670410263)
      ·
        refine ⟨55274421387301921005615395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36849614258201280670410263 55274421387301921005615395)
        ·
          refine ⟨82911632080952881508423093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55274421387301921005615395 82911632080952881508423093)
          ·
            refine ⟨7772965507589332641414665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82911632080952881508423093 7772965507589332641414665)
            ·
              refine ⟨5829724130691999481060999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772965507589332641414665 5829724130691999481060999)
              ·
                refine ⟨8744586196037999221591499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829724130691999481060999 8744586196037999221591499)
                ·
                  refine ⟨13116879294056998832387249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744586196037999221591499 13116879294056998832387249)
                  ·
                    refine ⟨9837659470542749124290437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13116879294056998832387249 9837659470542749124290437)
                    ·
                      refine ⟨1844561150726765460804457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9837659470542749124290437 1844561150726765460804457)
                      ·
                        rfl

theorem cell23_3592270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3592270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592270 prefixEnd_3592270 := by exact prefixLift 3592270
  have htrace : WordTrace (prefixWord ++ tailWord_3592270) baseStart_3592270 baseEnd_3592270 := by
    simpa [prefixWord, tailWord_3592270, baseEnd_3592270] using wordTrace_append hprefix tailTrace_3592270
  have hstable : (prefixWord ++ tailWord_3592270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592270).length < 2 ^ (prefixWord ++ tailWord_3592270).sum := by decide
  have hdescent : baseEnd_3592270 < baseStart_3592270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592274 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_3592274 : Nat := 118140960795 + 3592274 * 2 ^ 59
def prefixEnd_3592274 : Nat := 4983230072969 + 3 ^ 40 * 3592274 * 2
def baseEnd_3592274 : Nat := 1844563204649383445154439

theorem tailTrace_3592274 : CollatzResearch.WordTrace tailWord_3592274 prefixEnd_3592274 1844563204649383445154439 := by
  unfold tailWord_3592274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32755249146953071100039969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87347331058541522933439917 32755249146953071100039969)
  ·
    refine ⟨24566436860214803325029977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32755249146953071100039969 24566436860214803325029977)
    ·
      refine ⟨18424827645161102493772483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566436860214803325029977 18424827645161102493772483)
      ·
        refine ⟨27637241467741653740658725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424827645161102493772483 27637241467741653740658725)
        ·
          refine ⟨5181982775201560076373511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27637241467741653740658725 5181982775201560076373511)
          ·
            refine ⟨7772974162802340114560267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181982775201560076373511 7772974162802340114560267)
            ·
              refine ⟨11659461244203510171840401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772974162802340114560267 11659461244203510171840401)
              ·
                refine ⟨8744595933152632628880301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11659461244203510171840401 8744595933152632628880301)
                ·
                  refine ⟨3279223474932237235830113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8744595933152632628880301 3279223474932237235830113)
                  ·
                    refine ⟨2459417606199177926872585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3279223474932237235830113 2459417606199177926872585)
                    ·
                      refine ⟨1844563204649383445154439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459417606199177926872585 1844563204649383445154439)
                      ·
                        rfl

theorem cell23_3592274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_3592274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592274 prefixEnd_3592274 := by exact prefixLift 3592274
  have htrace : WordTrace (prefixWord ++ tailWord_3592274) baseStart_3592274 baseEnd_3592274 := by
    simpa [prefixWord, tailWord_3592274, baseEnd_3592274] using wordTrace_append hprefix tailTrace_3592274
  have hstable : (prefixWord ++ tailWord_3592274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592274).length < 2 ^ (prefixWord ++ tailWord_3592274).sum := by decide
  have hdescent : baseEnd_3592274 < baseStart_3592274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592323 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 6]
def baseStart_3592323 : Nat := 118140960795 + 3592323 * 2 ^ 59
def prefixEnd_3592323 : Nat := 4983230072969 + 3 ^ 40 * 3592323 * 2
def baseEnd_3592323 : Nat := 614862788400484584480571

theorem tailTrace_3592323 : CollatzResearch.WordTrace tailWord_3592323 prefixEnd_3592323 614862788400484584480571 := by
  unfold tailWord_3592323
  simp only [CollatzResearch.WordTrace]
  refine ⟨131022783764634765768693623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87348522509756510512462415 131022783764634765768693623)
  ·
    refine ⟨196534175646952148653040435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131022783764634765768693623 196534175646952148653040435)
    ·
      refine ⟨294801263470428222979560653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196534175646952148653040435 294801263470428222979560653)
      ·
        refine ⟨110550473801410583617335245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294801263470428222979560653 110550473801410583617335245)
        ·
          refine ⟨41456427675528968856500717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110550473801410583617335245 41456427675528968856500717)
          ·
            refine ⟨15546160378323363321187769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41456427675528968856500717 15546160378323363321187769)
            ·
              refine ⟨11659620283742522490890827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15546160378323363321187769 11659620283742522490890827)
              ·
                refine ⟨17489430425613783736336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659620283742522490890827 17489430425613783736336241)
                ·
                  refine ⟨13117072819210337802252181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17489430425613783736336241 13117072819210337802252181)
                  ·
                    refine ⟨614862788400484584480571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13117072819210337802252181 614862788400484584480571)
                    ·
                      rfl

theorem cell23_3592323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_3592323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592323 prefixEnd_3592323 := by exact prefixLift 3592323
  have htrace : WordTrace (prefixWord ++ tailWord_3592323) baseStart_3592323 baseEnd_3592323 := by
    simpa [prefixWord, tailWord_3592323, baseEnd_3592323] using wordTrace_append hprefix tailTrace_3592323
  have hstable : (prefixWord ++ tailWord_3592323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592323).length < 2 ^ (prefixWord ++ tailWord_3592323).sum := by decide
  have hdescent : baseEnd_3592323 < baseStart_3592323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592324 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3592324 : Nat := 118140960795 + 3592324 * 2 ^ 59
def prefixEnd_3592324 : Nat := 4983230072969 + 3 ^ 40 * 3592324 * 2
def baseEnd_3592324 : Nat := 1844588878682108249529209

theorem tailTrace_3592324 : CollatzResearch.WordTrace tailWord_3592324 prefixEnd_3592324 1844588878682108249529209 := by
  unfold tailWord_3592324
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511410118815571469740013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87348546825087428626320017 65511410118815571469740013)
  ·
    refine ⟨24566778794555839301152505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65511410118815571469740013 24566778794555839301152505)
    ·
      refine ⟨18425084095916879475864379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566778794555839301152505 18425084095916879475864379)
      ·
        refine ⟨27637626143875319213796569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425084095916879475864379 27637626143875319213796569)
        ·
          refine ⟨20728219607906489410347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27637626143875319213796569 20728219607906489410347427)
          ·
            refine ⟨31092329411859734115521141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728219607906489410347427 31092329411859734115521141)
            ·
              refine ⟨2914905882361850073330107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31092329411859734115521141 2914905882361850073330107)
              ·
                refine ⟨4372358823542775109995161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914905882361850073330107 4372358823542775109995161)
                ·
                  refine ⟨3279269117657081332496371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372358823542775109995161 3279269117657081332496371)
                  ·
                    refine ⟨4918903676485621998744557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3279269117657081332496371 4918903676485621998744557)
                    ·
                      refine ⟨1844588878682108249529209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4918903676485621998744557 1844588878682108249529209)
                      ·
                        rfl

theorem cell23_3592324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3592324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592324 prefixEnd_3592324 := by exact prefixLift 3592324
  have htrace : WordTrace (prefixWord ++ tailWord_3592324) baseStart_3592324 baseEnd_3592324 := by
    simpa [prefixWord, tailWord_3592324, baseEnd_3592324] using wordTrace_append hprefix tailTrace_3592324
  have hstable : (prefixWord ++ tailWord_3592324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592324).length < 2 ^ (prefixWord ++ tailWord_3592324).sum := by decide
  have hdescent : baseEnd_3592324 < baseStart_3592324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592383 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 6, 5]
def baseStart_3592383 : Nat := 118140960795 + 3592383 * 2 ^ 59
def prefixEnd_3592383 : Nat := 4983230072969 + 3 ^ 40 * 3592383 * 2
def baseEnd_3592383 : Nat := 614873058013574506230479

theorem tailTrace_3592383 : CollatzResearch.WordTrace tailWord_3592383 prefixEnd_3592383 614873058013574506230479 := by
  unfold tailWord_3592383
  simp only [CollatzResearch.WordTrace]
  refine ⟨131024972144417396015877803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87349981429611597343918535 131024972144417396015877803)
  ·
    refine ⟨196537458216626094023816705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131024972144417396015877803 196537458216626094023816705)
    ·
      refine ⟨147403093662469570517862529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196537458216626094023816705 147403093662469570517862529)
      ·
        refine ⟨110552320246852177888396897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147403093662469570517862529 110552320246852177888396897)
        ·
          refine ⟨82914240185139133416297673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110552320246852177888396897 82914240185139133416297673)
          ·
            refine ⟨62185680138854350062223255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82914240185139133416297673 62185680138854350062223255)
            ·
              refine ⟨93278520208281525093334883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62185680138854350062223255 93278520208281525093334883)
              ·
                refine ⟨139917780312422287640002325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93278520208281525093334883 139917780312422287640002325)
                ·
                  refine ⟨6558645952144794733125109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139917780312422287640002325 6558645952144794733125109)
                  ·
                    refine ⟨614873058013574506230479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558645952144794733125109 614873058013574506230479)
                    ·
                      rfl

theorem cell23_3592383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_3592383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592383 prefixEnd_3592383 := by exact prefixLift 3592383
  have htrace : WordTrace (prefixWord ++ tailWord_3592383) baseStart_3592383 baseEnd_3592383 := by
    simpa [prefixWord, tailWord_3592383, baseEnd_3592383] using wordTrace_append hprefix tailTrace_3592383
  have hstable : (prefixWord ++ tailWord_3592383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592383).length < 2 ^ (prefixWord ++ tailWord_3592383).sum := by decide
  have hdescent : baseEnd_3592383 < baseStart_3592383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592440 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_3592440 : Nat := 118140960795 + 3592440 * 2 ^ 59
def prefixEnd_3592440 : Nat := 4983230072969 + 3 ^ 40 * 3592440 * 2
def baseEnd_3592440 : Nat := 1844648442438029795678675

theorem tailTrace_3592440 : CollatzResearch.WordTrace tailWord_3592440 prefixEnd_3592440 1844648442438029795678675 := by
  unfold tailWord_3592440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65513525552605447375351387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87351367403473929833801849 65513525552605447375351387)
  ·
    refine ⟨98270288328908171063027081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65513525552605447375351387 98270288328908171063027081)
    ·
      refine ⟨73702716246681128297270311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98270288328908171063027081 73702716246681128297270311)
      ·
        refine ⟨110554074370021692445905467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73702716246681128297270311 110554074370021692445905467)
        ·
          refine ⟨165831111555032538668858201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110554074370021692445905467 165831111555032538668858201)
          ·
            refine ⟨124373333666274404001643651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165831111555032538668858201 124373333666274404001643651)
            ·
              refine ⟨186560000499411606002465477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124373333666274404001643651 186560000499411606002465477)
              ·
                refine ⟨34980000093639676125462277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186560000499411606002465477 34980000093639676125462277)
                ·
                  refine ⟨6558750017557439273524177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34980000093639676125462277 6558750017557439273524177)
                  ·
                    refine ⟨4919062513168079455143133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558750017557439273524177 4919062513168079455143133)
                    ·
                      refine ⟨1844648442438029795678675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919062513168079455143133 1844648442438029795678675)
                      ·
                        rfl

theorem cell23_3592440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_3592440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592440 prefixEnd_3592440 := by exact prefixLift 3592440
  have htrace : WordTrace (prefixWord ++ tailWord_3592440) baseStart_3592440 baseEnd_3592440 := by
    simpa [prefixWord, tailWord_3592440, baseEnd_3592440] using wordTrace_append hprefix tailTrace_3592440
  have hstable : (prefixWord ++ tailWord_3592440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592440).length < 2 ^ (prefixWord ++ tailWord_3592440).sum := by decide
  have hdescent : baseEnd_3592440 < baseStart_3592440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592457 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_3592457 : Nat := 118140960795 + 3592457 * 2 ^ 59
def prefixEnd_3592457 : Nat := 4983230072969 + 3 ^ 40 * 3592457 * 2
def baseEnd_3592457 : Nat := 1844657171609156229166097

theorem tailTrace_3592457 : CollatzResearch.WordTrace tailWord_3592457 prefixEnd_3592457 1844657171609156229166097 := by
  unfold tailWord_3592457
  simp only [CollatzResearch.WordTrace]
  refine ⟨131027671146149306654071625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87351780764099537769381083 131027671146149306654071625)
  ·
    refine ⟨98270753359611979990553719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131027671146149306654071625 98270753359611979990553719)
    ·
      refine ⟨147406130039417969985830579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98270753359611979990553719 147406130039417969985830579)
      ·
        refine ⟨221109195059126954978745869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147406130039417969985830579 221109195059126954978745869)
        ·
          refine ⟨82915948147172608117029701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221109195059126954978745869 82915948147172608117029701)
          ·
            refine ⟨15546740277594864021943069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82915948147172608117029701 15546740277594864021943069)
            ·
              refine ⟨5830027604098074008228651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15546740277594864021943069 5830027604098074008228651)
              ·
                refine ⟨8745041406147111012342977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5830027604098074008228651 8745041406147111012342977)
                ·
                  refine ⟨6558781054610333259257233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8745041406147111012342977 6558781054610333259257233)
                  ·
                    refine ⟨4919085790957749944442925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558781054610333259257233 4919085790957749944442925)
                    ·
                      refine ⟨1844657171609156229166097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919085790957749944442925 1844657171609156229166097)
                      ·
                        rfl

theorem cell23_3592457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_3592457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592457 prefixEnd_3592457 := by exact prefixLift 3592457
  have htrace : WordTrace (prefixWord ++ tailWord_3592457) baseStart_3592457 baseEnd_3592457 := by
    simpa [prefixWord, tailWord_3592457, baseEnd_3592457] using wordTrace_append hprefix tailTrace_3592457
  have hstable : (prefixWord ++ tailWord_3592457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592457).length < 2 ^ (prefixWord ++ tailWord_3592457).sum := by decide
  have hdescent : baseEnd_3592457 < baseStart_3592457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3592463 : Nat := 118140960795 + 3592463 * 2 ^ 59
def prefixEnd_3592463 : Nat := 4983230072969 + 3 ^ 40 * 3592463 * 2
def baseEnd_3592463 : Nat := 1844660252493083205691069

theorem tailTrace_3592463 : CollatzResearch.WordTrace tailWord_3592463 prefixEnd_3592463 1844660252493083205691069 := by
  unfold tailWord_3592463
  simp only [CollatzResearch.WordTrace]
  refine ⟨131027889984127569678790043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87351926656085046452526695 131027889984127569678790043)
  ·
    refine ⟨196541834976191354518185065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131027889984127569678790043 196541834976191354518185065)
    ·
      refine ⟨147406376232143515888638799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196541834976191354518185065 147406376232143515888638799)
      ·
        refine ⟨221109564348215273832958199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147406376232143515888638799 221109564348215273832958199)
        ·
          refine ⟨331664346522322910749437299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221109564348215273832958199 331664346522322910749437299)
          ·
            refine ⟨497496519783484366124155949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331664346522322910749437299 497496519783484366124155949)
            ·
              refine ⟨186561194918806637296558481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497496519783484366124155949 186561194918806637296558481)
              ·
                refine ⟨139920896189104977972418861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186561194918806637296558481 139920896189104977972418861)
                ·
                  refine ⟨52470336070914366739657073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139920896189104977972418861 52470336070914366739657073)
                  ·
                    refine ⟨39352752053185775054742805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52470336070914366739657073 39352752053185775054742805)
                    ·
                      refine ⟨1844660252493083205691069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39352752053185775054742805 1844660252493083205691069)
                      ·
                        rfl

theorem cell23_3592463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3592463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592463 prefixEnd_3592463 := by exact prefixLift 3592463
  have htrace : WordTrace (prefixWord ++ tailWord_3592463) baseStart_3592463 baseEnd_3592463 := by
    simpa [prefixWord, tailWord_3592463, baseEnd_3592463] using wordTrace_append hprefix tailTrace_3592463
  have hstable : (prefixWord ++ tailWord_3592463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592463).length < 2 ^ (prefixWord ++ tailWord_3592463).sum := by decide
  have hdescent : baseEnd_3592463 < baseStart_3592463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592477 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 8]
def baseStart_3592477 : Nat := 118140960795 + 3592477 * 2 ^ 59
def prefixEnd_3592477 : Nat := 4983230072969 + 3 ^ 40 * 3592477 * 2
def baseEnd_3592477 : Nat := 204963049024694016768445

theorem tailTrace_3592477 : CollatzResearch.WordTrace tailWord_3592477 prefixEnd_3592477 204963049024694016768445 := by
  unfold tailWord_3592477
  simp only [CollatzResearch.WordTrace]
  refine ⟨131028400606076850069799685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87352267070717900046533123 131028400606076850069799685)
  ·
    refine ⟨24567825113639409388087441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131028400606076850069799685 24567825113639409388087441)
    ·
      refine ⟨18425868835229557041065581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24567825113639409388087441 18425868835229557041065581)
      ·
        refine ⟨6909700813211083890399593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18425868835229557041065581 6909700813211083890399593)
        ·
          refine ⟨5182275609908312917799695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909700813211083890399593 5182275609908312917799695)
          ·
            refine ⟨7773413414862469376699543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182275609908312917799695 7773413414862469376699543)
            ·
              refine ⟨11660120122293704065049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773413414862469376699543 11660120122293704065049315)
              ·
                refine ⟨17490180183440556097573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11660120122293704065049315 17490180183440556097573973)
                ·
                  refine ⟨204963049024694016768445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17490180183440556097573973 204963049024694016768445)
                  ·
                    rfl

theorem cell23_3592477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_3592477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592477 prefixEnd_3592477 := by exact prefixLift 3592477
  have htrace : WordTrace (prefixWord ++ tailWord_3592477) baseStart_3592477 baseEnd_3592477 := by
    simpa [prefixWord, tailWord_3592477, baseEnd_3592477] using wordTrace_append hprefix tailTrace_3592477
  have hstable : (prefixWord ++ tailWord_3592477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592477).length < 2 ^ (prefixWord ++ tailWord_3592477).sum := by decide
  have hdescent : baseEnd_3592477 < baseStart_3592477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592480 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3592480 : Nat := 118140960795 + 3592480 * 2 ^ 59
def prefixEnd_3592480 : Nat := 4983230072969 + 3 ^ 40 * 3592480 * 2
def baseEnd_3592480 : Nat := 1844668981664209639178491

theorem tailTrace_3592480 : CollatzResearch.WordTrace tailWord_3592480 prefixEnd_3592480 1844668981664209639178491 := by
  unfold tailWord_3592480
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514255012532990791079447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87352340016710654388105929 65514255012532990791079447)
  ·
    refine ⟨98271382518799486186619171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65514255012532990791079447 98271382518799486186619171)
    ·
      refine ⟨147407073778199229279928757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98271382518799486186619171 147407073778199229279928757)
      ·
        refine ⟨13819413166706177744993321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147407073778199229279928757 13819413166706177744993321)
        ·
          refine ⟨10364559875029633308744991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13819413166706177744993321 10364559875029633308744991)
          ·
            refine ⟨15546839812544449963117487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364559875029633308744991 15546839812544449963117487)
            ·
              refine ⟨23320259718816674944676231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546839812544449963117487 23320259718816674944676231)
              ·
                refine ⟨34980389578225012417014347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23320259718816674944676231 34980389578225012417014347)
                ·
                  refine ⟨52470584367337518625521521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34980389578225012417014347 52470584367337518625521521)
                  ·
                    refine ⟨39352938275503138969141141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52470584367337518625521521 39352938275503138969141141)
                    ·
                      refine ⟨1844668981664209639178491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39352938275503138969141141 1844668981664209639178491)
                      ·
                        rfl

theorem cell23_3592480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3592480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592480 prefixEnd_3592480 := by exact prefixLift 3592480
  have htrace : WordTrace (prefixWord ++ tailWord_3592480) baseStart_3592480 baseEnd_3592480 := by
    simpa [prefixWord, tailWord_3592480, baseEnd_3592480] using wordTrace_append hprefix tailTrace_3592480
  have hstable : (prefixWord ++ tailWord_3592480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592480).length < 2 ^ (prefixWord ++ tailWord_3592480).sum := by decide
  have hdescent : baseEnd_3592480 < baseStart_3592480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592520 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_3592520 : Nat := 118140960795 + 3592520 * 2 ^ 59
def prefixEnd_3592520 : Nat := 4983230072969 + 3 ^ 40 * 3592520 * 2
def baseEnd_3592520 : Nat := 614896506963463160892769

theorem tailTrace_3592520 : CollatzResearch.WordTrace tailWord_3592520 prefixEnd_3592520 614896506963463160892769 := by
  unfold tailWord_3592520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514984472460534206807507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87353312629947378942410009 65514984472460534206807507)
  ·
    refine ⟨98272476708690801310211261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65514984472460534206807507 98272476708690801310211261)
    ·
      refine ⟨36852178765759050491329223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98272476708690801310211261 36852178765759050491329223)
      ·
        refine ⟨55278268148638575736993835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852178765759050491329223 55278268148638575736993835)
        ·
          refine ⟨82917402222957863605490753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55278268148638575736993835 82917402222957863605490753)
          ·
            refine ⟨62188051667218397704118065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82917402222957863605490753 62188051667218397704118065)
            ·
              refine ⟨46641038750413798278088549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62188051667218397704118065 46641038750413798278088549)
              ·
                refine ⟨8745194765702587177141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46641038750413798278088549 8745194765702587177141603)
                ·
                  refine ⟨13117792148553880765712405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745194765702587177141603 13117792148553880765712405)
                  ·
                    refine ⟨614896506963463160892769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13117792148553880765712405 614896506963463160892769)
                    ·
                      rfl

theorem cell23_3592520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_3592520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592520 prefixEnd_3592520 := by exact prefixLift 3592520
  have htrace : WordTrace (prefixWord ++ tailWord_3592520) baseStart_3592520 baseEnd_3592520 := by
    simpa [prefixWord, tailWord_3592520, baseEnd_3592520] using wordTrace_append hprefix tailTrace_3592520
  have hstable : (prefixWord ++ tailWord_3592520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592520).length < 2 ^ (prefixWord ++ tailWord_3592520).sum := by decide
  have hdescent : baseEnd_3592520 < baseStart_3592520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592537 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_3592537 : Nat := 118140960795 + 3592537 * 2 ^ 59
def prefixEnd_3592537 : Nat := 4983230072969 + 3 ^ 40 * 3592537 * 2
def baseEnd_3592537 : Nat := 614899416687171972055243

theorem tailTrace_3592537 : CollatzResearch.WordTrace tailWord_3592537 prefixEnd_3592537 614899416687171972055243 := by
  unfold tailWord_3592537
  simp only [CollatzResearch.WordTrace]
  refine ⟨131030588985859480316983865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87353725990572986877989243 131030588985859480316983865)
  ·
    refine ⟨98272941739394610237737899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131030588985859480316983865 98272941739394610237737899)
    ·
      refine ⟨147409412609091915356606849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98272941739394610237737899 147409412609091915356606849)
      ·
        refine ⟨110557059456818936517455137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147409412609091915356606849 110557059456818936517455137)
        ·
          refine ⟨82917794592614202388091353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110557059456818936517455137 82917794592614202388091353)
          ·
            refine ⟨62188345944460651791068515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82917794592614202388091353 62188345944460651791068515)
            ·
              refine ⟨93282518916690977686602773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62188345944460651791068515 93282518916690977686602773)
              ·
                refine ⟨4372618074219889579059505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93282518916690977686602773 4372618074219889579059505)
                ·
                  refine ⟨3279463555664917184294629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372618074219889579059505 3279463555664917184294629)
                  ·
                    refine ⟨614899416687171972055243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279463555664917184294629 614899416687171972055243)
                    ·
                      rfl

theorem cell23_3592537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_3592537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592537 prefixEnd_3592537 := by exact prefixLift 3592537
  have htrace : WordTrace (prefixWord ++ tailWord_3592537) baseStart_3592537 baseEnd_3592537 := by
    simpa [prefixWord, tailWord_3592537, baseEnd_3592537] using wordTrace_append hprefix tailTrace_3592537
  have hstable : (prefixWord ++ tailWord_3592537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592537).length < 2 ^ (prefixWord ++ tailWord_3592537).sum := by decide
  have hdescent : baseEnd_3592537 < baseStart_3592537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592547 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3592547 : Nat := 118140960795 + 3592547 * 2 ^ 59
def prefixEnd_3592547 : Nat := 4983230072969 + 3 ^ 40 * 3592547 * 2
def baseEnd_3592547 : Nat := 1844703384868060877040683

theorem tailTrace_3592547 : CollatzResearch.WordTrace tailWord_3592547 prefixEnd_3592547 1844703384868060877040683 := by
  unfold tailWord_3592547
  simp only [CollatzResearch.WordTrace]
  refine ⟨131030953715823252024847895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87353969143882168016565263 131030953715823252024847895)
  ·
    refine ⟨196546430573734878037271843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131030953715823252024847895 196546430573734878037271843)
    ·
      refine ⟨294819645860602317055907765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196546430573734878037271843 294819645860602317055907765)
      ·
        refine ⟨27639341799431467223991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294819645860602317055907765 27639341799431467223991353)
        ·
          refine ⟨20729506349573600417993515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27639341799431467223991353 20729506349573600417993515)
          ·
            refine ⟨31094259524360400626990273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20729506349573600417993515 31094259524360400626990273)
            ·
              refine ⟨23320694643270300470242705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31094259524360400626990273 23320694643270300470242705)
              ·
                refine ⟨17490520982452725352682029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23320694643270300470242705 17490520982452725352682029)
                ·
                  refine ⟨6558945368419772007255761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17490520982452725352682029 6558945368419772007255761)
                  ·
                    refine ⟨4919209026314829005441821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558945368419772007255761 4919209026314829005441821)
                    ·
                      refine ⟨1844703384868060877040683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919209026314829005441821 1844703384868060877040683)
                      ·
                        rfl

theorem cell23_3592547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3592547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592547 prefixEnd_3592547 := by exact prefixLift 3592547
  have htrace : WordTrace (prefixWord ++ tailWord_3592547) baseStart_3592547 baseEnd_3592547 := by
    simpa [prefixWord, tailWord_3592547, baseEnd_3592547] using wordTrace_append hprefix tailTrace_3592547
  have hstable : (prefixWord ++ tailWord_3592547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592547).length < 2 ^ (prefixWord ++ tailWord_3592547).sum := by decide
  have hdescent : baseEnd_3592547 < baseStart_3592547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592557 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3592557 : Nat := 118140960795 + 3592557 * 2 ^ 59
def prefixEnd_3592557 : Nat := 4983230072969 + 3 ^ 40 * 3592557 * 2
def baseEnd_3592557 : Nat := 1844708519674605837915637

theorem tailTrace_3592557 : CollatzResearch.WordTrace tailWord_3592557 prefixEnd_3592557 1844708519674605837915637 := by
  unfold tailWord_3592557
  simp only [CollatzResearch.WordTrace]
  refine ⟨131031318445787023732711925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87354212297191349155141283 131031318445787023732711925)
  ·
    refine ⟨12284186104292533474941743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131031318445787023732711925 12284186104292533474941743)
    ·
      refine ⟨18426279156438800212412615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12284186104292533474941743 18426279156438800212412615)
      ·
        refine ⟨27639418734658200318618923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18426279156438800212412615 27639418734658200318618923)
        ·
          refine ⟨41459128101987300477928385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27639418734658200318618923 41459128101987300477928385)
          ·
            refine ⟨31094346076490475358446289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41459128101987300477928385 31094346076490475358446289)
            ·
              refine ⟨23320759557367856518834717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31094346076490475358446289 23320759557367856518834717)
              ·
                refine ⟨8745284834012946194563019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23320759557367856518834717 8745284834012946194563019)
                ·
                  refine ⟨13117927251019419291844529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745284834012946194563019 13117927251019419291844529)
                  ·
                    refine ⟨9838445438264564468883397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13117927251019419291844529 9838445438264564468883397)
                    ·
                      refine ⟨1844708519674605837915637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9838445438264564468883397 1844708519674605837915637)
                      ·
                        rfl

theorem cell23_3592557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3592557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592557 prefixEnd_3592557 := by exact prefixLift 3592557
  have htrace : WordTrace (prefixWord ++ tailWord_3592557) baseStart_3592557 baseEnd_3592557 := by
    simpa [prefixWord, tailWord_3592557, baseEnd_3592557] using wordTrace_append hprefix tailTrace_3592557
  have hstable : (prefixWord ++ tailWord_3592557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592557).length < 2 ^ (prefixWord ++ tailWord_3592557).sum := by decide
  have hdescent : baseEnd_3592557 < baseStart_3592557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592618 : List Nat := [3, 1, 6, 1, 1, 1, 3, 7]
def baseStart_3592618 : Nat := 118140960795 + 3592618 * 2 ^ 59
def prefixEnd_3592618 : Nat := 4983230072969 + 3 ^ 40 * 3592618 * 2
def baseEnd_3592618 : Nat := 68323697851649262935291

theorem tailTrace_3592618 : CollatzResearch.WordTrace tailWord_3592618 prefixEnd_3592618 68323697851649262935291 := by
  unfold tailWord_3592618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32758385824641507787670627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87355695532377354100455005 32758385824641507787670627)
  ·
    refine ⟨49137578736962261681505941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32758385824641507787670627 49137578736962261681505941)
    ·
      refine ⟨2303324003295106016320591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49137578736962261681505941 2303324003295106016320591)
      ·
        refine ⟨3454986004942659024480887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303324003295106016320591 3454986004942659024480887)
        ·
          refine ⟨5182479007413988536721331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454986004942659024480887 5182479007413988536721331)
          ·
            refine ⟨7773718511120982805081997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182479007413988536721331 7773718511120982805081997)
            ·
              refine ⟨2915144441670368551905749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7773718511120982805081997 2915144441670368551905749)
              ·
                refine ⟨68323697851649262935291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2915144441670368551905749 68323697851649262935291)
                ·
                  rfl

theorem cell23_3592618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_3592618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592618 prefixEnd_3592618 := by exact prefixLift 3592618
  have htrace : WordTrace (prefixWord ++ tailWord_3592618) baseStart_3592618 baseEnd_3592618 := by
    simpa [prefixWord, tailWord_3592618, baseEnd_3592618] using wordTrace_append hprefix tailTrace_3592618
  have hstable : (prefixWord ++ tailWord_3592618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592618).length < 2 ^ (prefixWord ++ tailWord_3592618).sum := by decide
  have hdescent : baseEnd_3592618 < baseStart_3592618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592638 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_3592638 : Nat := 118140960795 + 3592638 * 2 ^ 59
def prefixEnd_3592638 : Nat := 4983230072969 + 3 ^ 40 * 3592638 * 2
def baseEnd_3592638 : Nat := 1844750111607620021002765

theorem tailTrace_3592638 : CollatzResearch.WordTrace tailWord_3592638 prefixEnd_3592638 1844750111607620021002765 := by
  unfold tailWord_3592638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16379284094811696820801321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87356181838995716377607045 16379284094811696820801321)
  ·
    refine ⟨12284463071108772615600991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16379284094811696820801321 12284463071108772615600991)
    ·
      refine ⟨18426694606663158923401487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12284463071108772615600991 18426694606663158923401487)
      ·
        refine ⟨27640041909994738385102231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18426694606663158923401487 27640041909994738385102231)
        ·
          refine ⟨41460062864992107577653347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27640041909994738385102231 41460062864992107577653347)
          ·
            refine ⟨62190094297488161366480021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41460062864992107577653347 62190094297488161366480021)
            ·
              refine ⟨2915160670194757564053751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62190094297488161366480021 2915160670194757564053751)
              ·
                refine ⟨4372741005292136346080627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915160670194757564053751 4372741005292136346080627)
                ·
                  refine ⟨6559111507938204519120941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372741005292136346080627 6559111507938204519120941)
                  ·
                    refine ⟨2459666815476826694670353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6559111507938204519120941 2459666815476826694670353)
                    ·
                      refine ⟨1844750111607620021002765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459666815476826694670353 1844750111607620021002765)
                      ·
                        rfl

theorem cell23_3592638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_3592638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592638 prefixEnd_3592638 := by exact prefixLift 3592638
  have htrace : WordTrace (prefixWord ++ tailWord_3592638) baseStart_3592638 baseEnd_3592638 := by
    simpa [prefixWord, tailWord_3592638, baseEnd_3592638] using wordTrace_append hprefix tailTrace_3592638
  have hstable : (prefixWord ++ tailWord_3592638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592638).length < 2 ^ (prefixWord ++ tailWord_3592638).sum := by decide
  have hdescent : baseEnd_3592638 < baseStart_3592638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592640 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 11]
def baseStart_3592640 : Nat := 118140960795 + 3592640 * 2 ^ 59
def prefixEnd_3592640 : Nat := 4983230072969 + 3 ^ 40 * 3592640 * 2
def baseEnd_3592640 : Nat := 204972348729881001464195

theorem tailTrace_3592640 : CollatzResearch.WordTrace tailWord_3592640 prefixEnd_3592640 204972348729881001464195 := by
  unfold tailWord_3592640
  simp only [CollatzResearch.WordTrace]
  refine ⟨65517172852243164453991687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87356230469657552605322249 65517172852243164453991687)
  ·
    refine ⟨98275759278364746680987531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65517172852243164453991687 98275759278364746680987531)
    ·
      refine ⟨147413638917547120021481297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98275759278364746680987531 147413638917547120021481297)
      ·
        refine ⟨110560229188160340016110973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147413638917547120021481297 110560229188160340016110973)
        ·
          refine ⟨41460085945560127506041615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110560229188160340016110973 41460085945560127506041615)
          ·
            refine ⟨62190128918340191259062423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41460085945560127506041615 62190128918340191259062423)
            ·
              refine ⟨93285193377510286888593635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62190128918340191259062423 93285193377510286888593635)
              ·
                refine ⟨139927790066265430332890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93285193377510286888593635 139927790066265430332890453)
                ·
                  refine ⟨204972348729881001464195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 139927790066265430332890453 204972348729881001464195)
                  ·
                    rfl

theorem cell23_3592640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_3592640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592640 prefixEnd_3592640 := by exact prefixLift 3592640
  have htrace : WordTrace (prefixWord ++ tailWord_3592640) baseStart_3592640 baseEnd_3592640 := by
    simpa [prefixWord, tailWord_3592640, baseEnd_3592640] using wordTrace_append hprefix tailTrace_3592640
  have hstable : (prefixWord ++ tailWord_3592640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592640).length < 2 ^ (prefixWord ++ tailWord_3592640).sum := by decide
  have hdescent : baseEnd_3592640 < baseStart_3592640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592647 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3592647 : Nat := 118140960795 + 3592647 * 2 ^ 59
def prefixEnd_3592647 : Nat := 4983230072969 + 3 ^ 40 * 3592647 * 2
def baseEnd_3592647 : Nat := 1844754732933510485790223

theorem tailTrace_3592647 : CollatzResearch.WordTrace tailWord_3592647 prefixEnd_3592647 1844754732933510485790223 := by
  unfold tailWord_3592647
  simp only [CollatzResearch.WordTrace]
  refine ⟨131034601015460969103488195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87356400676973979402325463 131034601015460969103488195)
  ·
    refine ⟨196551901523191453655232293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131034601015460969103488195 196551901523191453655232293)
    ·
      refine ⟨36853481535598397560356055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196551901523191453655232293 36853481535598397560356055)
      ·
        refine ⟨55280222303397596340534083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36853481535598397560356055 55280222303397596340534083)
        ·
          refine ⟨82920333455096394510801125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55280222303397596340534083 82920333455096394510801125)
          ·
            refine ⟨15547562522830573970775211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82920333455096394510801125 15547562522830573970775211)
            ·
              refine ⟨23321343784245860956162817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15547562522830573970775211 23321343784245860956162817)
              ·
                refine ⟨17491007838184395717122113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23321343784245860956162817 17491007838184395717122113)
                ·
                  refine ⟨13118255878638296787841585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17491007838184395717122113 13118255878638296787841585)
                  ·
                    refine ⟨9838691908978722590881189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13118255878638296787841585 9838691908978722590881189)
                    ·
                      refine ⟨1844754732933510485790223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9838691908978722590881189 1844754732933510485790223)
                      ·
                        rfl

theorem cell23_3592647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3592647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592647 prefixEnd_3592647 := by exact prefixLift 3592647
  have htrace : WordTrace (prefixWord ++ tailWord_3592647) baseStart_3592647 baseEnd_3592647 := by
    simpa [prefixWord, tailWord_3592647, baseEnd_3592647] using wordTrace_append hprefix tailTrace_3592647
  have hstable : (prefixWord ++ tailWord_3592647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592647).length < 2 ^ (prefixWord ++ tailWord_3592647).sum := by decide
  have hdescent : baseEnd_3592647 < baseStart_3592647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592687 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 2, 5]
def baseStart_3592687 : Nat := 118140960795 + 3592687 * 2 ^ 59
def prefixEnd_3592687 : Nat := 4983230072969 + 3 ^ 40 * 3592687 * 2
def baseEnd_3592687 : Nat := 614925090719896776430013

theorem tailTrace_3592687 : CollatzResearch.WordTrace tailWord_3592687 prefixEnd_3592687 614925090719896776430013 := by
  unfold tailWord_3592687
  simp only [CollatzResearch.WordTrace]
  refine ⟨131036059935316055934944315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87357373290210703956629543 131036059935316055934944315)
  ·
    refine ⟨196554089902974083902416473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131036059935316055934944315 196554089902974083902416473)
    ·
      refine ⟨147415567427230562926812355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196554089902974083902416473 147415567427230562926812355)
      ·
        refine ⟨221123351140845844390218533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147415567427230562926812355 221123351140845844390218533)
        ·
          refine ⟨41460628338908595823165975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221123351140845844390218533 41460628338908595823165975)
          ·
            refine ⟨62190942508362893734748963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41460628338908595823165975 62190942508362893734748963)
            ·
              refine ⟨93286413762544340602123445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62190942508362893734748963 93286413762544340602123445)
              ·
                refine ⟨8745601290238531931449073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93286413762544340602123445 8745601290238531931449073)
                ·
                  refine ⟨6559200967678898948586805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8745601290238531931449073 6559200967678898948586805)
                  ·
                    refine ⟨614925090719896776430013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6559200967678898948586805 614925090719896776430013)
                    ·
                      rfl

theorem cell23_3592687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_3592687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592687 prefixEnd_3592687 := by exact prefixLift 3592687
  have htrace : WordTrace (prefixWord ++ tailWord_3592687) baseStart_3592687 baseEnd_3592687 := by
    simpa [prefixWord, tailWord_3592687, baseEnd_3592687] using wordTrace_append hprefix tailTrace_3592687
  have hstable : (prefixWord ++ tailWord_3592687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592687).length < 2 ^ (prefixWord ++ tailWord_3592687).sum := by decide
  have hdescent : baseEnd_3592687 < baseStart_3592687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592708 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 5]
def baseStart_3592708 : Nat := 118140960795 + 3592708 * 2 ^ 59
def prefixEnd_3592708 : Nat := 4983230072969 + 3 ^ 40 * 3592708 * 2
def baseEnd_3592708 : Nat := 204976228361492749680827

theorem tailTrace_3592708 : CollatzResearch.WordTrace tailWord_3592708 prefixEnd_3592708 204976228361492749680827 := by
  unfold tailWord_3592708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65518412934119988260729389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87357883912159984347639185 65518412934119988260729389)
  ·
    refine ⟨24569404850294995597773521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65518412934119988260729389 24569404850294995597773521)
    ·
      refine ⟨18427053637721246698330141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24569404850294995597773521 18427053637721246698330141)
      ·
        refine ⟨6910145114145467511873803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18427053637721246698330141 6910145114145467511873803)
        ·
          refine ⟨10365217671218201267810705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910145114145467511873803 10365217671218201267810705)
          ·
            refine ⟨7773913253413650950858029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365217671218201267810705 7773913253413650950858029)
            ·
              refine ⟨2915217470030119106571761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7773913253413650950858029 2915217470030119106571761)
              ·
                refine ⟨2186413102522589329928821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915217470030119106571761 2186413102522589329928821)
                ·
                  refine ⟨204976228361492749680827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186413102522589329928821 204976228361492749680827)
                  ·
                    rfl

theorem cell23_3592708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_3592708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592708 prefixEnd_3592708 := by exact prefixLift 3592708
  have htrace : WordTrace (prefixWord ++ tailWord_3592708) baseStart_3592708 baseEnd_3592708 := by
    simpa [prefixWord, tailWord_3592708, baseEnd_3592708] using wordTrace_append hprefix tailTrace_3592708
  have hstable : (prefixWord ++ tailWord_3592708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592708).length < 2 ^ (prefixWord ++ tailWord_3592708).sum := by decide
  have hdescent : baseEnd_3592708 < baseStart_3592708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592764 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 6]
def baseStart_3592764 : Nat := 118140960795 + 3592764 * 2 ^ 59
def prefixEnd_3592764 : Nat := 4983230072969 + 3 ^ 40 * 3592764 * 2
def baseEnd_3592764 : Nat := 204979423352231836447465

theorem tailTrace_3592764 : CollatzResearch.WordTrace tailWord_3592764 prefixEnd_3592764 204979423352231836447465 := by
  unfold tailWord_3592764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519434178018549042748673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87359245570691398723664897 65519434178018549042748673)
  ·
    refine ⟨49139575633513911782061505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65519434178018549042748673 49139575633513911782061505)
    ·
      refine ⟨36854681725135433836546129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49139575633513911782061505 36854681725135433836546129)
      ·
        refine ⟨27641011293851575377409597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36854681725135433836546129 27641011293851575377409597)
        ·
          refine ⟨10365379235194340766528599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27641011293851575377409597 10365379235194340766528599)
          ·
            refine ⟨15548068852791511149792899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365379235194340766528599 15548068852791511149792899)
            ·
              refine ⟨23322103279187266724689349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15548068852791511149792899 23322103279187266724689349)
              ·
                refine ⟨4372894364847612510879253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23322103279187266724689349 4372894364847612510879253)
                ·
                  refine ⟨204979423352231836447465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4372894364847612510879253 204979423352231836447465)
                  ·
                    rfl

theorem cell23_3592764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_3592764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592764 prefixEnd_3592764 := by exact prefixLift 3592764
  have htrace : WordTrace (prefixWord ++ tailWord_3592764) baseStart_3592764 baseEnd_3592764 := by
    simpa [prefixWord, tailWord_3592764, baseEnd_3592764] using wordTrace_append hprefix tailTrace_3592764
  have hstable : (prefixWord ++ tailWord_3592764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592764).length < 2 ^ (prefixWord ++ tailWord_3592764).sum := by decide
  have hdescent : baseEnd_3592764 < baseStart_3592764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592767 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3592767 : Nat := 118140960795 + 3592767 * 2 ^ 59
def prefixEnd_3592767 : Nat := 4983230072969 + 3 ^ 40 * 3592767 * 2
def baseEnd_3592767 : Nat := 1844816350612050016289671

theorem tailTrace_3592767 : CollatzResearch.WordTrace tailWord_3592767 prefixEnd_3592767 1844816350612050016289671 := by
  unfold tailWord_3592767
  simp only [CollatzResearch.WordTrace]
  refine ⟨131038977775026229597856555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87359318516684153065237703 131038977775026229597856555)
  ·
    refine ⟨196558466662539344396784833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131038977775026229597856555 196558466662539344396784833)
    ·
      refine ⟨147418849996904508297588625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196558466662539344396784833 147418849996904508297588625)
      ·
        refine ⟨110564137497678381223191469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147418849996904508297588625 110564137497678381223191469)
        ·
          refine ⟨41461551561629392958696801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110564137497678381223191469 41461551561629392958696801)
          ·
            refine ⟨31096163671222044719022601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41461551561629392958696801 31096163671222044719022601)
            ·
              refine ⟨23322122753416533539266951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31096163671222044719022601 23322122753416533539266951)
              ·
                refine ⟨34983184130124800308900427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23322122753416533539266951 34983184130124800308900427)
                ·
                  refine ⟨52474776195187200463350641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34983184130124800308900427 52474776195187200463350641)
                  ·
                    refine ⟨39356082146390400347512981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52474776195187200463350641 39356082146390400347512981)
                    ·
                      refine ⟨1844816350612050016289671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39356082146390400347512981 1844816350612050016289671)
                      ·
                        rfl

theorem cell23_3592767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3592767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592767 prefixEnd_3592767 := by exact prefixLift 3592767
  have htrace : WordTrace (prefixWord ++ tailWord_3592767) baseStart_3592767 baseEnd_3592767 := by
    simpa [prefixWord, tailWord_3592767, baseEnd_3592767] using wordTrace_append hprefix tailTrace_3592767
  have hstable : (prefixWord ++ tailWord_3592767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592767).length < 2 ^ (prefixWord ++ tailWord_3592767).sum := by decide
  have hdescent : baseEnd_3592767 < baseStart_3592767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592768 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 1, 4]
def baseStart_3592768 : Nat := 118140960795 + 3592768 * 2 ^ 59
def prefixEnd_3592768 : Nat := 4983230072969 + 3 ^ 40 * 3592768 * 2
def baseEnd_3592768 : Nat := 614938954697568170792389

theorem tailTrace_3592768 : CollatzResearch.WordTrace tailWord_3592768 prefixEnd_3592768 614938954697568170792389 := by
  unfold tailWord_3592768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519507124011303384321479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87359342832015071179095305 65519507124011303384321479)
  ·
    refine ⟨98279260686016955076482219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65519507124011303384321479 98279260686016955076482219)
    ·
      refine ⟨147418891029025432614723329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98279260686016955076482219 147418891029025432614723329)
      ·
        refine ⟨110564168271769074461042497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147418891029025432614723329 110564168271769074461042497)
        ·
          refine ⟨82923126203826805845781873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110564168271769074461042497 82923126203826805845781873)
          ·
            refine ⟨62192344652870104384336405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82923126203826805845781873 62192344652870104384336405)
            ·
              refine ⟨2915266155603286143015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62192344652870104384336405 2915266155603286143015769)
              ·
                refine ⟨2186449616702464607261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915266155603286143015769 2186449616702464607261827)
                ·
                  refine ⟨3279674425053696910892741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186449616702464607261827 3279674425053696910892741)
                  ·
                    refine ⟨614938954697568170792389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279674425053696910892741 614938954697568170792389)
                    ·
                      rfl

theorem cell23_3592768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_3592768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592768 prefixEnd_3592768 := by exact prefixLift 3592768
  have htrace : WordTrace (prefixWord ++ tailWord_3592768) baseStart_3592768 baseEnd_3592768 := by
    simpa [prefixWord, tailWord_3592768, baseEnd_3592768] using wordTrace_append hprefix tailTrace_3592768
  have hstable : (prefixWord ++ tailWord_3592768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592768).length < 2 ^ (prefixWord ++ tailWord_3592768).sum := by decide
  have hdescent : baseEnd_3592768 < baseStart_3592768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592781 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3592781 : Nat := 118140960795 + 3592781 * 2 ^ 59
def prefixEnd_3592781 : Nat := 4983230072969 + 3 ^ 40 * 3592781 * 2
def baseEnd_3592781 : Nat := 204980393260134773501623

theorem tailTrace_3592781 : CollatzResearch.WordTrace tailWord_3592781 prefixEnd_3592781 204980393260134773501623 := by
  unfold tailWord_3592781
  simp only [CollatzResearch.WordTrace]
  refine ⟨131039488396975509988866197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87359658931317006659244131 131039488396975509988866197)
  ·
    refine ⟨6142476018608227030728103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131039488396975509988866197 6142476018608227030728103)
    ·
      refine ⟨9213714027912340546092155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142476018608227030728103 9213714027912340546092155)
      ·
        refine ⟨13820571041868510819138233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213714027912340546092155 13820571041868510819138233)
        ·
          refine ⟨10365428281401383114353675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13820571041868510819138233 10365428281401383114353675)
          ·
            refine ⟨15548142422102074671530513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365428281401383114353675 15548142422102074671530513)
            ·
              refine ⟨11661106816576556003647885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15548142422102074671530513 11661106816576556003647885)
              ·
                refine ⟨4372915056216208501367957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11661106816576556003647885 4372915056216208501367957)
                ·
                  refine ⟨204980393260134773501623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4372915056216208501367957 204980393260134773501623)
                  ·
                    rfl

theorem cell23_3592781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3592781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592781 prefixEnd_3592781 := by exact prefixLift 3592781
  have htrace : WordTrace (prefixWord ++ tailWord_3592781) baseStart_3592781 baseEnd_3592781 := by
    simpa [prefixWord, tailWord_3592781, baseEnd_3592781] using wordTrace_append hprefix tailTrace_3592781
  have hstable : (prefixWord ++ tailWord_3592781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592781).length < 2 ^ (prefixWord ++ tailWord_3592781).sum := by decide
  have hdescent : baseEnd_3592781 < baseStart_3592781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592791 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_3592791 : Nat := 118140960795 + 3592791 * 2 ^ 59
def prefixEnd_3592791 : Nat := 4983230072969 + 3 ^ 40 * 3592791 * 2
def baseEnd_3592791 : Nat := 1844828674147757922389561

theorem tailTrace_3592791 : CollatzResearch.WordTrace tailWord_3592791 prefixEnd_3592791 1844828674147757922389561 := by
  unfold tailWord_3592791
  simp only [CollatzResearch.WordTrace]
  refine ⟨131039853126939281696730227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87359902084626187797820151 131039853126939281696730227)
  ·
    refine ⟨196559779690408922545095341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131039853126939281696730227 196559779690408922545095341)
    ·
      refine ⟨73709917383903345954410753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196559779690408922545095341 73709917383903345954410753)
      ·
        refine ⟨55282438037927509465808065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73709917383903345954410753 55282438037927509465808065)
        ·
          refine ⟨41461828528445632099356049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55282438037927509465808065 41461828528445632099356049)
          ·
            refine ⟨31096371396334224074517037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41461828528445632099356049 31096371396334224074517037)
            ·
              refine ⟨11661139273625334027943889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31096371396334224074517037 11661139273625334027943889)
              ·
                refine ⟨8745854455219000520957917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11661139273625334027943889 8745854455219000520957917)
                ·
                  refine ⟨3279695420707125195359219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8745854455219000520957917 3279695420707125195359219)
                  ·
                    refine ⟨4919543131060687793038829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3279695420707125195359219 4919543131060687793038829)
                    ·
                      refine ⟨1844828674147757922389561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919543131060687793038829 1844828674147757922389561)
                      ·
                        rfl

theorem cell23_3592791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_3592791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592791 prefixEnd_3592791 := by exact prefixLift 3592791
  have htrace : WordTrace (prefixWord ++ tailWord_3592791) baseStart_3592791 baseEnd_3592791 := by
    simpa [prefixWord, tailWord_3592791, baseEnd_3592791] using wordTrace_append hprefix tailTrace_3592791
  have hstable : (prefixWord ++ tailWord_3592791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592791).length < 2 ^ (prefixWord ++ tailWord_3592791).sum := by decide
  have hdescent : baseEnd_3592791 < baseStart_3592791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592801 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_3592801 : Nat := 118140960795 + 3592801 * 2 ^ 59
def prefixEnd_3592801 : Nat := 4983230072969 + 3 ^ 40 * 3592801 * 2
def baseEnd_3592801 : Nat := 1844833808954302883264515

theorem tailTrace_3592801 : CollatzResearch.WordTrace tailWord_3592801 prefixEnd_3592801 1844833808954302883264515 := by
  unfold tailWord_3592801
  simp only [CollatzResearch.WordTrace]
  refine ⟨131040217856903053404594257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87360145237935368936396171 131040217856903053404594257)
  ·
    refine ⟨98280163392677290053445693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131040217856903053404594257 98280163392677290053445693)
    ·
      refine ⟨36855061272253983770042135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98280163392677290053445693 36855061272253983770042135)
      ·
        refine ⟨55282591908380975655063203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36855061272253983770042135 55282591908380975655063203)
        ·
          refine ⟨82923887862571463482594805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55282591908380975655063203 82923887862571463482594805)
          ·
            refine ⟨7774114487116074701493263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82923887862571463482594805 7774114487116074701493263)
            ·
              refine ⟨11661171730674112052239895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774114487116074701493263 11661171730674112052239895)
              ·
                refine ⟨17491757596011168078359843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661171730674112052239895 17491757596011168078359843)
                ·
                  refine ⟨26237636394016752117539765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17491757596011168078359843 26237636394016752117539765)
                  ·
                    refine ⟨2459778411939070511019353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26237636394016752117539765 2459778411939070511019353)
                    ·
                      refine ⟨1844833808954302883264515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2459778411939070511019353 1844833808954302883264515)
                      ·
                        rfl

theorem cell23_3592801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_3592801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592801 prefixEnd_3592801 := by exact prefixLift 3592801
  have htrace : WordTrace (prefixWord ++ tailWord_3592801) baseStart_3592801 baseEnd_3592801 := by
    simpa [prefixWord, tailWord_3592801, baseEnd_3592801] using wordTrace_append hprefix tailTrace_3592801
  have hstable : (prefixWord ++ tailWord_3592801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592801).length < 2 ^ (prefixWord ++ tailWord_3592801).sum := by decide
  have hdescent : baseEnd_3592801 < baseStart_3592801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592802 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3592802 : Nat := 118140960795 + 3592802 * 2 ^ 59
def prefixEnd_3592802 : Nat := 4983230072969 + 3 ^ 40 * 3592802 * 2
def baseEnd_3592802 : Nat := 614944774144985793117337

theorem tailTrace_3592802 : CollatzResearch.WordTrace tailWord_3592802 prefixEnd_3592802 614944774144985793117337 := by
  unfold tailWord_3592802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32760063582474857643845165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87360169553266287050253773 32760063582474857643845165)
  ·
    refine ⟨12285023843428071616441937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32760063582474857643845165 12285023843428071616441937)
    ·
      refine ⟨9213767882571053712331453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12285023843428071616441937 9213767882571053712331453)
      ·
        refine ⟨3455162955964145142124295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9213767882571053712331453 3455162955964145142124295)
        ·
          refine ⟨5182744433946217713186443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455162955964145142124295 5182744433946217713186443)
          ·
            refine ⟨7774116650919326569779665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182744433946217713186443 7774116650919326569779665)
            ·
              refine ⟨5830587488189494927334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774116650919326569779665 5830587488189494927334749)
              ·
                refine ⟨2186470308071060597750531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5830587488189494927334749 2186470308071060597750531)
                ·
                  refine ⟨3279705462106590896625797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186470308071060597750531 3279705462106590896625797)
                  ·
                    refine ⟨614944774144985793117337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279705462106590896625797 614944774144985793117337)
                    ·
                      rfl

theorem cell23_3592802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3592802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592802 prefixEnd_3592802 := by exact prefixLift 3592802
  have htrace : WordTrace (prefixWord ++ tailWord_3592802) baseStart_3592802 baseEnd_3592802 := by
    simpa [prefixWord, tailWord_3592802, baseEnd_3592802] using wordTrace_append hprefix tailTrace_3592802
  have hstable : (prefixWord ++ tailWord_3592802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592802).length < 2 ^ (prefixWord ++ tailWord_3592802).sum := by decide
  have hdescent : baseEnd_3592802 < baseStart_3592802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592824 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_3592824 : Nat := 118140960795 + 3592824 * 2 ^ 59
def prefixEnd_3592824 : Nat := 4983230072969 + 3 ^ 40 * 3592824 * 2
def baseEnd_3592824 : Nat := 614948539669785431092303

theorem tailTrace_3592824 : CollatzResearch.WordTrace tailWord_3592824 prefixEnd_3592824 614948539669785431092303 := by
  unfold tailWord_3592824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65520528367909864166340763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87360704490546485555121017 65520528367909864166340763)
  ·
    refine ⟨98280792551864796249511145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65520528367909864166340763 98280792551864796249511145)
    ·
      refine ⟨73710594413898597187133359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98280792551864796249511145 73710594413898597187133359)
      ·
        refine ⟨110565891620847895780700039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73710594413898597187133359 110565891620847895780700039)
        ·
          refine ⟨165848837431271843671050059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110565891620847895780700039 165848837431271843671050059)
          ·
            refine ⟨248773256146907765506575089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165848837431271843671050059 248773256146907765506575089)
            ·
              refine ⟨186579942110180824129931317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248773256146907765506575089 186579942110180824129931317)
              ·
                refine ⟨17491869572829452262181061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186579942110180824129931317 17491869572829452262181061)
                ·
                  refine ⟨3279725544905522299158949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17491869572829452262181061 3279725544905522299158949)
                  ·
                    refine ⟨614948539669785431092303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279725544905522299158949 614948539669785431092303)
                    ·
                      rfl

theorem cell23_3592824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_3592824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592824 prefixEnd_3592824 := by exact prefixLift 3592824
  have htrace : WordTrace (prefixWord ++ tailWord_3592824) baseStart_3592824 baseEnd_3592824 := by
    simpa [prefixWord, tailWord_3592824, baseEnd_3592824] using wordTrace_append hprefix tailTrace_3592824
  have hstable : (prefixWord ++ tailWord_3592824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592824).length < 2 ^ (prefixWord ++ tailWord_3592824).sum := by decide
  have hdescent : baseEnd_3592824 < baseStart_3592824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592844 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3592844 : Nat := 118140960795 + 3592844 * 2 ^ 59
def prefixEnd_3592844 : Nat := 4983230072969 + 3 ^ 40 * 3592844 * 2
def baseEnd_3592844 : Nat := 1844855888622446215026817

theorem tailTrace_3592844 : CollatzResearch.WordTrace tailWord_3592844 prefixEnd_3592844 1844855888622446215026817 := by
  unfold tailWord_3592844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65520893097873635874204793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87361190797164847832273057 65520893097873635874204793)
  ·
    refine ⟨49140669823405226905653595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65520893097873635874204793 49140669823405226905653595)
    ·
      refine ⟨73711004735107840358480393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49140669823405226905653595 73711004735107840358480393)
      ·
        refine ⟨55283253551330880268860295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73711004735107840358480393 55283253551330880268860295)
        ·
          refine ⟨82924880326996320403290443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55283253551330880268860295 82924880326996320403290443)
          ·
            refine ⟨124387320490494480604935665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82924880326996320403290443 124387320490494480604935665)
            ·
              refine ⟨93290490367870860453701749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124387320490494480604935665 93290490367870860453701749)
              ·
                refine ⟨8745983471987893167534539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93290490367870860453701749 8745983471987893167534539)
                ·
                  refine ⟨13118975207981839751301809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745983471987893167534539 13118975207981839751301809)
                  ·
                    refine ⟨9839231405986379813476357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13118975207981839751301809 9839231405986379813476357)
                    ·
                      refine ⟨1844855888622446215026817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9839231405986379813476357 1844855888622446215026817)
                      ·
                        rfl

theorem cell23_3592844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3592844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592844 prefixEnd_3592844 := by exact prefixLift 3592844
  have htrace : WordTrace (prefixWord ++ tailWord_3592844) baseStart_3592844 baseEnd_3592844 := by
    simpa [prefixWord, tailWord_3592844, baseEnd_3592844] using wordTrace_append hprefix tailTrace_3592844
  have hstable : (prefixWord ++ tailWord_3592844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592844).length < 2 ^ (prefixWord ++ tailWord_3592844).sum := by decide
  have hdescent : baseEnd_3592844 < baseStart_3592844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3592847 : Nat := 118140960795 + 3592847 * 2 ^ 59
def prefixEnd_3592847 : Nat := 4983230072969 + 3 ^ 40 * 3592847 * 2
def baseEnd_3592847 : Nat := 1844857429064409703289303

theorem tailTrace_3592847 : CollatzResearch.WordTrace tailWord_3592847 prefixEnd_3592847 1844857429064409703289303 := by
  unfold tailWord_3592847
  simp only [CollatzResearch.WordTrace]
  refine ⟨131041895614736403260768795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87361263743157602173845863 131041895614736403260768795)
  ·
    refine ⟨196562843422104604891153193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131041895614736403260768795 196562843422104604891153193)
    ·
      refine ⟨147422132566578453668364895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196562843422104604891153193 147422132566578453668364895)
      ·
        refine ⟨221133198849867680502547343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147422132566578453668364895 221133198849867680502547343)
        ·
          refine ⟨331699798274801520753821015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221133198849867680502547343 331699798274801520753821015)
          ·
            refine ⟨497549697412202281130731523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331699798274801520753821015 497549697412202281130731523)
            ·
              refine ⟨746324546118303421696097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497549697412202281130731523 746324546118303421696097285)
              ·
                refine ⟨139935852397181891568018241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746324546118303421696097285 139935852397181891568018241)
                ·
                  refine ⟨104951889297886418676013681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139935852397181891568018241 104951889297886418676013681)
                  ·
                    refine ⟨78713916973414814007010261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104951889297886418676013681 78713916973414814007010261)
                    ·
                      refine ⟨1844857429064409703289303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78713916973414814007010261 1844857429064409703289303)
                      ·
                        rfl

theorem cell23_3592847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3592847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592847 prefixEnd_3592847 := by exact prefixLift 3592847
  have htrace : WordTrace (prefixWord ++ tailWord_3592847) baseStart_3592847 baseEnd_3592847 := by
    simpa [prefixWord, tailWord_3592847, baseEnd_3592847] using wordTrace_append hprefix tailTrace_3592847
  have hstable : (prefixWord ++ tailWord_3592847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592847).length < 2 ^ (prefixWord ++ tailWord_3592847).sum := by decide
  have hdescent : baseEnd_3592847 < baseStart_3592847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592902 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3592902 : Nat := 118140960795 + 3592902 * 2 ^ 59
def prefixEnd_3592902 : Nat := 4983230072969 + 3 ^ 40 * 3592902 * 2
def baseEnd_3592902 : Nat := 1844885670500406988101551

theorem tailTrace_3592902 : CollatzResearch.WordTrace tailWord_3592902 prefixEnd_3592902 1844885670500406988101551 := by
  unfold tailWord_3592902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4095121925923035864188155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87362601086358098436013973 4095121925923035864188155)
  ·
    refine ⟨6142682888884553796282233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4095121925923035864188155 6142682888884553796282233)
    ·
      refine ⟨4607012166663415347211675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6142682888884553796282233 4607012166663415347211675)
      ·
        refine ⟨6910518249995123020817513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607012166663415347211675 6910518249995123020817513)
        ·
          refine ⟨5182888687496342265613135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6910518249995123020817513 5182888687496342265613135)
          ·
            refine ⟨7774333031244513398419703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182888687496342265613135 7774333031244513398419703)
            ·
              refine ⟨11661499546866770097629555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774333031244513398419703 11661499546866770097629555)
              ·
                refine ⟨17492249320300155146444333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661499546866770097629555 17492249320300155146444333)
                ·
                  refine ⟨6559593495112558179916625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17492249320300155146444333 6559593495112558179916625)
                  ·
                    refine ⟨4919695121334418634937469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6559593495112558179916625 4919695121334418634937469)
                    ·
                      refine ⟨1844885670500406988101551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919695121334418634937469 1844885670500406988101551)
                      ·
                        rfl

theorem cell23_3592902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3592902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592902 prefixEnd_3592902 := by exact prefixLift 3592902
  have htrace : WordTrace (prefixWord ++ tailWord_3592902) baseStart_3592902 baseEnd_3592902 := by
    simpa [prefixWord, tailWord_3592902, baseEnd_3592902] using wordTrace_append hprefix tailTrace_3592902
  have hstable : (prefixWord ++ tailWord_3592902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592902).length < 2 ^ (prefixWord ++ tailWord_3592902).sum := by decide
  have hdescent : baseEnd_3592902 < baseStart_3592902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592941 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3592941 : Nat := 118140960795 + 3592941 * 2 ^ 59
def prefixEnd_3592941 : Nat := 4983230072969 + 3 ^ 40 * 3592941 * 2
def baseEnd_3592941 : Nat := 1844905696245932335513871

theorem tailTrace_3592941 : CollatzResearch.WordTrace tailWord_3592941 prefixEnd_3592941 1844905696245932335513871 := by
  unfold tailWord_3592941
  simp only [CollatzResearch.WordTrace]
  refine ⟨131045324076395857314690677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87363549384263904876460451 131045324076395857314690677)
  ·
    refine ⟨12285499132162111623252251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131045324076395857314690677 12285499132162111623252251)
    ·
      refine ⟨18428248698243167434878377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12285499132162111623252251 18428248698243167434878377)
      ·
        refine ⟨13821186523682375576158783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18428248698243167434878377 13821186523682375576158783)
        ·
          refine ⟨20731779785523563364238175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13821186523682375576158783 20731779785523563364238175)
          ·
            refine ⟨31097669678285345046357263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20731779785523563364238175 31097669678285345046357263)
            ·
              refine ⟨46646504517428017569535895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31097669678285345046357263 46646504517428017569535895)
              ·
                refine ⟨69969756776142026354303843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46646504517428017569535895 69969756776142026354303843)
                ·
                  refine ⟨104954635164213039531455765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69969756776142026354303843 104954635164213039531455765)
                  ·
                    refine ⟨4919748523322486228036989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104954635164213039531455765 4919748523322486228036989)
                    ·
                      refine ⟨1844905696245932335513871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4919748523322486228036989 1844905696245932335513871)
                      ·
                        rfl

theorem cell23_3592941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3592941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592941 prefixEnd_3592941 := by exact prefixLift 3592941
  have htrace : WordTrace (prefixWord ++ tailWord_3592941) baseStart_3592941 baseEnd_3592941 := by
    simpa [prefixWord, tailWord_3592941, baseEnd_3592941] using wordTrace_append hprefix tailTrace_3592941
  have hstable : (prefixWord ++ tailWord_3592941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592941).length < 2 ^ (prefixWord ++ tailWord_3592941).sum := by decide
  have hdescent : baseEnd_3592941 < baseStart_3592941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592944 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 7]
def baseStart_3592944 : Nat := 118140960795 + 3592944 * 2 ^ 59
def prefixEnd_3592944 : Nat := 4983230072969 + 3 ^ 40 * 3592944 * 2
def baseEnd_3592944 : Nat := 204989692965321758197373

theorem tailTrace_3592944 : CollatzResearch.WordTrace tailWord_3592944 prefixEnd_3592944 204989692965321758197373 := by
  unfold tailWord_3592944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65522716747692494413524943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87363622330256659218033257 65522716747692494413524943)
  ·
    refine ⟨98284075121538741620287415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65522716747692494413524943 98284075121538741620287415)
    ·
      refine ⟨147426112682308112430431123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98284075121538741620287415 147426112682308112430431123)
      ·
        refine ⟨221139169023462168645646685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147426112682308112430431123 221139169023462168645646685)
        ·
          refine ⟨82927188383798313242117507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221139169023462168645646685 82927188383798313242117507)
          ·
            refine ⟨124390782575697469863176261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82927188383798313242117507 124390782575697469863176261)
            ·
              refine ⟨23323271732943275599345549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124390782575697469863176261 23323271732943275599345549)
              ·
                refine ⟨8746226899853728349754581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23323271732943275599345549 8746226899853728349754581)
                ·
                  refine ⟨204989692965321758197373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8746226899853728349754581 204989692965321758197373)
                  ·
                    rfl

theorem cell23_3592944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_3592944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3592944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3592944 prefixEnd_3592944 := by exact prefixLift 3592944
  have htrace : WordTrace (prefixWord ++ tailWord_3592944) baseStart_3592944 baseEnd_3592944 := by
    simpa [prefixWord, tailWord_3592944, baseEnd_3592944] using wordTrace_append hprefix tailTrace_3592944
  have hstable : (prefixWord ++ tailWord_3592944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592944).length < 2 ^ (prefixWord ++ tailWord_3592944).sum := by decide
  have hdescent : baseEnd_3592944 < baseStart_3592944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593011 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_3593011 : Nat := 118140960795 + 3593011 * 2 ^ 59
def prefixEnd_3593011 : Nat := 4983230072969 + 3 ^ 40 * 3593011 * 2
def baseEnd_3593011 : Nat := 1844941639891747061638549

theorem tailTrace_3593011 : CollatzResearch.WordTrace tailWord_3593011 prefixEnd_3593011 1844941639891747061638549 := by
  unfold tailWord_3593011
  simp only [CollatzResearch.WordTrace]
  refine ⟨131047877186142259269738887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87365251457428172846492591 131047877186142259269738887)
  ·
    refine ⟨196571815779213388904608331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131047877186142259269738887 196571815779213388904608331)
    ·
      refine ⟨294857723668820083356912497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196571815779213388904608331 294857723668820083356912497)
      ·
        refine ⟨221143292751615062517684373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294857723668820083356912497 221143292751615062517684373)
        ·
          refine ⟨10366091847731956055516455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221143292751615062517684373 10366091847731956055516455)
          ·
            refine ⟨15549137771597934083274683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366091847731956055516455 15549137771597934083274683)
            ·
              refine ⟨23323706657396901124912025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15549137771597934083274683 23323706657396901124912025)
              ·
                refine ⟨17492779993047675843684019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23323706657396901124912025 17492779993047675843684019)
                ·
                  refine ⟨26239169989571513765526029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17492779993047675843684019 26239169989571513765526029)
                  ·
                    refine ⟨9839688746089317662072261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26239169989571513765526029 9839688746089317662072261)
                    ·
                      refine ⟨1844941639891747061638549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9839688746089317662072261 1844941639891747061638549)
                      ·
                        rfl

theorem cell23_3593011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_3593011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593011 prefixEnd_3593011 := by exact prefixLift 3593011
  have htrace : WordTrace (prefixWord ++ tailWord_3593011) baseStart_3593011 baseEnd_3593011 := by
    simpa [prefixWord, tailWord_3593011, baseEnd_3593011] using wordTrace_append hprefix tailTrace_3593011
  have hstable : (prefixWord ++ tailWord_3593011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593011).length < 2 ^ (prefixWord ++ tailWord_3593011).sum := by decide
  have hdescent : baseEnd_3593011 < baseStart_3593011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593106 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3593106 : Nat := 118140960795 + 3593106 * 2 ^ 59
def prefixEnd_3593106 : Nat := 4983230072969 + 3 ^ 40 * 3593106 * 2
def baseEnd_3593106 : Nat := 614996806851308063316871

theorem tailTrace_3593106 : CollatzResearch.WordTrace tailWord_3593106 prefixEnd_3593106 614996806851308063316871 := by
  unfold tailWord_3593106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32762835530199522623611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87367561413865393662964781 32762835530199522623611793)
  ·
    refine ⟨24572126647649641967708845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32762835530199522623611793 24572126647649641967708845)
    ·
      refine ⟨9214547492868615737890817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24572126647649641967708845 9214547492868615737890817)
      ·
        refine ⟨6910910619651461803418113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9214547492868615737890817 6910910619651461803418113)
        ·
          refine ⟨5183182964738596352563585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6910910619651461803418113 5183182964738596352563585)
          ·
            refine ⟨3887387223553947264422689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5183182964738596352563585 3887387223553947264422689)
            ·
              refine ⟨2915540417665460448317017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887387223553947264422689 2915540417665460448317017)
              ·
                refine ⟨2186655313249095336237763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915540417665460448317017 2186655313249095336237763)
                ·
                  refine ⟨3279982969873643004356645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186655313249095336237763 3279982969873643004356645)
                  ·
                    refine ⟨614996806851308063316871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3279982969873643004356645 614996806851308063316871)
                    ·
                      rfl

theorem cell23_3593106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3593106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593106 prefixEnd_3593106 := by exact prefixLift 3593106
  have htrace : WordTrace (prefixWord ++ tailWord_3593106) baseStart_3593106 baseEnd_3593106 := by
    simpa [prefixWord, tailWord_3593106, baseEnd_3593106] using wordTrace_append hprefix tailTrace_3593106
  have hstable : (prefixWord ++ tailWord_3593106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593106).length < 2 ^ (prefixWord ++ tailWord_3593106).sum := by decide
  have hdescent : baseEnd_3593106 < baseStart_3593106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593111 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 6]
def baseStart_3593111 : Nat := 118140960795 + 3593111 * 2 ^ 59
def prefixEnd_3593111 : Nat := 4983230072969 + 3 ^ 40 * 3593111 * 2
def baseEnd_3593111 : Nat := 614997662652398890129363

theorem tailTrace_3593111 : CollatzResearch.WordTrace tailWord_3593111 prefixEnd_3593111 614997662652398890129363 := by
  unfold tailWord_3593111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131051524485779976348379187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87367682990519984232252791 131051524485779976348379187)
  ·
    refine ⟨196577286728669964522568781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131051524485779976348379187 196577286728669964522568781)
    ·
      refine ⟨73716482523251236695963293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196577286728669964522568781 73716482523251236695963293)
      ·
        refine ⟨27643680946219213760986235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73716482523251236695963293 27643680946219213760986235)
        ·
          refine ⟨41465521419328820641479353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27643680946219213760986235 41465521419328820641479353)
          ·
            refine ⟨31099141064496615481109515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41465521419328820641479353 31099141064496615481109515)
            ·
              refine ⟨46648711596744923221664273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31099141064496615481109515 46648711596744923221664273)
              ·
                refine ⟨34986533697558692416248205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46648711596744923221664273 34986533697558692416248205)
                ·
                  refine ⟨13119950136584509656093077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34986533697558692416248205 13119950136584509656093077)
                  ·
                    refine ⟨614997662652398890129363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13119950136584509656093077 614997662652398890129363)
                    ·
                      rfl

theorem cell23_3593111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_3593111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593111 prefixEnd_3593111 := by exact prefixLift 3593111
  have htrace : WordTrace (prefixWord ++ tailWord_3593111) baseStart_3593111 baseEnd_3593111 := by
    simpa [prefixWord, tailWord_3593111, baseEnd_3593111] using wordTrace_append hprefix tailTrace_3593111
  have hstable : (prefixWord ++ tailWord_3593111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593111).length < 2 ^ (prefixWord ++ tailWord_3593111).sum := by decide
  have hdescent : baseEnd_3593111 < baseStart_3593111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593131 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_3593131 : Nat := 118140960795 + 3593131 * 2 ^ 59
def prefixEnd_3593131 : Nat := 4983230072969 + 3 ^ 40 * 3593131 * 2
def baseEnd_3593131 : Nat := 1845003257570286592137997

theorem tailTrace_3593131 : CollatzResearch.WordTrace tailWord_3593131 prefixEnd_3593131 1845003257570286592137997 := by
  unfold tailWord_3593131
  simp only [CollatzResearch.WordTrace]
  refine ⟨131052253945707519764107247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87368169297138346509404831 131052253945707519764107247)
  ·
    refine ⟨196578380918561279646160871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131052253945707519764107247 196578380918561279646160871)
    ·
      refine ⟨294867571377841919469241307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196578380918561279646160871 294867571377841919469241307)
      ·
        refine ⟨442301357066762879203861961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294867571377841919469241307 442301357066762879203861961)
        ·
          refine ⟨331726017800072159402896471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442301357066762879203861961 331726017800072159402896471)
          ·
            refine ⟨497589026700108239104344707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331726017800072159402896471 497589026700108239104344707)
            ·
              refine ⟨746383540050162358656517061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497589026700108239104344707 746383540050162358656517061)
              ·
                refine ⟨139946913759405442248096949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746383540050162358656517061 139946913759405442248096949)
                ·
                  refine ⟨13120023164944260210759089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139946913759405442248096949 13120023164944260210759089)
                  ·
                    refine ⟨9840017373708195158069317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13120023164944260210759089 9840017373708195158069317)
                    ·
                      refine ⟨1845003257570286592137997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9840017373708195158069317 1845003257570286592137997)
                      ·
                        rfl

theorem cell23_3593131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_3593131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593131 prefixEnd_3593131 := by exact prefixLift 3593131
  have htrace : WordTrace (prefixWord ++ tailWord_3593131) baseStart_3593131 baseEnd_3593131 := by
    simpa [prefixWord, tailWord_3593131, baseEnd_3593131] using wordTrace_append hprefix tailTrace_3593131
  have hstable : (prefixWord ++ tailWord_3593131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593131).length < 2 ^ (prefixWord ++ tailWord_3593131).sum := by decide
  have hdescent : baseEnd_3593131 < baseStart_3593131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593149 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_3593149 : Nat := 118140960795 + 3593149 * 2 ^ 59
def prefixEnd_3593149 : Nat := 4983230072969 + 3 ^ 40 * 3593149 * 2
def baseEnd_3593149 : Nat := 615004166740689173904305

theorem tailTrace_3593149 : CollatzResearch.WordTrace tailWord_3593149 prefixEnd_3593149 615004166740689173904305 := by
  unfold tailWord_3593149
  simp only [CollatzResearch.WordTrace]
  refine ⟨131052910459642308838262501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87368606973094872558841667 131052910459642308838262501)
  ·
    refine ⟨24572420711182932907174219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131052910459642308838262501 24572420711182932907174219)
    ·
      refine ⟨36858631066774399360761329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24572420711182932907174219 36858631066774399360761329)
      ·
        refine ⟨27643973300080799520570997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36858631066774399360761329 27643973300080799520570997)
        ·
          refine ⟨2591622496882574955053531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27643973300080799520570997 2591622496882574955053531)
          ·
            refine ⟨3887433745323862432580297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591622496882574955053531 3887433745323862432580297)
            ·
              refine ⟨2915575308992896824435223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887433745323862432580297 2915575308992896824435223)
              ·
                refine ⟨4373362963489345236652835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915575308992896824435223 4373362963489345236652835)
                ·
                  refine ⟨6560044445234017854979253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373362963489345236652835 6560044445234017854979253)
                  ·
                    refine ⟨615004166740689173904305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6560044445234017854979253 615004166740689173904305)
                    ·
                      rfl

theorem cell23_3593149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_3593149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593149 prefixEnd_3593149 := by exact prefixLift 3593149
  have htrace : WordTrace (prefixWord ++ tailWord_3593149) baseStart_3593149 baseEnd_3593149 := by
    simpa [prefixWord, tailWord_3593149, baseEnd_3593149] using wordTrace_append hprefix tailTrace_3593149
  have hstable : (prefixWord ++ tailWord_3593149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593149).length < 2 ^ (prefixWord ++ tailWord_3593149).sum := by decide
  have hdescent : baseEnd_3593149 < baseStart_3593149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593152 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4]
def baseStart_3593152 : Nat := 118140960795 + 3593152 * 2 ^ 59
def prefixEnd_3593152 : Nat := 4983230072969 + 3 ^ 40 * 3593152 * 2
def baseEnd_3593152 : Nat := 1845014040664031009975401

theorem tailTrace_3593152 : CollatzResearch.WordTrace tailWord_3593152 prefixEnd_3593152 1845014040664031009975401 := by
  unfold tailWord_3593152
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526509939315720175310855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87368679919087626900414473 65526509939315720175310855)
  ·
    refine ⟨98289764908973580262966283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65526509939315720175310855 98289764908973580262966283)
    ·
      refine ⟨147434647363460370394449425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98289764908973580262966283 147434647363460370394449425)
      ·
        refine ⟨110575985522595277795837069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147434647363460370394449425 110575985522595277795837069)
        ·
          refine ⟨41465994570973229173438901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110575985522595277795837069 41465994570973229173438901)
          ·
            refine ⟨3887436991028740235009897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41465994570973229173438901 3887436991028740235009897)
            ·
              refine ⟨2915577743271555176257423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887436991028740235009897 2915577743271555176257423)
              ·
                refine ⟨4373366614907332764386135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915577743271555176257423 4373366614907332764386135)
                ·
                  refine ⟨6560049922360999146579203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373366614907332764386135 6560049922360999146579203)
                  ·
                    refine ⟨9840074883541498719868805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560049922360999146579203 9840074883541498719868805)
                    ·
                      refine ⟨1845014040664031009975401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9840074883541498719868805 1845014040664031009975401)
                      ·
                        rfl

theorem cell23_3593152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_3593152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593152 prefixEnd_3593152 := by exact prefixLift 3593152
  have htrace : WordTrace (prefixWord ++ tailWord_3593152) baseStart_3593152 baseEnd_3593152 := by
    simpa [prefixWord, tailWord_3593152, baseEnd_3593152] using wordTrace_append hprefix tailTrace_3593152
  have hstable : (prefixWord ++ tailWord_3593152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593152).length < 2 ^ (prefixWord ++ tailWord_3593152).sum := by decide
  have hdescent : baseEnd_3593152 < baseStart_3593152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593189 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3593189 : Nat := 118140960795 + 3593189 * 2 ^ 59
def prefixEnd_3593189 : Nat := 4983230072969 + 3 ^ 40 * 3593189 * 2
def baseEnd_3593189 : Nat := 1845033039448247365212731

theorem tailTrace_3593189 : CollatzResearch.WordTrace tailWord_3593189 prefixEnd_3593189 1845033039448247365212731 := by
  unfold tailWord_3593189
  simp only [CollatzResearch.WordTrace]
  refine ⟨131054369379497395669718621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87369579586331597113145747 131054369379497395669718621)
  ·
    refine ⟨49145388517311523376144483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131054369379497395669718621 49145388517311523376144483)
    ·
      refine ⟨73718082775967285064216725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49145388517311523376144483 73718082775967285064216725)
      ·
        refine ⟨3455535130123466487385159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73718082775967285064216725 3455535130123466487385159)
        ·
          refine ⟨5183302695185199731077739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455535130123466487385159 5183302695185199731077739)
          ·
            refine ⟨7774954042777799596616609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183302695185199731077739 7774954042777799596616609)
            ·
              refine ⟨5831215532083349697462457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774954042777799596616609 5831215532083349697462457)
              ·
                refine ⟨4373411649062512273096843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831215532083349697462457 4373411649062512273096843)
                ·
                  refine ⟨6560117473593768409645265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373411649062512273096843 6560117473593768409645265)
                  ·
                    refine ⟨4920088105195326307233949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560117473593768409645265 4920088105195326307233949)
                    ·
                      refine ⟨1845033039448247365212731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920088105195326307233949 1845033039448247365212731)
                      ·
                        rfl

theorem cell23_3593189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3593189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593189 prefixEnd_3593189 := by exact prefixLift 3593189
  have htrace : WordTrace (prefixWord ++ tailWord_3593189) baseStart_3593189 baseEnd_3593189 := by
    simpa [prefixWord, tailWord_3593189, baseEnd_3593189] using wordTrace_append hprefix tailTrace_3593189
  have hstable : (prefixWord ++ tailWord_3593189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593189).length < 2 ^ (prefixWord ++ tailWord_3593189).sum := by decide
  have hdescent : baseEnd_3593189 < baseStart_3593189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593212 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_3593212 : Nat := 118140960795 + 3593212 * 2 ^ 59
def prefixEnd_3593212 : Nat := 4983230072969 + 3 ^ 40 * 3593212 * 2
def baseEnd_3593212 : Nat := 1845044849503300775225125

theorem tailTrace_3593212 : CollatzResearch.WordTrace tailWord_3593212 prefixEnd_3593212 1845044849503300775225125 := by
  unfold tailWord_3593212
  simp only [CollatzResearch.WordTrace]
  refine ⟨65527604129207035298902945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87370138838942713731870593 65527604129207035298902945)
  ·
    refine ⟨49145703096905276474177209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65527604129207035298902945 49145703096905276474177209)
    ·
      refine ⟨36859277322678957355632907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49145703096905276474177209 36859277322678957355632907)
      ·
        refine ⟨55288915984018436033449361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36859277322678957355632907 55288915984018436033449361)
        ·
          refine ⟨41466686988013827025087021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55288915984018436033449361 41466686988013827025087021)
          ·
            refine ⟨15550007620505185134407633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41466686988013827025087021 15550007620505185134407633)
            ·
              refine ⟨11662505715378888850805725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15550007620505185134407633 11662505715378888850805725)
              ·
                refine ⟨4373439643267083319052147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11662505715378888850805725 4373439643267083319052147)
                ·
                  refine ⟨6560159464900624978578221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373439643267083319052147 6560159464900624978578221)
                  ·
                    refine ⟨2460059799337734366966833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6560159464900624978578221 2460059799337734366966833)
                    ·
                      refine ⟨1845044849503300775225125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460059799337734366966833 1845044849503300775225125)
                      ·
                        rfl

theorem cell23_3593212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_3593212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593212 prefixEnd_3593212 := by exact prefixLift 3593212
  have htrace : WordTrace (prefixWord ++ tailWord_3593212) baseStart_3593212 baseEnd_3593212 := by
    simpa [prefixWord, tailWord_3593212, baseEnd_3593212] using wordTrace_append hprefix tailTrace_3593212
  have hstable : (prefixWord ++ tailWord_3593212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593212).length < 2 ^ (prefixWord ++ tailWord_3593212).sum := by decide
  have hdescent : baseEnd_3593212 < baseStart_3593212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593231 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 13]
def baseStart_3593231 : Nat := 118140960795 + 3593231 * 2 ^ 59
def prefixEnd_3593231 : Nat := 4983230072969 + 3 ^ 40 * 3593231 * 2
def baseEnd_3593231 : Nat := 205006067292859577876393

theorem tailTrace_3593231 : CollatzResearch.WordTrace tailWord_3593231 prefixEnd_3593231 205006067292859577876393 := by
  unfold tailWord_3593231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131055901245345236842747547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87370600830230157895165031 131055901245345236842747547)
  ·
    refine ⟨196583851868017855264121321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131055901245345236842747547 196583851868017855264121321)
    ·
      refine ⟨147437888901013391448090991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196583851868017855264121321 147437888901013391448090991)
      ·
        refine ⟨221156833351520087172136487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147437888901013391448090991 221156833351520087172136487)
        ·
          refine ⟨331735250027280130758204731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221156833351520087172136487 331735250027280130758204731)
          ·
            refine ⟨497602875040920196137307097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331735250027280130758204731 497602875040920196137307097)
            ·
              refine ⟨373202156280690147102980323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497602875040920196137307097 373202156280690147102980323)
              ·
                refine ⟨559803234421035220654470485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373202156280690147102980323 559803234421035220654470485)
                ·
                  refine ⟨205006067292859577876393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 559803234421035220654470485 205006067292859577876393)
                  ·
                    rfl

theorem cell23_3593231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 13].length) (baseStart_3593231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593231 prefixEnd_3593231 := by exact prefixLift 3593231
  have htrace : WordTrace (prefixWord ++ tailWord_3593231) baseStart_3593231 baseEnd_3593231 := by
    simpa [prefixWord, tailWord_3593231, baseEnd_3593231] using wordTrace_append hprefix tailTrace_3593231
  have hstable : (prefixWord ++ tailWord_3593231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593231).length < 2 ^ (prefixWord ++ tailWord_3593231).sum := by decide
  have hdescent : baseEnd_3593231 < baseStart_3593231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593265 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 5]
def baseStart_3593265 : Nat := 118140960795 + 3593265 * 2 ^ 59
def prefixEnd_3593265 : Nat := 4983230072969 + 3 ^ 40 * 3593265 * 2
def baseEnd_3593265 : Nat := 205008007108665451984709

theorem tailTrace_3593265 : CollatzResearch.WordTrace tailWord_3593265 prefixEnd_3593265 205008007108665451984709 := by
  unfold tailWord_3593265
  simp only [CollatzResearch.WordTrace]
  refine ⟨131057141327222060649485249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87371427551481373766323499 131057141327222060649485249)
  ·
    refine ⟨98292855995416545487113937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131057141327222060649485249 98292855995416545487113937)
    ·
      refine ⟨73719641996562409115335453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98292855995416545487113937 73719641996562409115335453)
      ·
        refine ⟨27644865748710903418250795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73719641996562409115335453 27644865748710903418250795)
        ·
          refine ⟨41467298623066355127376193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27644865748710903418250795 41467298623066355127376193)
          ·
            refine ⟨31100473967299766345532145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41467298623066355127376193 31100473967299766345532145)
            ·
              refine ⟨23325355475474824759149109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31100473967299766345532145 23325355475474824759149109)
              ·
                refine ⟨2186752075825764821170229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23325355475474824759149109 2186752075825764821170229)
                ·
                  refine ⟨205008007108665451984709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186752075825764821170229 205008007108665451984709)
                  ·
                    rfl

theorem cell23_3593265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 5].length) (baseStart_3593265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593265 prefixEnd_3593265 := by exact prefixLift 3593265
  have htrace : WordTrace (prefixWord ++ tailWord_3593265) baseStart_3593265 baseEnd_3593265 := by
    simpa [prefixWord, tailWord_3593265, baseEnd_3593265] using wordTrace_append hprefix tailTrace_3593265
  have hstable : (prefixWord ++ tailWord_3593265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593265).length < 2 ^ (prefixWord ++ tailWord_3593265).sum := by decide
  have hdescent : baseEnd_3593265 < baseStart_3593265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593285 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_3593285 : Nat := 118140960795 + 3593285 * 2 ^ 59
def prefixEnd_3593285 : Nat := 4983230072969 + 3 ^ 40 * 3593285 * 2
def baseEnd_3593285 : Nat := 1845082333591078989612289

theorem tailTrace_3593285 : CollatzResearch.WordTrace tailWord_3593285 prefixEnd_3593285 1845082333591078989612289 := by
  unfold tailWord_3593285
  simp only [CollatzResearch.WordTrace]
  refine ⟨131057870787149604065213309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87371913858099736043475539 131057870787149604065213309)
  ·
    refine ⟨49146701545181101524454991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131057870787149604065213309 49146701545181101524454991)
    ·
      refine ⟨73720052317771652286682487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49146701545181101524454991 73720052317771652286682487)
      ·
        refine ⟨110580078476657478430023731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73720052317771652286682487 110580078476657478430023731)
        ·
          refine ⟨165870117714986217645035597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110580078476657478430023731 165870117714986217645035597)
          ·
            refine ⟨62201294143119831616888349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165870117714986217645035597 62201294143119831616888349)
            ·
              refine ⟨23325485303669936856333131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62201294143119831616888349 23325485303669936856333131)
              ·
                refine ⟨34988227955504905284499697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23325485303669936856333131 34988227955504905284499697)
                ·
                  refine ⟨26241170966628678963374773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34988227955504905284499697 26241170966628678963374773)
                  ·
                    refine ⟨2460109778121438652816385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26241170966628678963374773 2460109778121438652816385)
                    ·
                      refine ⟨1845082333591078989612289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460109778121438652816385 1845082333591078989612289)
                      ·
                        rfl

theorem cell23_3593285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_3593285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593285 prefixEnd_3593285 := by exact prefixLift 3593285
  have htrace : WordTrace (prefixWord ++ tailWord_3593285) baseStart_3593285 baseEnd_3593285 := by
    simpa [prefixWord, tailWord_3593285, baseEnd_3593285] using wordTrace_append hprefix tailTrace_3593285
  have hstable : (prefixWord ++ tailWord_3593285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593285).length < 2 ^ (prefixWord ++ tailWord_3593285).sum := by decide
  have hdescent : baseEnd_3593285 < baseStart_3593285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593288 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3593288 : Nat := 118140960795 + 3593288 * 2 ^ 59
def prefixEnd_3593288 : Nat := 4983230072969 + 3 ^ 40 * 3593288 * 2
def baseEnd_3593288 : Nat := 1845083874033042477874775

theorem tailTrace_3593288 : CollatzResearch.WordTrace tailWord_3593288 prefixEnd_3593288 1845083874033042477874775 := by
  unfold tailWord_3593288
  simp only [CollatzResearch.WordTrace]
  refine ⟨65528990103069367788786259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87371986804092490385048345 65528990103069367788786259)
  ·
    refine ⟨98293485154604051683179389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65528990103069367788786259 98293485154604051683179389)
    ·
      refine ⟨36860056932976519381192271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98293485154604051683179389 36860056932976519381192271)
      ·
        refine ⟨55290085399464779071788407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860056932976519381192271 55290085399464779071788407)
        ·
          refine ⟨82935128099197168607682611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55290085399464779071788407 82935128099197168607682611)
          ·
            refine ⟨124402692148795752911523917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82935128099197168607682611 124402692148795752911523917)
            ·
              refine ⟨46651009555798407341821469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124402692148795752911523917 46651009555798407341821469)
              ·
                refine ⟨17494128583424402753183051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46651009555798407341821469 17494128583424402753183051)
                ·
                  refine ⟨26241192875136604129774577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17494128583424402753183051 26241192875136604129774577)
                  ·
                    refine ⟨19680894656352453097330933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26241192875136604129774577 19680894656352453097330933)
                    ·
                      refine ⟨1845083874033042477874775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19680894656352453097330933 1845083874033042477874775)
                      ·
                        rfl

theorem cell23_3593288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3593288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593288 prefixEnd_3593288 := by exact prefixLift 3593288
  have htrace : WordTrace (prefixWord ++ tailWord_3593288) baseStart_3593288 baseEnd_3593288 := by
    simpa [prefixWord, tailWord_3593288, baseEnd_3593288] using wordTrace_append hprefix tailTrace_3593288
  have hstable : (prefixWord ++ tailWord_3593288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593288).length < 2 ^ (prefixWord ++ tailWord_3593288).sum := by decide
  have hdescent : baseEnd_3593288 < baseStart_3593288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593315 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3593315 : Nat := 118140960795 + 3593315 * 2 ^ 59
def prefixEnd_3593315 : Nat := 4983230072969 + 3 ^ 40 * 3593315 * 2
def baseEnd_3593315 : Nat := 1845097738010713872237151

theorem tailTrace_3593315 : CollatzResearch.WordTrace tailWord_3593315 prefixEnd_3593315 1845097738010713872237151 := by
  unfold tailWord_3593315
  simp only [CollatzResearch.WordTrace]
  refine ⟨131058964977040919188805399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87372643318027279459203599 131058964977040919188805399)
  ·
    refine ⟨196588447465561378783208099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131058964977040919188805399 196588447465561378783208099)
    ·
      refine ⟨294882671198342068174812149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196588447465561378783208099 294882671198342068174812149)
      ·
        refine ⟨27645250424844568891388639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294882671198342068174812149 27645250424844568891388639)
        ·
          refine ⟨41467875637266853337082959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27645250424844568891388639 41467875637266853337082959)
          ·
            refine ⟨62201813455900280005624439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41467875637266853337082959 62201813455900280005624439)
            ·
              refine ⟨93302720183850420008436659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62201813455900280005624439 93302720183850420008436659)
              ·
                refine ⟨139954080275775630012654989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93302720183850420008436659 139954080275775630012654989)
                ·
                  refine ⟨52482780103415861254745621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139954080275775630012654989 52482780103415861254745621)
                  ·
                    refine ⟨2460130317347618496316201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52482780103415861254745621 2460130317347618496316201)
                    ·
                      refine ⟨1845097738010713872237151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460130317347618496316201 1845097738010713872237151)
                      ·
                        rfl

theorem cell23_3593315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3593315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593315 prefixEnd_3593315 := by exact prefixLift 3593315
  have htrace : WordTrace (prefixWord ++ tailWord_3593315) baseStart_3593315 baseEnd_3593315 := by
    simpa [prefixWord, tailWord_3593315, baseEnd_3593315] using wordTrace_append hprefix tailTrace_3593315
  have hstable : (prefixWord ++ tailWord_3593315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593315).length < 2 ^ (prefixWord ++ tailWord_3593315).sum := by decide
  have hdescent : baseEnd_3593315 < baseStart_3593315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593328 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_3593328 : Nat := 118140960795 + 3593328 * 2 ^ 59
def prefixEnd_3593328 : Nat := 4983230072969 + 3 ^ 40 * 3593328 * 2
def baseEnd_3593328 : Nat := 1845104413259222321374591

theorem tailTrace_3593328 : CollatzResearch.WordTrace tailWord_3593328 prefixEnd_3593328 1845104413259222321374591 := by
  unfold tailWord_3593328
  simp only [CollatzResearch.WordTrace]
  refine ⟨65529719562996911204514319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87372959417329214939352425 65529719562996911204514319)
  ·
    refine ⟨98294579344495366806771479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65529719562996911204514319 98294579344495366806771479)
    ·
      refine ⟨147441869016743050210157219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98294579344495366806771479 147441869016743050210157219)
      ·
        refine ⟨221162803525114575315235829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147441869016743050210157219 221162803525114575315235829)
        ·
          refine ⟨20734012830479491435803359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221162803525114575315235829 20734012830479491435803359)
          ·
            refine ⟨31101019245719237153705039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20734012830479491435803359 31101019245719237153705039)
            ·
              refine ⟨46651528868578855730557559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31101019245719237153705039 46651528868578855730557559)
              ·
                refine ⟨69977293302868283595836339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46651528868578855730557559 69977293302868283595836339)
                ·
                  refine ⟨104965939954302425393754509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69977293302868283595836339 104965939954302425393754509)
                  ·
                    refine ⟨39362227482863409522657941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104965939954302425393754509 39362227482863409522657941)
                    ·
                      refine ⟨1845104413259222321374591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39362227482863409522657941 1845104413259222321374591)
                      ·
                        rfl

theorem cell23_3593328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_3593328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593328 prefixEnd_3593328 := by exact prefixLift 3593328
  have htrace : WordTrace (prefixWord ++ tailWord_3593328) baseStart_3593328 baseEnd_3593328 := by
    simpa [prefixWord, tailWord_3593328, baseEnd_3593328] using wordTrace_append hprefix tailTrace_3593328
  have hstable : (prefixWord ++ tailWord_3593328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593328).length < 2 ^ (prefixWord ++ tailWord_3593328).sum := by decide
  have hdescent : baseEnd_3593328 < baseStart_3593328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593335 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_3593335 : Nat := 118140960795 + 3593335 * 2 ^ 59
def prefixEnd_3593335 : Nat := 4983230072969 + 3 ^ 40 * 3593335 * 2
def baseEnd_3593335 : Nat := 1845108007623803793987059

theorem tailTrace_3593335 : CollatzResearch.WordTrace tailWord_3593335 prefixEnd_3593335 1845108007623803793987059 := by
  unfold tailWord_3593335
  simp only [CollatzResearch.WordTrace]
  refine ⟨131059694436968462604533459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87373129624645641736355639 131059694436968462604533459)
  ·
    refine ⟨196589541655452693906800189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131059694436968462604533459 196589541655452693906800189)
    ·
      refine ⟨73721078120794760215050071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196589541655452693906800189 73721078120794760215050071)
      ·
        refine ⟨110581617181192140322575107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73721078120794760215050071 110581617181192140322575107)
        ·
          refine ⟨165872425771788210483862661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110581617181192140322575107 165872425771788210483862661)
          ·
            refine ⟨31101079832210289465724249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165872425771788210483862661 31101079832210289465724249)
            ·
              refine ⟨23325809874157717099293187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31101079832210289465724249 23325809874157717099293187)
              ·
                refine ⟨34988714811236575648939781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23325809874157717099293187 34988714811236575648939781)
                ·
                  refine ⟨6560384027106857934176209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34988714811236575648939781 6560384027106857934176209)
                  ·
                    refine ⟨4920288020330143450632157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560384027106857934176209 4920288020330143450632157)
                    ·
                      refine ⟨1845108007623803793987059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920288020330143450632157 1845108007623803793987059)
                      ·
                        rfl

theorem cell23_3593335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_3593335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593335 prefixEnd_3593335 := by exact prefixLift 3593335
  have htrace : WordTrace (prefixWord ++ tailWord_3593335) baseStart_3593335 baseEnd_3593335 := by
    simpa [prefixWord, tailWord_3593335, baseEnd_3593335] using wordTrace_append hprefix tailTrace_3593335
  have hstable : (prefixWord ++ tailWord_3593335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593335).length < 2 ^ (prefixWord ++ tailWord_3593335).sum := by decide
  have hdescent : baseEnd_3593335 < baseStart_3593335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593392 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2]
def baseStart_3593392 : Nat := 118140960795 + 3593392 * 2 ^ 59
def prefixEnd_3593392 : Nat := 4983230072969 + 3 ^ 40 * 3593392 * 2
def baseEnd_3593392 : Nat := 1845137276021110070974297

theorem tailTrace_3593392 : CollatzResearch.WordTrace tailWord_3593392 prefixEnd_3593392 1845137276021110070974297 := by
  unfold tailWord_3593392
  simp only [CollatzResearch.WordTrace]
  refine ⟨65530886698880980669679215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87374515598507974226238953 65530886698880980669679215)
  ·
    refine ⟨98296330048321471004518823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65530886698880980669679215 98296330048321471004518823)
    ·
      refine ⟨147444495072482206506778235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98296330048321471004518823 147444495072482206506778235)
      ·
        refine ⟨221166742608723309760167353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147444495072482206506778235 221166742608723309760167353)
        ·
          refine ⟨165875056956542482320125515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221166742608723309760167353 165875056956542482320125515)
          ·
            refine ⟨248812585434813723480188273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165875056956542482320125515 248812585434813723480188273)
            ·
              refine ⟨186609439076110292610141205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248812585434813723480188273 186609439076110292610141205)
              ·
                refine ⟨8747317456692669966100369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186609439076110292610141205 8747317456692669966100369)
                ·
                  refine ⟨6560488092519502474575277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747317456692669966100369 6560488092519502474575277)
                  ·
                    refine ⟨2460183034694813427965729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6560488092519502474575277 2460183034694813427965729)
                    ·
                      refine ⟨1845137276021110070974297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460183034694813427965729 1845137276021110070974297)
                      ·
                        rfl

theorem cell23_3593392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2].length) (baseStart_3593392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593392 prefixEnd_3593392 := by exact prefixLift 3593392
  have htrace : WordTrace (prefixWord ++ tailWord_3593392) baseStart_3593392 baseEnd_3593392 := by
    simpa [prefixWord, tailWord_3593392, baseEnd_3593392] using wordTrace_append hprefix tailTrace_3593392
  have hstable : (prefixWord ++ tailWord_3593392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593392).length < 2 ^ (prefixWord ++ tailWord_3593392).sum := by decide
  have hdescent : baseEnd_3593392 < baseStart_3593392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593432 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_3593432 : Nat := 118140960795 + 3593432 * 2 ^ 59
def prefixEnd_3593432 : Nat := 4983230072969 + 3 ^ 40 * 3593432 * 2
def baseEnd_3593432 : Nat := 615052605082429971491371

theorem tailTrace_3593432 : CollatzResearch.WordTrace tailWord_3593432 prefixEnd_3593432 615052605082429971491371 := by
  unfold tailWord_3593432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65531616158808524085407275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87375488211744698780543033 65531616158808524085407275)
  ·
    refine ⟨98297424238212786128110913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65531616158808524085407275 98297424238212786128110913)
    ·
      refine ⟨73723068178659589596083185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98297424238212786128110913 73723068178659589596083185)
      ·
        refine ⟨55292301133994692197062389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73723068178659589596083185 55292301133994692197062389)
        ·
          refine ⟨5183653231312002393474599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55292301133994692197062389 5183653231312002393474599)
          ·
            refine ⟨7775479846968003590211899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183653231312002393474599 7775479846968003590211899)
            ·
              refine ⟨11663219770452005385317849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775479846968003590211899 11663219770452005385317849)
              ·
                refine ⟨8747414827839004038988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663219770452005385317849 8747414827839004038988387)
                ·
                  refine ⟨13121122241758506058482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747414827839004038988387 13121122241758506058482581)
                  ·
                    refine ⟨615052605082429971491371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13121122241758506058482581 615052605082429971491371)
                    ·
                      rfl

theorem cell23_3593432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_3593432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593432 prefixEnd_3593432 := by exact prefixLift 3593432
  have htrace : WordTrace (prefixWord ++ tailWord_3593432) baseStart_3593432 baseEnd_3593432 := by
    simpa [prefixWord, tailWord_3593432, baseEnd_3593432] using wordTrace_append hprefix tailTrace_3593432
  have hstable : (prefixWord ++ tailWord_3593432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593432).length < 2 ^ (prefixWord ++ tailWord_3593432).sum := by decide
  have hdescent : baseEnd_3593432 < baseStart_3593432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593445 : List Nat := [1, 3, 1, 4, 3, 11]
def baseStart_3593445 : Nat := 118140960795 + 3593445 * 2 ^ 59
def prefixEnd_3593445 : Nat := 4983230072969 + 3 ^ 40 * 3593445 * 2
def baseEnd_3593445 : Nat := 7593269508213161990171

theorem tailTrace_3593445 : CollatzResearch.WordTrace tailWord_3593445 prefixEnd_3593445 7593269508213161990171 := by
  unfold tailWord_3593445
  simp only [CollatzResearch.WordTrace]
  refine ⟨131063706466569951391037789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87375804311046634260691859 131063706466569951391037789)
  ·
    refine ⟨49148889924963731771639171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131063706466569951391037789 49148889924963731771639171)
    ·
      refine ⟨73723334887445597657458757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49148889924963731771639171 73723334887445597657458757)
      ·
        refine ⟨13823125291396049560773517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73723334887445597657458757 13823125291396049560773517)
        ·
          refine ⟨5183671984273518585290069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13823125291396049560773517 5183671984273518585290069)
          ·
            refine ⟨7593269508213161990171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5183671984273518585290069 7593269508213161990171)
            ·
              rfl

theorem cell23_3593445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 11].length) (baseStart_3593445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593445 prefixEnd_3593445 := by exact prefixLift 3593445
  have htrace : WordTrace (prefixWord ++ tailWord_3593445) baseStart_3593445 baseEnd_3593445 := by
    simpa [prefixWord, tailWord_3593445, baseEnd_3593445] using wordTrace_append hprefix tailTrace_3593445
  have hstable : (prefixWord ++ tailWord_3593445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593445).length < 2 ^ (prefixWord ++ tailWord_3593445).sum := by decide
  have hdescent : baseEnd_3593445 < baseStart_3593445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593472 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_3593472 : Nat := 118140960795 + 3593472 * 2 ^ 59
def prefixEnd_3593472 : Nat := 4983230072969 + 3 ^ 40 * 3593472 * 2
def baseEnd_3593472 : Nat := 1845178354473469757973929

theorem tailTrace_3593472 : CollatzResearch.WordTrace tailWord_3593472 prefixEnd_3593472 1845178354473469757973929 := by
  unfold tailWord_3593472
  simp only [CollatzResearch.WordTrace]
  refine ⟨65532345618736067501135335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87376460824981423334847113 65532345618736067501135335)
  ·
    refine ⟨98298518428104101251703003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65532345618736067501135335 98298518428104101251703003)
    ·
      refine ⟨147447777642156151877554505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98298518428104101251703003 147447777642156151877554505)
      ·
        refine ⟨110585833231617113908165879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147447777642156151877554505 110585833231617113908165879)
        ·
          refine ⟨165878749847425670862248819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110585833231617113908165879 165878749847425670862248819)
          ·
            refine ⟨248818124771138506293373229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165878749847425670862248819 248818124771138506293373229)
            ·
              refine ⟨93306796789176939860014961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248818124771138506293373229 93306796789176939860014961)
              ·
                refine ⟨69980097591882704895011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93306796789176939860014961 69980097591882704895011221)
                ·
                  refine ⟨3280317074619501791953651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69980097591882704895011221 3280317074619501791953651)
                  ·
                    refine ⟨4920475611929252687930477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3280317074619501791953651 4920475611929252687930477)
                    ·
                      refine ⟨1845178354473469757973929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920475611929252687930477 1845178354473469757973929)
                      ·
                        rfl

theorem cell23_3593472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_3593472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593472 prefixEnd_3593472 := by exact prefixLift 3593472
  have htrace : WordTrace (prefixWord ++ tailWord_3593472) baseStart_3593472 baseEnd_3593472 := by
    simpa [prefixWord, tailWord_3593472, baseEnd_3593472] using wordTrace_append hprefix tailTrace_3593472
  have hstable : (prefixWord ++ tailWord_3593472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593472).length < 2 ^ (prefixWord ++ tailWord_3593472).sum := by decide
  have hdescent : baseEnd_3593472 < baseStart_3593472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593490 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3593490 : Nat := 118140960795 + 3593490 * 2 ^ 59
def prefixEnd_3593490 : Nat := 4983230072969 + 3 ^ 40 * 3593490 * 2
def baseEnd_3593490 : Nat := 1845187597125250687548847

theorem tailTrace_3593490 : CollatzResearch.WordTrace tailWord_3593490 prefixEnd_3593490 1845187597125250687548847 := by
  unfold tailWord_3593490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766336937851731019106481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87376898500937949384283949 32766336937851731019106481)
  ·
    refine ⟨24574752703388798264329861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32766336937851731019106481 24574752703388798264329861)
    ·
      refine ⟨4607766131885399674561849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24574752703388798264329861 4607766131885399674561849)
      ·
        refine ⟨3455824598914049755921387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4607766131885399674561849 3455824598914049755921387)
        ·
          refine ⟨5183736898371074633882081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455824598914049755921387 5183736898371074633882081)
          ·
            refine ⟨3887802673778305975411561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5183736898371074633882081 3887802673778305975411561)
            ·
              refine ⟨2915852005333729481558671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887802673778305975411561 2915852005333729481558671)
              ·
                refine ⟨4373778008000594222338007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915852005333729481558671 4373778008000594222338007)
                ·
                  refine ⟨6560667012000891333507011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373778008000594222338007 6560667012000891333507011)
                  ·
                    refine ⟨9841000518001337000260517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560667012000891333507011 9841000518001337000260517)
                    ·
                      refine ⟨1845187597125250687548847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9841000518001337000260517 1845187597125250687548847)
                      ·
                        rfl

theorem cell23_3593490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3593490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593490 prefixEnd_3593490 := by exact prefixLift 3593490
  have htrace : WordTrace (prefixWord ++ tailWord_3593490) baseStart_3593490 baseEnd_3593490 := by
    simpa [prefixWord, tailWord_3593490, baseEnd_3593490] using wordTrace_append hprefix tailTrace_3593490
  have hstable : (prefixWord ++ tailWord_3593490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593490).length < 2 ^ (prefixWord ++ tailWord_3593490).sum := by decide
  have hdescent : baseEnd_3593490 < baseStart_3593490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593506 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3593506 : Nat := 118140960795 + 3593506 * 2 ^ 59
def prefixEnd_3593506 : Nat := 4983230072969 + 3 ^ 40 * 3593506 * 2
def baseEnd_3593506 : Nat := 1845195812815722624948773

theorem tailTrace_3593506 : CollatzResearch.WordTrace tailWord_3593506 prefixEnd_3593506 1845195812815722624948773 := by
  unfold tailWord_3593506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766482829837239702252093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87377287546232639206005581 32766482829837239702252093)
  ·
    refine ⟨12287431061188964888344535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32766482829837239702252093 12287431061188964888344535)
    ·
      refine ⟨18431146591783447332516803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12287431061188964888344535 18431146591783447332516803)
      ·
        refine ⟨27646719887675170998775205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18431146591783447332516803 27646719887675170998775205)
        ·
          refine ⟨5183759978939094562270351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27646719887675170998775205 5183759978939094562270351)
          ·
            refine ⟨7775639968408641843405527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183759978939094562270351 7775639968408641843405527)
            ·
              refine ⟨11663459952612962765108291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775639968408641843405527 11663459952612962765108291)
              ·
                refine ⟨17495189928919444147662437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663459952612962765108291 17495189928919444147662437)
                ·
                  refine ⟨3280348111672395777686707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17495189928919444147662437 3280348111672395777686707)
                  ·
                    refine ⟨4920522167508593666530061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3280348111672395777686707 4920522167508593666530061)
                    ·
                      refine ⟨1845195812815722624948773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920522167508593666530061 1845195812815722624948773)
                      ·
                        rfl

theorem cell23_3593506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3593506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593506 prefixEnd_3593506 := by exact prefixLift 3593506
  have htrace : WordTrace (prefixWord ++ tailWord_3593506) baseStart_3593506 baseEnd_3593506 := by
    simpa [prefixWord, tailWord_3593506, baseEnd_3593506] using wordTrace_append hprefix tailTrace_3593506
  have hstable : (prefixWord ++ tailWord_3593506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593506).length < 2 ^ (prefixWord ++ tailWord_3593506).sum := by decide
  have hdescent : baseEnd_3593506 < baseStart_3593506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593522 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3593522 : Nat := 118140960795 + 3593522 * 2 ^ 59
def prefixEnd_3593522 : Nat := 4983230072969 + 3 ^ 40 * 3593522 * 2
def baseEnd_3593522 : Nat := 615068009502064854116233

theorem tailTrace_3593522 : CollatzResearch.WordTrace tailWord_3593522 prefixEnd_3593522 615068009502064854116233 := by
  unfold tailWord_3593522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766628721822748385397705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87377676591527329027727213 32766628721822748385397705)
  ·
    refine ⟨24574971541367061289048279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32766628721822748385397705 24574971541367061289048279)
    ·
      refine ⟨36862457312050591933572419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24574971541367061289048279 36862457312050591933572419)
      ·
        refine ⟨55293685968075887900358629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36862457312050591933572419 55293685968075887900358629)
        ·
          refine ⟨10367566119014228981317243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55293685968075887900358629 10367566119014228981317243)
          ·
            refine ⟨15551349178521343471975865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367566119014228981317243 15551349178521343471975865)
            ·
              refine ⟨11663511883891007603981899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15551349178521343471975865 11663511883891007603981899)
              ·
                refine ⟨17495267825836511405972849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663511883891007603981899 17495267825836511405972849)
                ·
                  refine ⟨13121450869377383554479637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17495267825836511405972849 13121450869377383554479637)
                  ·
                    refine ⟨615068009502064854116233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13121450869377383554479637 615068009502064854116233)
                    ·
                      rfl

theorem cell23_3593522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3593522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593522 prefixEnd_3593522 := by exact prefixLift 3593522
  have htrace : WordTrace (prefixWord ++ tailWord_3593522) baseStart_3593522 baseEnd_3593522 := by
    simpa [prefixWord, tailWord_3593522, baseEnd_3593522] using wordTrace_append hprefix tailTrace_3593522
  have hstable : (prefixWord ++ tailWord_3593522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593522).length < 2 ^ (prefixWord ++ tailWord_3593522).sum := by decide
  have hdescent : baseEnd_3593522 < baseStart_3593522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593562 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_3593562 : Nat := 118140960795 + 3593562 * 2 ^ 59
def prefixEnd_3593562 : Nat := 4983230072969 + 3 ^ 40 * 3593562 * 2
def baseEnd_3593562 : Nat := 1845224567732374405848515

theorem tailTrace_3593562 : CollatzResearch.WordTrace tailWord_3593562 prefixEnd_3593562 1845224567732374405848515 := by
  unfold tailWord_3593562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766993451786520093261735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87378649204764053582031293 32766993451786520093261735)
  ·
    refine ⟨49150490177679780139892603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32766993451786520093261735 49150490177679780139892603)
    ·
      refine ⟨73725735266519670209838905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49150490177679780139892603 73725735266519670209838905)
      ·
        refine ⟨55294301449889752657379179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73725735266519670209838905 55294301449889752657379179)
        ·
          refine ⟨82941452174834628986068769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55294301449889752657379179 82941452174834628986068769)
          ·
            refine ⟨62206089131125971739551577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82941452174834628986068769 62206089131125971739551577)
            ·
              refine ⟨46654566848344478804663683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62206089131125971739551577 46654566848344478804663683)
              ·
                refine ⟨69981850272516718206995525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46654566848344478804663683 69981850272516718206995525)
                ·
                  refine ⟨13121596926096884663811661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69981850272516718206995525 13121596926096884663811661)
                  ·
                    refine ⟨4920598847286331748929373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13121596926096884663811661 4920598847286331748929373)
                    ·
                      refine ⟨1845224567732374405848515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920598847286331748929373 1845224567732374405848515)
                      ·
                        rfl

theorem cell23_3593562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_3593562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593562 prefixEnd_3593562 := by exact prefixLift 3593562
  have htrace : WordTrace (prefixWord ++ tailWord_3593562) baseStart_3593562 baseEnd_3593562 := by
    simpa [prefixWord, tailWord_3593562, baseEnd_3593562] using wordTrace_append hprefix tailTrace_3593562
  have hstable : (prefixWord ++ tailWord_3593562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593562).length < 2 ^ (prefixWord ++ tailWord_3593562).sum := by decide
  have hdescent : baseEnd_3593562 < baseStart_3593562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593580 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_3593580 : Nat := 118140960795 + 3593580 * 2 ^ 59
def prefixEnd_3593580 : Nat := 4983230072969 + 3 ^ 40 * 3593580 * 2
def baseEnd_3593580 : Nat := 1845233810384155335423433

theorem tailTrace_3593580 : CollatzResearch.WordTrace tailWord_3593580 prefixEnd_3593580 1845233810384155335423433 := by
  unfold tailWord_3593580
  simp only [CollatzResearch.WordTrace]
  refine ⟨65534315160540434723601097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87379086880720579631468129 65534315160540434723601097)
  ·
    refine ⟨49150736370405326042700823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65534315160540434723601097 49150736370405326042700823)
    ·
      refine ⟨73726104555607989064051235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49150736370405326042700823 73726104555607989064051235)
      ·
        refine ⟨110589156833411983596076853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73726104555607989064051235 110589156833411983596076853)
        ·
          refine ⟨10367733453132373462132205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110589156833411983596076853 10367733453132373462132205)
          ·
            refine ⟨3887900044924640048299577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10367733453132373462132205 3887900044924640048299577)
            ·
              refine ⟨2915925033693480036224683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887900044924640048299577 2915925033693480036224683)
              ·
                refine ⟨4373887550540220054337025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915925033693480036224683 4373887550540220054337025)
                ·
                  refine ⟨3280415662905165040752769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373887550540220054337025 3280415662905165040752769)
                  ·
                    refine ⟨2460311747178873780564577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3280415662905165040752769 2460311747178873780564577)
                    ·
                      refine ⟨1845233810384155335423433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460311747178873780564577 1845233810384155335423433)
                      ·
                        rfl

theorem cell23_3593580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_3593580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593580 prefixEnd_3593580 := by exact prefixLift 3593580
  have htrace : WordTrace (prefixWord ++ tailWord_3593580) baseStart_3593580 baseEnd_3593580 := by
    simpa [prefixWord, tailWord_3593580, baseEnd_3593580] using wordTrace_append hprefix tailTrace_3593580
  have hstable : (prefixWord ++ tailWord_3593580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593580).length < 2 ^ (prefixWord ++ tailWord_3593580).sum := by decide
  have hdescent : baseEnd_3593580 < baseStart_3593580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593639 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3593639 : Nat := 118140960795 + 3593639 * 2 ^ 59
def prefixEnd_3593639 : Nat := 4983230072969 + 3 ^ 40 * 3593639 * 2
def baseEnd_3593639 : Nat := 1845264105742770604585661

theorem tailTrace_3593639 : CollatzResearch.WordTrace tailWord_3593639 prefixEnd_3593639 1845264105742770604585661 := by
  unfold tailWord_3593639
  simp only [CollatzResearch.WordTrace]
  refine ⟨131070782227867122523599971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87380521485244748349066647 131070782227867122523599971)
  ·
    refine ⟨196606173341800683785399957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131070782227867122523599971 196606173341800683785399957)
    ·
      refine ⟨9215914375396907052440623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196606173341800683785399957 9215914375396907052440623)
      ·
        refine ⟨13823871563095360578660935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9215914375396907052440623 13823871563095360578660935)
        ·
          refine ⟨20735807344643040867991403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13823871563095360578660935 20735807344643040867991403)
          ·
            refine ⟨31103711016964561301987105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20735807344643040867991403 31103711016964561301987105)
            ·
              refine ⟨23327783262723420976490329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31103711016964561301987105 23327783262723420976490329)
              ·
                refine ⟨17495837447042565732367747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23327783262723420976490329 17495837447042565732367747)
                ·
                  refine ⟨26243756170563848598551621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17495837447042565732367747 26243756170563848598551621)
                  ·
                    refine ⟨4920704281980721612228429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26243756170563848598551621 4920704281980721612228429)
                    ·
                      refine ⟨1845264105742770604585661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920704281980721612228429 1845264105742770604585661)
                      ·
                        rfl

theorem cell23_3593639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3593639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593639 prefixEnd_3593639 := by exact prefixLift 3593639
  have htrace : WordTrace (prefixWord ++ tailWord_3593639) baseStart_3593639 baseEnd_3593639 := by
    simpa [prefixWord, tailWord_3593639, baseEnd_3593639] using wordTrace_append hprefix tailTrace_3593639
  have hstable : (prefixWord ++ tailWord_3593639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593639).length < 2 ^ (prefixWord ++ tailWord_3593639).sum := by decide
  have hdescent : baseEnd_3593639 < baseStart_3593639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593676 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 6]
def baseStart_3593676 : Nat := 118140960795 + 3593676 * 2 ^ 59
def prefixEnd_3593676 : Nat := 4983230072969 + 3 ^ 40 * 3593676 * 2
def baseEnd_3593676 : Nat := 205031456058554106646999

theorem tailTrace_3593676 : CollatzResearch.WordTrace tailWord_3593676 prefixEnd_3593676 205031456058554106646999 := by
  unfold tailWord_3593676
  simp only [CollatzResearch.WordTrace]
  refine ⟨65536065864366538921348441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87381421152488718561797921 65536065864366538921348441)
  ·
    refine ⟨49152049398274904191011331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65536065864366538921348441 49152049398274904191011331)
    ·
      refine ⟨73728074097412356286516997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49152049398274904191011331 73728074097412356286516997)
      ·
        refine ⟨13824013893264816803721937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73728074097412356286516997 13824013893264816803721937)
        ·
          refine ⟨10368010419948612602791453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13824013893264816803721937 10368010419948612602791453)
          ·
            refine ⟨3888003907480729726046795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10368010419948612602791453 3888003907480729726046795)
            ·
              refine ⟨5832005861221094589070193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888003907480729726046795 5832005861221094589070193)
              ·
                refine ⟨4374004395915820941802645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5832005861221094589070193 4374004395915820941802645)
                ·
                  refine ⟨205031456058554106646999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4374004395915820941802645 205031456058554106646999)
                  ·
                    rfl

theorem cell23_3593676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_3593676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593676 prefixEnd_3593676 := by exact prefixLift 3593676
  have htrace : WordTrace (prefixWord ++ tailWord_3593676) baseStart_3593676 baseEnd_3593676 := by
    simpa [prefixWord, tailWord_3593676, baseEnd_3593676] using wordTrace_append hprefix tailTrace_3593676
  have hstable : (prefixWord ++ tailWord_3593676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593676).length < 2 ^ (prefixWord ++ tailWord_3593676).sum := by decide
  have hdescent : baseEnd_3593676 < baseStart_3593676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593720 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_3593720 : Nat := 118140960795 + 3593720 * 2 ^ 59
def prefixEnd_3593720 : Nat := 4983230072969 + 3 ^ 40 * 3593720 * 2
def baseEnd_3593720 : Nat := 1845305697675784787672789

theorem tailTrace_3593720 : CollatzResearch.WordTrace tailWord_3593720 prefixEnd_3593720 1845305697675784787672789 := by
  unfold tailWord_3593720
  simp only [CollatzResearch.WordTrace]
  refine ⟨65536868270286836678649307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87382491027049115571532409 65536868270286836678649307)
  ·
    refine ⟨98305302405430255017973961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65536868270286836678649307 98305302405430255017973961)
    ·
      refine ⟨73728976804072691263480471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98305302405430255017973961 73728976804072691263480471)
      ·
        refine ⟨110593465206109036895220707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73728976804072691263480471 110593465206109036895220707)
        ·
          refine ⟨165890197809163555342831061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110593465206109036895220707 165890197809163555342831061)
          ·
            refine ⟨3888051511152270828347603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165890197809163555342831061 3888051511152270828347603)
            ·
              refine ⟨5832077266728406242521405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888051511152270828347603 5832077266728406242521405)
              ·
                refine ⟨2187028975023152340945527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5832077266728406242521405 2187028975023152340945527)
                ·
                  refine ⟨3280543462534728511418291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187028975023152340945527 3280543462534728511418291)
                  ·
                    refine ⟨4920815193802092767127437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3280543462534728511418291 4920815193802092767127437)
                    ·
                      refine ⟨1845305697675784787672789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4920815193802092767127437 1845305697675784787672789)
                      ·
                        rfl

theorem cell23_3593720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_3593720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593720 prefixEnd_3593720 := by exact prefixLift 3593720
  have htrace : WordTrace (prefixWord ++ tailWord_3593720) baseStart_3593720 baseEnd_3593720 := by
    simpa [prefixWord, tailWord_3593720, baseEnd_3593720] using wordTrace_append hprefix tailTrace_3593720
  have hstable : (prefixWord ++ tailWord_3593720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593720).length < 2 ^ (prefixWord ++ tailWord_3593720).sum := by decide
  have hdescent : baseEnd_3593720 < baseStart_3593720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593730 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3593730 : Nat := 118140960795 + 3593730 * 2 ^ 59
def prefixEnd_3593730 : Nat := 4983230072969 + 3 ^ 40 * 3593730 * 2
def baseEnd_3593730 : Nat := 1845310832482329748547743

theorem tailTrace_3593730 : CollatzResearch.WordTrace tailWord_3593730 prefixEnd_3593730 1845310832482329748547743 := by
  unfold tailWord_3593730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32768525317634361266290661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87382734180358296710108429 32768525317634361266290661)
  ·
    refine ⟨6144098497056442737429499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32768525317634361266290661 6144098497056442737429499)
    ·
      refine ⟨9216147745584664106144249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144098497056442737429499 9216147745584664106144249)
      ·
        refine ⟨6912110809188498079608187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9216147745584664106144249 6912110809188498079608187)
        ·
          refine ⟨10368166213782747119412281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912110809188498079608187 10368166213782747119412281)
          ·
            refine ⟨7776124660337060339559211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10368166213782747119412281 7776124660337060339559211)
            ·
              refine ⟨11664186990505590509338817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776124660337060339559211 11664186990505590509338817)
              ·
                refine ⟨8748140242879192882004113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11664186990505590509338817 8748140242879192882004113)
                ·
                  refine ⟨6561105182159394661503085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748140242879192882004113 6561105182159394661503085)
                  ·
                    refine ⟨2460414443309772998063657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6561105182159394661503085 2460414443309772998063657)
                    ·
                      refine ⟨1845310832482329748547743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460414443309772998063657 1845310832482329748547743)
                      ·
                        rfl

theorem cell23_3593730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3593730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593730 prefixEnd_3593730 := by exact prefixLift 3593730
  have htrace : WordTrace (prefixWord ++ tailWord_3593730) baseStart_3593730 baseEnd_3593730 := by
    simpa [prefixWord, tailWord_3593730, baseEnd_3593730] using wordTrace_append hprefix tailTrace_3593730
  have hstable : (prefixWord ++ tailWord_3593730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593730).length < 2 ^ (prefixWord ++ tailWord_3593730).sum := by decide
  have hdescent : baseEnd_3593730 < baseStart_3593730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593749 : List Nat := [1, 3, 2, 1, 3, 3, 2, 8]
def baseStart_3593749 : Nat := 118140960795 + 3593749 * 2 ^ 59
def prefixEnd_3593749 : Nat := 4983230072969 + 3 ^ 40 * 3593749 * 2
def baseEnd_3593749 : Nat := 68345206985732043489265

theorem tailTrace_3593749 : CollatzResearch.WordTrace tailWord_3593749 prefixEnd_3593749 68345206985732043489265 := by
  unfold tailWord_3593749
  simp only [CollatzResearch.WordTrace]
  refine ⟨131074794257468611310104301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87383196171645740873402867 131074794257468611310104301)
  ·
    refine ⟨49153047846550729241289113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131074794257468611310104301 49153047846550729241289113)
    ·
      refine ⟨36864785884913046930966835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49153047846550729241289113 36864785884913046930966835)
      ·
        refine ⟨55297178827369570396450253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36864785884913046930966835 55297178827369570396450253)
        ·
          refine ⟨20736442060263588898668845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55297178827369570396450253 20736442060263588898668845)
          ·
            refine ⟨7776165772598845837000817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20736442060263588898668845 7776165772598845837000817)
            ·
              refine ⟨5832124329449134377750613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7776165772598845837000817 5832124329449134377750613)
              ·
                refine ⟨68345206985732043489265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5832124329449134377750613 68345206985732043489265)
                ·
                  rfl

theorem cell23_3593749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 8].length) (baseStart_3593749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593749 prefixEnd_3593749 := by exact prefixLift 3593749
  have htrace : WordTrace (prefixWord ++ tailWord_3593749) baseStart_3593749 baseEnd_3593749 := by
    simpa [prefixWord, tailWord_3593749, baseEnd_3593749] using wordTrace_append hprefix tailTrace_3593749
  have hstable : (prefixWord ++ tailWord_3593749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593749).length < 2 ^ (prefixWord ++ tailWord_3593749).sum := by decide
  have hdescent : baseEnd_3593749 < baseStart_3593749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593809 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3593809 : Nat := 118140960795 + 3593809 * 2 ^ 59
def prefixEnd_3593809 : Nat := 4983230072969 + 3 ^ 40 * 3593809 * 2
def baseEnd_3593809 : Nat := 615117132484678313153293

theorem tailTrace_3593809 : CollatzResearch.WordTrace tailWord_3593809 prefixEnd_3593809 615117132484678313153293 := by
  unfold tailWord_3593809
  simp only [CollatzResearch.WordTrace]
  refine ⟨131076982637251241557288481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87384655091500827704858987 131076982637251241557288481)
  ·
    refine ⟨98307736977938431167966361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131076982637251241557288481 98307736977938431167966361)
    ·
      refine ⟨73730802733453823375974771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98307736977938431167966361 73730802733453823375974771)
      ·
        refine ⟨110596204100180735063962157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73730802733453823375974771 110596204100180735063962157)
        ·
          refine ⟨41473576537567775648985809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110596204100180735063962157 41473576537567775648985809)
          ·
            refine ⟨31105182403175831736739357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41473576537567775648985809 31105182403175831736739357)
            ·
              refine ⟨11664443401190936901277259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31105182403175831736739357 11664443401190936901277259)
              ·
                refine ⟨17496665101786405351915889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11664443401190936901277259 17496665101786405351915889)
                ·
                  refine ⟨13122498826339804013936917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17496665101786405351915889 13122498826339804013936917)
                  ·
                    refine ⟨615117132484678313153293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13122498826339804013936917 615117132484678313153293)
                    ·
                      rfl

theorem cell23_3593809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3593809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593809 prefixEnd_3593809 := by exact prefixLift 3593809
  have htrace : WordTrace (prefixWord ++ tailWord_3593809) baseStart_3593809 baseEnd_3593809 := by
    simpa [prefixWord, tailWord_3593809, baseEnd_3593809] using wordTrace_append hprefix tailTrace_3593809
  have hstable : (prefixWord ++ tailWord_3593809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593809).length < 2 ^ (prefixWord ++ tailWord_3593809).sum := by decide
  have hdescent : baseEnd_3593809 < baseStart_3593809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593856 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 5]
def baseStart_3593856 : Nat := 118140960795 + 3593856 * 2 ^ 59
def prefixEnd_3593856 : Nat := 4983230072969 + 3 ^ 40 * 3593856 * 2
def baseEnd_3593856 : Nat := 205041725671644028396907

theorem tailTrace_3593856 : CollatzResearch.WordTrace tailWord_3593856 prefixEnd_3593856 205041725671644028396907 := by
  unfold tailWord_3593856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65539348434040484292124711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87385797912053979056166281 65539348434040484292124711)
  ·
    refine ⟨98309022651060726438187067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65539348434040484292124711 98309022651060726438187067)
    ·
      refine ⟨147463533976591089657280601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98309022651060726438187067 147463533976591089657280601)
      ·
        refine ⟨110597650482443317242960451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147463533976591089657280601 110597650482443317242960451)
        ·
          refine ⟨165896475723664975864440677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110597650482443317242960451 165896475723664975864440677)
          ·
            refine ⟨31105589198187182974582627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165896475723664975864440677 31105589198187182974582627)
            ·
              refine ⟨46658383797280774461873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31105589198187182974582627 46658383797280774461873941)
              ·
                refine ⟨2187111740497536302900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46658383797280774461873941 2187111740497536302900341)
                ·
                  refine ⟨205041725671644028396907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187111740497536302900341 205041725671644028396907)
                  ·
                    rfl

theorem cell23_3593856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 5].length) (baseStart_3593856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593856 prefixEnd_3593856 := by exact prefixLift 3593856
  have htrace : WordTrace (prefixWord ++ tailWord_3593856) baseStart_3593856 baseEnd_3593856 := by
    simpa [prefixWord, tailWord_3593856, baseEnd_3593856] using wordTrace_append hprefix tailTrace_3593856
  have hstable : (prefixWord ++ tailWord_3593856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593856).length < 2 ^ (prefixWord ++ tailWord_3593856).sum := by decide
  have hdescent : baseEnd_3593856 < baseStart_3593856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593906 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3593906 : Nat := 118140960795 + 3593906 * 2 ^ 59
def prefixEnd_3593906 : Nat := 4983230072969 + 3 ^ 40 * 3593906 * 2
def baseEnd_3593906 : Nat := 1845401205077521059946933

theorem tailTrace_3593906 : CollatzResearch.WordTrace tailWord_3593906 prefixEnd_3593906 1845401205077521059946933 := by
  unfold tailWord_3593906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32770130129474956780892393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87387013678599884749046381 32770130129474956780892393)
  ·
    refine ⟨24577597597106217585669295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32770130129474956780892393 24577597597106217585669295)
    ·
      refine ⟨36866396395659326378503943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24577597597106217585669295 36866396395659326378503943)
      ·
        refine ⟨55299594593488989567755915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36866396395659326378503943 55299594593488989567755915)
        ·
          refine ⟨82949391890233484351633873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55299594593488989567755915 82949391890233484351633873)
          ·
            refine ⟨62212043917675113263725405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82949391890233484351633873 62212043917675113263725405)
            ·
              refine ⟨23329516469128167473897027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62212043917675113263725405 23329516469128167473897027)
              ·
                refine ⟨34994274703692251210845541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23329516469128167473897027 34994274703692251210845541)
                ·
                  refine ⟨6561426506942297102033539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34994274703692251210845541 6561426506942297102033539)
                  ·
                    refine ⟨9842139760413445653050309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561426506942297102033539 9842139760413445653050309)
                    ·
                      refine ⟨1845401205077521059946933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9842139760413445653050309 1845401205077521059946933)
                      ·
                        rfl

theorem cell23_3593906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3593906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593906 prefixEnd_3593906 := by exact prefixLift 3593906
  have htrace : WordTrace (prefixWord ++ tailWord_3593906) baseStart_3593906 baseEnd_3593906 := by
    simpa [prefixWord, tailWord_3593906, baseEnd_3593906] using wordTrace_append hprefix tailTrace_3593906
  have hstable : (prefixWord ++ tailWord_3593906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593906).length < 2 ^ (prefixWord ++ tailWord_3593906).sum := by decide
  have hdescent : baseEnd_3593906 < baseStart_3593906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593940 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3593940 : Nat := 118140960795 + 3593940 * 2 ^ 59
def prefixEnd_3593940 : Nat := 4983230072969 + 3 ^ 40 * 3593940 * 2
def baseEnd_3593940 : Nat := 1845418663419773926921777

theorem tailTrace_3593940 : CollatzResearch.WordTrace tailWord_3593940 prefixEnd_3593940 1845418663419773926921777 := by
  unfold tailWord_3593940
  simp only [CollatzResearch.WordTrace]
  refine ⟨65540880299888325465153637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87387840399851100620204849 65540880299888325465153637)
  ·
    refine ⟨12288915056229061024716307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65540880299888325465153637 12288915056229061024716307)
    ·
      refine ⟨18433372584343591537074461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288915056229061024716307 18433372584343591537074461)
      ·
        refine ⟨6912514719128846826402923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18433372584343591537074461 6912514719128846826402923)
        ·
          refine ⟨10368772078693270239604385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912514719128846826402923 10368772078693270239604385)
          ·
            refine ⟨7776579059019952679703289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10368772078693270239604385 7776579059019952679703289)
            ·
              refine ⟨5832434294264964509777467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7776579059019952679703289 5832434294264964509777467)
              ·
                refine ⟨8748651441397446764666201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832434294264964509777467 8748651441397446764666201)
                ·
                  refine ⟨6561488581048085073499651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748651441397446764666201 6561488581048085073499651)
                  ·
                    refine ⟨9842232871572127610249477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6561488581048085073499651 9842232871572127610249477)
                    ·
                      refine ⟨1845418663419773926921777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9842232871572127610249477 1845418663419773926921777)
                      ·
                        rfl

theorem cell23_3593940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3593940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593940 prefixEnd_3593940 := by exact prefixLift 3593940
  have htrace : WordTrace (prefixWord ++ tailWord_3593940) baseStart_3593940 baseEnd_3593940 := by
    simpa [prefixWord, tailWord_3593940, baseEnd_3593940] using wordTrace_append hprefix tailTrace_3593940
  have hstable : (prefixWord ++ tailWord_3593940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593940).length < 2 ^ (prefixWord ++ tailWord_3593940).sum := by decide
  have hdescent : baseEnd_3593940 < baseStart_3593940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593943 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_3593943 : Nat := 118140960795 + 3593943 * 2 ^ 59
def prefixEnd_3593943 : Nat := 4983230072969 + 3 ^ 40 * 3593943 * 2
def baseEnd_3593943 : Nat := 1845420203861737415184263

theorem tailTrace_3593943 : CollatzResearch.WordTrace tailWord_3593943 prefixEnd_3593943 1845420203861737415184263 := by
  unfold tailWord_3593943
  simp only [CollatzResearch.WordTrace]
  refine ⟨131081870018765782442666483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87387913345843854961777655 131081870018765782442666483)
  ·
    refine ⟨196622805028148673663999725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131081870018765782442666483 196622805028148673663999725)
    ·
      refine ⟨73733551885555752623999897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196622805028148673663999725 73733551885555752623999897)
      ·
        refine ⟨55300163914166814467999923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73733551885555752623999897 55300163914166814467999923)
        ·
          refine ⟨82950245871250221701999885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55300163914166814467999923 82950245871250221701999885)
          ·
            refine ⟨31106342201718833138249957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82950245871250221701999885 31106342201718833138249957)
            ·
              refine ⟨5832439162822281213421867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31106342201718833138249957 5832439162822281213421867)
              ·
                refine ⟨8748658744233421820132801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832439162822281213421867 8748658744233421820132801)
                ·
                  refine ⟨6561494058175066365099601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748658744233421820132801 6561494058175066365099601)
                  ·
                    refine ⟨4921120543631299773824701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6561494058175066365099601 4921120543631299773824701)
                    ·
                      refine ⟨1845420203861737415184263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921120543631299773824701 1845420203861737415184263)
                      ·
                        rfl

theorem cell23_3593943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_3593943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593943 prefixEnd_3593943 := by exact prefixLift 3593943
  have htrace : WordTrace (prefixWord ++ tailWord_3593943) baseStart_3593943 baseEnd_3593943 := by
    simpa [prefixWord, tailWord_3593943, baseEnd_3593943] using wordTrace_append hprefix tailTrace_3593943
  have hstable : (prefixWord ++ tailWord_3593943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593943).length < 2 ^ (prefixWord ++ tailWord_3593943).sum := by decide
  have hdescent : baseEnd_3593943 < baseStart_3593943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593966 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3593966 : Nat := 118140960795 + 3593966 * 2 ^ 59
def prefixEnd_3593966 : Nat := 4983230072969 + 3 ^ 40 * 3593966 * 2
def baseEnd_3593966 : Nat := 1845432013916790825196657

theorem tailTrace_3593966 : CollatzResearch.WordTrace tailWord_3593966 prefixEnd_3593966 1845432013916790825196657 := by
  unfold tailWord_3593966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385338612210307171344219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87388472598454971580502501 16385338612210307171344219)
  ·
    refine ⟨24578007918315460757016329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16385338612210307171344219 24578007918315460757016329)
    ·
      refine ⟨18433505938736595567762247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24578007918315460757016329 18433505938736595567762247)
      ·
        refine ⟨27650258908104893351643371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433505938736595567762247 27650258908104893351643371)
        ·
          refine ⟨41475388362157340027465057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650258908104893351643371 41475388362157340027465057)
          ·
            refine ⟨31106541271618005020598793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41475388362157340027465057 31106541271618005020598793)
            ·
              refine ⟨23329905953713503765449095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31106541271618005020598793 23329905953713503765449095)
              ·
                refine ⟨34994858930570255648173643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23329905953713503765449095 34994858930570255648173643)
                ·
                  refine ⟨52492288395855383472260465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34994858930570255648173643 52492288395855383472260465)
                  ·
                    refine ⟨39369216296891537604195349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52492288395855383472260465 39369216296891537604195349)
                    ·
                      refine ⟨1845432013916790825196657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39369216296891537604195349 1845432013916790825196657)
                      ·
                        rfl

theorem cell23_3593966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3593966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593966 prefixEnd_3593966 := by exact prefixLift 3593966
  have htrace : WordTrace (prefixWord ++ tailWord_3593966) baseStart_3593966 baseEnd_3593966 := by
    simpa [prefixWord, tailWord_3593966, baseEnd_3593966] using wordTrace_append hprefix tailTrace_3593966
  have hstable : (prefixWord ++ tailWord_3593966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593966).length < 2 ^ (prefixWord ++ tailWord_3593966).sum := by decide
  have hdescent : baseEnd_3593966 < baseStart_3593966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593983 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 4, 3, 2]
def baseStart_3593983 : Nat := 118140960795 + 3593983 * 2 ^ 59
def prefixEnd_3593983 : Nat := 4983230072969 + 3 ^ 40 * 3593983 * 2
def baseEnd_3593983 : Nat := 1845440743087917258684079

theorem tailTrace_3593983 : CollatzResearch.WordTrace tailWord_3593983 prefixEnd_3593983 1845440743087917258684079 := by
  unfold tailWord_3593983
  simp only [CollatzResearch.WordTrace]
  refine ⟨131083328938620869274122603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87388885959080579516081735 131083328938620869274122603)
  ·
    refine ⟨196624993407931303911183905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131083328938620869274122603 196624993407931303911183905)
    ·
      refine ⟨147468745055948477933387929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196624993407931303911183905 147468745055948477933387929)
      ·
        refine ⟨110601558791961358450040947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147468745055948477933387929 110601558791961358450040947)
        ·
          refine ⟨165902338187942037675061421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110601558791961358450040947 165902338187942037675061421)
          ·
            refine ⟨62213376820478264128148033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165902338187942037675061421 62213376820478264128148033)
            ·
              refine ⟨46660032615358698096111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62213376820478264128148033 46660032615358698096111025)
              ·
                refine ⟨34995024461519023572083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46660032615358698096111025 34995024461519023572083269)
                ·
                  refine ⟨6561567086534816919765613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34995024461519023572083269 6561567086534816919765613)
                  ·
                    refine ⟨2460587657450556344912105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6561567086534816919765613 2460587657450556344912105)
                    ·
                      refine ⟨1845440743087917258684079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460587657450556344912105 1845440743087917258684079)
                      ·
                        rfl

theorem cell23_3593983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_3593983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3593983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3593983 prefixEnd_3593983 := by exact prefixLift 3593983
  have htrace : WordTrace (prefixWord ++ tailWord_3593983) baseStart_3593983 baseEnd_3593983 := by
    simpa [prefixWord, tailWord_3593983, baseEnd_3593983] using wordTrace_append hprefix tailTrace_3593983
  have hstable : (prefixWord ++ tailWord_3593983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593983).length < 2 ^ (prefixWord ++ tailWord_3593983).sum := by decide
  have hdescent : baseEnd_3593983 < baseStart_3593983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594007 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_3594007 : Nat := 118140960795 + 3594007 * 2 ^ 59
def prefixEnd_3594007 : Nat := 4983230072969 + 3 ^ 40 * 3594007 * 2
def baseEnd_3594007 : Nat := 1845453066623625164783969

theorem tailTrace_3594007 : CollatzResearch.WordTrace tailWord_3594007 prefixEnd_3594007 1845453066623625164783969 := by
  unfold tailWord_3594007
  simp only [CollatzResearch.WordTrace]
  refine ⟨131084204290533921372996275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87389469527022614248664183 131084204290533921372996275)
  ·
    refine ⟨196626306435800882059494413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131084204290533921372996275 196626306435800882059494413)
    ·
      refine ⟨73734864913425330772310405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196626306435800882059494413 73734864913425330772310405)
      ·
        refine ⟨13825287171267249519808201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73734864913425330772310405 13825287171267249519808201)
        ·
          refine ⟨10368965378450437139856151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13825287171267249519808201 10368965378450437139856151)
          ·
            refine ⟨15553448067675655709784227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368965378450437139856151 15553448067675655709784227)
            ·
              refine ⟨23330172101513483564676341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15553448067675655709784227 23330172101513483564676341)
              ·
                refine ⟨2187203634516889084188407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23330172101513483564676341 2187203634516889084188407)
                ·
                  refine ⟨3280805451775333626282611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187203634516889084188407 3280805451775333626282611)
                  ·
                    refine ⟨4921208177663000439423917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3280805451775333626282611 4921208177663000439423917)
                    ·
                      refine ⟨1845453066623625164783969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921208177663000439423917 1845453066623625164783969)
                      ·
                        rfl

theorem cell23_3594007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_3594007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594007 prefixEnd_3594007 := by exact prefixLift 3594007
  have htrace : WordTrace (prefixWord ++ tailWord_3594007) baseStart_3594007 baseEnd_3594007 := by
    simpa [prefixWord, tailWord_3594007, baseEnd_3594007] using wordTrace_append hprefix tailTrace_3594007
  have hstable : (prefixWord ++ tailWord_3594007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594007).length < 2 ^ (prefixWord ++ tailWord_3594007).sum := by decide
  have hdescent : baseEnd_3594007 < baseStart_3594007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594010 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_3594010 : Nat := 118140960795 + 3594010 * 2 ^ 59
def prefixEnd_3594010 : Nat := 4983230072969 + 3 ^ 40 * 3594010 * 2
def baseEnd_3594010 : Nat := 615151535688529551015485

theorem tailTrace_3594010 : CollatzResearch.WordTrace tailWord_3594010 prefixEnd_3594010 615151535688529551015485 := by
  unfold tailWord_3594010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771078427380763221338871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87389542473015368590236989 32771078427380763221338871)
  ·
    refine ⟨49156617641071144832008307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32771078427380763221338871 49156617641071144832008307)
    ·
      refine ⟨73734926461606717248012461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49156617641071144832008307 73734926461606717248012461)
      ·
        refine ⟨27650597423102518968004673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73734926461606717248012461 27650597423102518968004673)
        ·
          refine ⟨20737948067326889226003505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27650597423102518968004673 20737948067326889226003505)
          ·
            refine ⟨15553461050495166919502629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20737948067326889226003505 15553461050495166919502629)
            ·
              refine ⟨2916273946967843797406743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15553461050495166919502629 2916273946967843797406743)
              ·
                refine ⟨4374410920451765696110115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916273946967843797406743 4374410920451765696110115)
                ·
                  refine ⟨6561616380677648544165173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374410920451765696110115 6561616380677648544165173)
                  ·
                    refine ⟨615151535688529551015485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6561616380677648544165173 615151535688529551015485)
                    ·
                      rfl

theorem cell23_3594010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_3594010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594010 prefixEnd_3594010 := by exact prefixLift 3594010
  have htrace : WordTrace (prefixWord ++ tailWord_3594010) baseStart_3594010 baseEnd_3594010 := by
    simpa [prefixWord, tailWord_3594010, baseEnd_3594010] using wordTrace_append hprefix tailTrace_3594010
  have hstable : (prefixWord ++ tailWord_3594010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594010).length < 2 ^ (prefixWord ++ tailWord_3594010).sum := by decide
  have hdescent : baseEnd_3594010 < baseStart_3594010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594014 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3594014 : Nat := 118140960795 + 3594014 * 2 ^ 59
def prefixEnd_3594014 : Nat := 4983230072969 + 3 ^ 40 * 3594014 * 2
def baseEnd_3594014 : Nat := 205050740109800737488493

theorem tailTrace_3594014 : CollatzResearch.WordTrace tailWord_3594014 prefixEnd_3594014 205050740109800737488493 := by
  unfold tailWord_3594014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385557450188570196062637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87389639734339041045667397 16385557450188570196062637)
  ·
    refine ⟨6144584043820713823523489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16385557450188570196062637 6144584043820713823523489)
    ·
      refine ⟨4608438032865535367642617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144584043820713823523489 4608438032865535367642617)
      ·
        refine ⟨3456328524649151525731963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608438032865535367642617 3456328524649151525731963)
        ·
          refine ⟨5184492786973727288597945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456328524649151525731963 5184492786973727288597945)
          ·
            refine ⟨3888369590230295466448459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184492786973727288597945 3888369590230295466448459)
            ·
              refine ⟨5832554385345443199672689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888369590230295466448459 5832554385345443199672689)
              ·
                refine ⟨4374415789009082399754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5832554385345443199672689 4374415789009082399754517)
                ·
                  refine ⟨205050740109800737488493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4374415789009082399754517 205050740109800737488493)
                  ·
                    rfl

theorem cell23_3594014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3594014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594014 prefixEnd_3594014 := by exact prefixLift 3594014
  have htrace : WordTrace (prefixWord ++ tailWord_3594014) baseStart_3594014 baseEnd_3594014 := by
    simpa [prefixWord, tailWord_3594014, baseEnd_3594014] using wordTrace_append hprefix tailTrace_3594014
  have hstable : (prefixWord ++ tailWord_3594014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594014).length < 2 ^ (prefixWord ++ tailWord_3594014).sum := by decide
  have hdescent : baseEnd_3594014 < baseStart_3594014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594033 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3594033 : Nat := 118140960795 + 3594033 * 2 ^ 59
def prefixEnd_3594033 : Nat := 4983230072969 + 3 ^ 40 * 3594033 * 2
def baseEnd_3594033 : Nat := 1845466417120642063058849

theorem tailTrace_3594033 : CollatzResearch.WordTrace tailWord_3594033 prefixEnd_3594033 1845466417120642063058849 := by
  unfold tailWord_3594033
  simp only [CollatzResearch.WordTrace]
  refine ⟨131085152588439727813442753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87390101725626485208961835 131085152588439727813442753)
  ·
    refine ⟨98313864441329795860082065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131085152588439727813442753 98313864441329795860082065)
    ·
      refine ⟨73735398330997346895061549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98313864441329795860082065 73735398330997346895061549)
      ·
        refine ⟨27650774374124005085648081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73735398330997346895061549 27650774374124005085648081)
        ·
          refine ⟨20738080780593003814236061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27650774374124005085648081 20738080780593003814236061)
          ·
            refine ⟨7776780292722376430338523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20738080780593003814236061 7776780292722376430338523)
            ·
              refine ⟨11665170439083564645507785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776780292722376430338523 11665170439083564645507785)
              ·
                refine ⟨8748877829312673484130839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11665170439083564645507785 8748877829312673484130839)
                ·
                  refine ⟨13123316743969010226196259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8748877829312673484130839 13123316743969010226196259)
                  ·
                    refine ⟨19684975115953515339294389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13123316743969010226196259 19684975115953515339294389)
                    ·
                      refine ⟨1845466417120642063058849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19684975115953515339294389 1845466417120642063058849)
                      ·
                        rfl

theorem cell23_3594033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3594033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594033 prefixEnd_3594033 := by exact prefixLift 3594033
  have htrace : WordTrace (prefixWord ++ tailWord_3594033) baseStart_3594033 baseEnd_3594033 := by
    simpa [prefixWord, tailWord_3594033, baseEnd_3594033] using wordTrace_append hprefix tailTrace_3594033
  have hstable : (prefixWord ++ tailWord_3594033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594033).length < 2 ^ (prefixWord ++ tailWord_3594033).sum := by decide
  have hdescent : baseEnd_3594033 < baseStart_3594033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594080 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_3594080 : Nat := 118140960795 + 3594080 * 2 ^ 59
def prefixEnd_3594080 : Nat := 4983230072969 + 3 ^ 40 * 3594080 * 2
def baseEnd_3594080 : Nat := 1845490550711403379171133

theorem tailTrace_3594080 : CollatzResearch.WordTrace tailWord_3594080 prefixEnd_3594080 1845490550711403379171133 := by
  unfold tailWord_3594080
  simp only [CollatzResearch.WordTrace]
  refine ⟨65543433409634727420201847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87391244546179636560269129 65543433409634727420201847)
  ·
    refine ⟨98315150114452091130302771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65543433409634727420201847 98315150114452091130302771)
    ·
      refine ⟨147472725171678136695454157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98315150114452091130302771 147472725171678136695454157)
      ·
        refine ⟨55302271939379301260795309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147472725171678136695454157 55302271939379301260795309)
        ·
          refine ⟨20738351977267237972798241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55302271939379301260795309 20738351977267237972798241)
          ·
            refine ⟨15553763982950428479598681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20738351977267237972798241 15553763982950428479598681)
            ·
              refine ⟨11665322987212821359699011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15553763982950428479598681 11665322987212821359699011)
              ·
                refine ⟨17497984480819232039548517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11665322987212821359699011 17497984480819232039548517)
                ·
                  refine ⟨3280872090153606007415347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17497984480819232039548517 3280872090153606007415347)
                  ·
                    refine ⟨4921308135230409011123021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3280872090153606007415347 4921308135230409011123021)
                    ·
                      refine ⟨1845490550711403379171133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921308135230409011123021 1845490550711403379171133)
                      ·
                        rfl

theorem cell23_3594080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_3594080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594080 prefixEnd_3594080 := by exact prefixLift 3594080
  have htrace : WordTrace (prefixWord ++ tailWord_3594080) baseStart_3594080 baseEnd_3594080 := by
    simpa [prefixWord, tailWord_3594080, baseEnd_3594080] using wordTrace_append hprefix tailTrace_3594080
  have hstable : (prefixWord ++ tailWord_3594080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594080).length < 2 ^ (prefixWord ++ tailWord_3594080).sum := by decide
  have hdescent : baseEnd_3594080 < baseStart_3594080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594096 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_3594096 : Nat := 118140960795 + 3594096 * 2 ^ 59
def prefixEnd_3594096 : Nat := 4983230072969 + 3 ^ 40 * 3594096 * 2
def baseEnd_3594096 : Nat := 615166255467291772190353

theorem tailTrace_3594096 : CollatzResearch.WordTrace tailWord_3594096 prefixEnd_3594096 615166255467291772190353 := by
  unfold tailWord_3594096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65543725193605744786493071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87391633591474326381990761 65543725193605744786493071)
  ·
    refine ⟨98315587790408617179739607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65543725193605744786493071 98315587790408617179739607)
    ·
      refine ⟨147473381685612925769609411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98315587790408617179739607 147473381685612925769609411)
      ·
        refine ⟨221210072528419388654414117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147473381685612925769609411 221210072528419388654414117)
        ·
          refine ⟨41476888599078635372702647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221210072528419388654414117 41476888599078635372702647)
          ·
            refine ⟨62215332898617953059053971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41476888599078635372702647 62215332898617953059053971)
            ·
              refine ⟨93322999347926929588580957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62215332898617953059053971 93322999347926929588580957)
              ·
                refine ⟨34996124755472598595717859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93322999347926929588580957 34996124755472598595717859)
                ·
                  refine ⟨52494187133208897893576789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34996124755472598595717859 52494187133208897893576789)
                  ·
                    refine ⟨615166255467291772190353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52494187133208897893576789 615166255467291772190353)
                    ·
                      rfl

theorem cell23_3594096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_3594096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594096 prefixEnd_3594096 := by exact prefixLift 3594096
  have htrace : WordTrace (prefixWord ++ tailWord_3594096) baseStart_3594096 baseEnd_3594096 := by
    simpa [prefixWord, tailWord_3594096, baseEnd_3594096] using wordTrace_append hprefix tailTrace_3594096
  have hstable : (prefixWord ++ tailWord_3594096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594096).length < 2 ^ (prefixWord ++ tailWord_3594096).sum := by decide
  have hdescent : baseEnd_3594096 < baseStart_3594096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594133 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3594133 : Nat := 118140960795 + 3594133 * 2 ^ 59
def prefixEnd_3594133 : Nat := 4983230072969 + 3 ^ 40 * 3594133 * 2
def baseEnd_3594133 : Nat := 1845517765186091671808389

theorem tailTrace_3594133 : CollatzResearch.WordTrace tailWord_3594133 prefixEnd_3594133 1845517765186091671808389 := by
  unfold tailWord_3594133
  simp only [CollatzResearch.WordTrace]
  refine ⟨131088799888077444892083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87392533258718296594722035 131088799888077444892083053)
  ·
    refine ⟨49158299958029041834531145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131088799888077444892083053 49158299958029041834531145)
    ·
      refine ⟨36868724968521781375898359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49158299958029041834531145 36868724968521781375898359)
      ·
        refine ⟨55303087452782672063847539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36868724968521781375898359 55303087452782672063847539)
        ·
          refine ⟨82954631179174008095771309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55303087452782672063847539 82954631179174008095771309)
          ·
            refine ⟨31107986692190253035914241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82954631179174008095771309 31107986692190253035914241)
            ·
              refine ⟨23330990019142689776935681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31107986692190253035914241 23330990019142689776935681)
              ·
                refine ⟨17498242514357017332701761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23330990019142689776935681 17498242514357017332701761)
                ·
                  refine ⟨13123681885767762999526321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17498242514357017332701761 13123681885767762999526321)
                  ·
                    refine ⟨9842761414325822249644741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13123681885767762999526321 9842761414325822249644741)
                    ·
                      refine ⟨1845517765186091671808389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9842761414325822249644741 1845517765186091671808389)
                      ·
                        rfl

theorem cell23_3594133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3594133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594133 prefixEnd_3594133 := by exact prefixLift 3594133
  have htrace : WordTrace (prefixWord ++ tailWord_3594133) baseStart_3594133 baseEnd_3594133 := by
    simpa [prefixWord, tailWord_3594133, baseEnd_3594133] using wordTrace_append hprefix tailTrace_3594133
  have hstable : (prefixWord ++ tailWord_3594133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594133).length < 2 ^ (prefixWord ++ tailWord_3594133).sum := by decide
  have hdescent : baseEnd_3594133 < baseStart_3594133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594137 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 2, 2, 2]
def baseStart_3594137 : Nat := 118140960795 + 3594137 * 2 ^ 59
def prefixEnd_3594137 : Nat := 4983230072969 + 3 ^ 40 * 3594137 * 2
def baseEnd_3594137 : Nat := 1845519819108709656158371

theorem tailTrace_3594137 : CollatzResearch.WordTrace tailWord_3594137 prefixEnd_3594137 1845519819108709656158371 := by
  unfold tailWord_3594137
  simp only [CollatzResearch.WordTrace]
  refine ⟨131088945780062953575228665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87392630520041969050152443 131088945780062953575228665)
  ·
    refine ⟨98316709335047215181421499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131088945780062953575228665 98316709335047215181421499)
    ·
      refine ⟨147475064002570822772132249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98316709335047215181421499 147475064002570822772132249)
      ·
        refine ⟨110606298001928117079099187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147475064002570822772132249 110606298001928117079099187)
        ·
          refine ⟨165909447002892175618648781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110606298001928117079099187 165909447002892175618648781)
          ·
            refine ⟨62216042626084565856993293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165909447002892175618648781 62216042626084565856993293)
            ·
              refine ⟨23331015984781712196372485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62216042626084565856993293 23331015984781712196372485)
              ·
                refine ⟨4374565497146571036819841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23331015984781712196372485 4374565497146571036819841)
                ·
                  refine ⟨3280924122859928277614881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374565497146571036819841 3280924122859928277614881)
                  ·
                    refine ⟨2460693092144946208211161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3280924122859928277614881 2460693092144946208211161)
                    ·
                      refine ⟨1845519819108709656158371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460693092144946208211161 1845519819108709656158371)
                      ·
                        rfl

theorem cell23_3594137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_3594137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594137 prefixEnd_3594137 := by exact prefixLift 3594137
  have htrace : WordTrace (prefixWord ++ tailWord_3594137) baseStart_3594137 baseEnd_3594137 := by
    simpa [prefixWord, tailWord_3594137, baseEnd_3594137] using wordTrace_append hprefix tailTrace_3594137
  have hstable : (prefixWord ++ tailWord_3594137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594137).length < 2 ^ (prefixWord ++ tailWord_3594137).sum := by decide
  have hdescent : baseEnd_3594137 < baseStart_3594137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594140 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3594140 : Nat := 118140960795 + 3594140 * 2 ^ 59
def prefixEnd_3594140 : Nat := 4983230072969 + 3 ^ 40 * 3594140 * 2
def baseEnd_3594140 : Nat := 1845521359550673144420857

theorem tailTrace_3594140 : CollatzResearch.WordTrace tailWord_3594140 prefixEnd_3594140 1845521359550673144420857 := by
  unfold tailWord_3594140
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544527599526042543793937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87392703466034723391725249 65544527599526042543793937)
  ·
    refine ⟨49158395699644531907845453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65544527599526042543793937 49158395699644531907845453)
    ·
      refine ⟨18434398387366699465442045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49158395699644531907845453 18434398387366699465442045)
      ·
        refine ⟨6912899395262512299540767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18434398387366699465442045 6912899395262512299540767)
        ·
          refine ⟨10369349092893768449311151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912899395262512299540767 10369349092893768449311151)
          ·
            refine ⟨15554023639340652673966727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369349092893768449311151 15554023639340652673966727)
            ·
              refine ⟨23331035459010979010950091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554023639340652673966727 23331035459010979010950091)
              ·
                refine ⟨34996553188516468516425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23331035459010979010950091 34996553188516468516425137)
                ·
                  refine ⟨26247414891387351387318853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34996553188516468516425137 26247414891387351387318853)
                  ·
                    refine ⟨4921390292135128385122285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26247414891387351387318853 4921390292135128385122285)
                    ·
                      refine ⟨1845521359550673144420857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921390292135128385122285 1845521359550673144420857)
                      ·
                        rfl

theorem cell23_3594140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3594140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594140 prefixEnd_3594140 := by exact prefixLift 3594140
  have htrace : WordTrace (prefixWord ++ tailWord_3594140) baseStart_3594140 baseEnd_3594140 := by
    simpa [prefixWord, tailWord_3594140, baseEnd_3594140] using wordTrace_append hprefix tailTrace_3594140
  have hstable : (prefixWord ++ tailWord_3594140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594140).length < 2 ^ (prefixWord ++ tailWord_3594140).sum := by decide
  have hdescent : baseEnd_3594140 < baseStart_3594140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594223 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_3594223 : Nat := 118140960795 + 3594223 * 2 ^ 59
def prefixEnd_3594223 : Nat := 4983230072969 + 3 ^ 40 * 3594223 * 2
def baseEnd_3594223 : Nat := 1845563978444996319682975

theorem tailTrace_3594223 : CollatzResearch.WordTrace tailWord_3594223 prefixEnd_3594223 1845563978444996319682975 := by
  unfold tailWord_3594223
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092082457751390262859323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87394721638500926841906215 131092082457751390262859323)
  ·
    refine ⟨196638123686627085394288985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131092082457751390262859323 196638123686627085394288985)
    ·
      refine ⟨147478592764970314045716739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196638123686627085394288985 147478592764970314045716739)
      ·
        refine ⟨221217889147455471068575109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147478592764970314045716739 221217889147455471068575109)
        ·
          refine ⟨41478354215147900825357833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221217889147455471068575109 41478354215147900825357833)
          ·
            refine ⟨31108765661360925619018375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41478354215147900825357833 31108765661360925619018375)
            ·
              refine ⟨46663148492041388428527563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31108765661360925619018375 46663148492041388428527563)
              ·
                refine ⟨69994722738062082642791345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46663148492041388428527563 69994722738062082642791345)
                ·
                  refine ⟨52496042053546561982093509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69994722738062082642791345 52496042053546561982093509)
                  ·
                    refine ⟨9843007885039980371642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52496042053546561982093509 9843007885039980371642533)
                    ·
                      refine ⟨1845563978444996319682975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9843007885039980371642533 1845563978444996319682975)
                      ·
                        rfl

theorem cell23_3594223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_3594223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594223 prefixEnd_3594223 := by exact prefixLift 3594223
  have htrace : WordTrace (prefixWord ++ tailWord_3594223) baseStart_3594223 baseEnd_3594223 := by
    simpa [prefixWord, tailWord_3594223, baseEnd_3594223] using wordTrace_append hprefix tailTrace_3594223
  have hstable : (prefixWord ++ tailWord_3594223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594223).length < 2 ^ (prefixWord ++ tailWord_3594223).sum := by decide
  have hdescent : baseEnd_3594223 < baseStart_3594223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594233 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 8]
def baseStart_3594233 : Nat := 118140960795 + 3594233 * 2 ^ 59
def prefixEnd_3594233 : Nat := 4983230072969 + 3 ^ 40 * 3594233 * 2
def baseEnd_3594233 : Nat := 205063234805726808950881

theorem tailTrace_3594233 : CollatzResearch.WordTrace tailWord_3594233 prefixEnd_3594233 205063234805726808950881 := by
  unfold tailWord_3594233
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092447187715161970723353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87394964791810107980482235 131092447187715161970723353)
  ·
    refine ⟨98319335390786371478042515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131092447187715161970723353 98319335390786371478042515)
    ·
      refine ⟨147479003086179557217063773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98319335390786371478042515 147479003086179557217063773)
      ·
        refine ⟨55304626157317333956398915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147479003086179557217063773 55304626157317333956398915)
        ·
          refine ⟨82956939235976000934598373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55304626157317333956398915 82956939235976000934598373)
          ·
            refine ⟨15554426106745500175237195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82956939235976000934598373 15554426106745500175237195)
            ·
              refine ⟨23331639160118250262855793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554426106745500175237195 23331639160118250262855793)
              ·
                refine ⟨17498729370088687697141845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23331639160118250262855793 17498729370088687697141845)
                ·
                  refine ⟨205063234805726808950881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17498729370088687697141845 205063234805726808950881)
                  ·
                    rfl

theorem cell23_3594233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_3594233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594233 prefixEnd_3594233 := by exact prefixLift 3594233
  have htrace : WordTrace (prefixWord ++ tailWord_3594233) baseStart_3594233 baseEnd_3594233 := by
    simpa [prefixWord, tailWord_3594233, baseEnd_3594233] using wordTrace_append hprefix tailTrace_3594233
  have hstable : (prefixWord ++ tailWord_3594233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594233).length < 2 ^ (prefixWord ++ tailWord_3594233).sum := by decide
  have hdescent : baseEnd_3594233 < baseStart_3594233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594244 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3594244 : Nat := 118140960795 + 3594244 * 2 ^ 59
def prefixEnd_3594244 : Nat := 4983230072969 + 3 ^ 40 * 3594244 * 2
def baseEnd_3594244 : Nat := 1845574761538740737520379

theorem tailTrace_3594244 : CollatzResearch.WordTrace tailWord_3594244 prefixEnd_3594244 1845574761538740737520379 := by
  unfold tailWord_3594244
  simp only [CollatzResearch.WordTrace]
  refine ⟨65546424195337655424686893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87395232260450207232915857 65546424195337655424686893)
  ·
    refine ⟨24579909073251620784257585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65546424195337655424686893 24579909073251620784257585)
    ·
      refine ⟨18434931804938715588193189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24579909073251620784257585 18434931804938715588193189)
      ·
        refine ⟨3456549713426009172786223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18434931804938715588193189 3456549713426009172786223)
        ·
          refine ⟨5184824570139013759179335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456549713426009172786223 5184824570139013759179335)
          ·
            refine ⟨7777236855208520638769003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184824570139013759179335 7777236855208520638769003)
            ·
              refine ⟨11665855282812780958153505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777236855208520638769003 11665855282812780958153505)
              ·
                refine ⟨8749391462109585718615129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11665855282812780958153505 8749391462109585718615129)
                ·
                  refine ⟨6562043596582189288961347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749391462109585718615129 6562043596582189288961347)
                  ·
                    refine ⟨9843065394873283933442021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562043596582189288961347 9843065394873283933442021)
                    ·
                      refine ⟨1845574761538740737520379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9843065394873283933442021 1845574761538740737520379)
                      ·
                        rfl

theorem cell23_3594244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3594244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594244 prefixEnd_3594244 := by exact prefixLift 3594244
  have htrace : WordTrace (prefixWord ++ tailWord_3594244) baseStart_3594244 baseEnd_3594244 := by
    simpa [prefixWord, tailWord_3594244, baseEnd_3594244] using wordTrace_append hprefix tailTrace_3594244
  have hstable : (prefixWord ++ tailWord_3594244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594244).length < 2 ^ (prefixWord ++ tailWord_3594244).sum := by decide
  have hdescent : baseEnd_3594244 < baseStart_3594244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594247 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3594247 : Nat := 118140960795 + 3594247 * 2 ^ 59
def prefixEnd_3594247 : Nat := 4983230072969 + 3 ^ 40 * 3594247 * 2
def baseEnd_3594247 : Nat := 1845576301980704225782865

theorem tailTrace_3594247 : CollatzResearch.WordTrace tailWord_3594247 prefixEnd_3594247 1845576301980704225782865 := by
  unfold tailWord_3594247
  simp only [CollatzResearch.WordTrace]
  refine ⟨131092957809664442361732995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87395305206442961574488663 131092957809664442361732995)
  ·
    refine ⟨196639436714496663542599493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131092957809664442361732995 196639436714496663542599493)
    ·
      refine ⟨36869894383968124414237405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196639436714496663542599493 36869894383968124414237405)
      ·
        refine ⟨13826210393988046655339027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36869894383968124414237405 13826210393988046655339027)
        ·
          refine ⟨20739315590982069983008541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826210393988046655339027 20739315590982069983008541)
          ·
            refine ⟨7777243346618276243628203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20739315590982069983008541 7777243346618276243628203)
            ·
              refine ⟨11665865019927414365442305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777243346618276243628203 11665865019927414365442305)
              ·
                refine ⟨8749398764945560774081729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11665865019927414365442305 8749398764945560774081729)
                ·
                  refine ⟨6562049073709170580561297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749398764945560774081729 6562049073709170580561297)
                  ·
                    refine ⟨4921536805281877935420973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562049073709170580561297 4921536805281877935420973)
                    ·
                      refine ⟨1845576301980704225782865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921536805281877935420973 1845576301980704225782865)
                      ·
                        rfl

theorem cell23_3594247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3594247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594247 prefixEnd_3594247 := by exact prefixLift 3594247
  have htrace : WordTrace (prefixWord ++ tailWord_3594247) baseStart_3594247 baseEnd_3594247 := by
    simpa [prefixWord, tailWord_3594247, baseEnd_3594247] using wordTrace_append hprefix tailTrace_3594247
  have hstable : (prefixWord ++ tailWord_3594247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594247).length < 2 ^ (prefixWord ++ tailWord_3594247).sum := by decide
  have hdescent : baseEnd_3594247 < baseStart_3594247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594317 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3594317 : Nat := 118140960795 + 3594317 * 2 ^ 59
def prefixEnd_3594317 : Nat := 4983230072969 + 3 ^ 40 * 3594317 * 2
def baseEnd_3594317 : Nat := 1845612245626518951907543

theorem tailTrace_3594317 : CollatzResearch.WordTrace tailWord_3594317 prefixEnd_3594317 1845612245626518951907543 := by
  unfold tailWord_3594317
  simp only [CollatzResearch.WordTrace]
  refine ⟨131095510919410844316781205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87397007279607229544520803 131095510919410844316781205)
  ·
    refine ⟨6145102074347383327349119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131095510919410844316781205 6145102074347383327349119)
    ·
      refine ⟨9217653111521074991023679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145102074347383327349119 9217653111521074991023679)
      ·
        refine ⟨13826479667281612486535519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217653111521074991023679 13826479667281612486535519)
        ·
          refine ⟨20739719500922418729803279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826479667281612486535519 20739719500922418729803279)
          ·
            refine ⟨31109579251383628094704919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20739719500922418729803279 31109579251383628094704919)
            ·
              refine ⟨46664368877075442142057379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31109579251383628094704919 46664368877075442142057379)
              ·
                refine ⟨69996553315613163213086069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46664368877075442142057379 69996553315613163213086069)
                ·
                  refine ⟨6562176873338734051226819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69996553315613163213086069 6562176873338734051226819)
                  ·
                    refine ⟨9843265310008101076840229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562176873338734051226819 9843265310008101076840229)
                    ·
                      refine ⟨1845612245626518951907543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9843265310008101076840229 1845612245626518951907543)
                      ·
                        rfl

theorem cell23_3594317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3594317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594317 prefixEnd_3594317 := by exact prefixLift 3594317
  have htrace : WordTrace (prefixWord ++ tailWord_3594317) baseStart_3594317 baseEnd_3594317 := by
    simpa [prefixWord, tailWord_3594317, baseEnd_3594317] using wordTrace_append hprefix tailTrace_3594317
  have hstable : (prefixWord ++ tailWord_3594317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594317).length < 2 ^ (prefixWord ++ tailWord_3594317).sum := by decide
  have hdescent : baseEnd_3594317 < baseStart_3594317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594327 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 2, 4]
def baseStart_3594327 : Nat := 118140960795 + 3594327 * 2 ^ 59
def prefixEnd_3594327 : Nat := 4983230072969 + 3 ^ 40 * 3594327 * 2
def baseEnd_3594327 : Nat := 615205793477687970927499

theorem tailTrace_3594327 : CollatzResearch.WordTrace tailWord_3594327 prefixEnd_3594327 615205793477687970927499 := by
  unfold tailWord_3594327
  simp only [CollatzResearch.WordTrace]
  refine ⟨131095875649374616024645235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87397250432916410683096823 131095875649374616024645235)
  ·
    refine ⟨196643813474061924036967853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131095875649374616024645235 196643813474061924036967853)
    ·
      refine ⟨73741430052773221513862945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196643813474061924036967853 73741430052773221513862945)
      ·
        refine ⟨55306072539579916135397209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73741430052773221513862945 55306072539579916135397209)
        ·
          refine ⟨41479554404684937101547907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55306072539579916135397209 41479554404684937101547907)
          ·
            refine ⟨62219331607027405652321861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41479554404684937101547907 62219331607027405652321861)
            ·
              refine ⟨11666124676317638559810349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62219331607027405652321861 11666124676317638559810349)
              ·
                refine ⟨4374796753619114459928881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11666124676317638559810349 4374796753619114459928881)
                ·
                  refine ⟨3281097565214335844946661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374796753619114459928881 3281097565214335844946661)
                  ·
                    refine ⟨615205793477687970927499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281097565214335844946661 615205793477687970927499)
                    ·
                      rfl

theorem cell23_3594327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_3594327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594327 prefixEnd_3594327 := by exact prefixLift 3594327
  have htrace : WordTrace (prefixWord ++ tailWord_3594327) baseStart_3594327 baseEnd_3594327 := by
    simpa [prefixWord, tailWord_3594327, baseEnd_3594327] using wordTrace_append hprefix tailTrace_3594327
  have hstable : (prefixWord ++ tailWord_3594327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594327).length < 2 ^ (prefixWord ++ tailWord_3594327).sum := by decide
  have hdescent : baseEnd_3594327 < baseStart_3594327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594337 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3594337 : Nat := 118140960795 + 3594337 * 2 ^ 59
def prefixEnd_3594337 : Nat := 4983230072969 + 3 ^ 40 * 3594337 * 2
def baseEnd_3594337 : Nat := 1845622515239608873657451

theorem tailTrace_3594337 : CollatzResearch.WordTrace tailWord_3594337 prefixEnd_3594337 1845622515239608873657451 := by
  unfold tailWord_3594337
  simp only [CollatzResearch.WordTrace]
  refine ⟨131096240379338387732509265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87397493586225591821672843 131096240379338387732509265)
  ·
    refine ⟨98322180284503790799381949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131096240379338387732509265 98322180284503790799381949)
    ·
      refine ⟨36870817606688921549768231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98322180284503790799381949 36870817606688921549768231)
      ·
        refine ⟨55306226410033382324652347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36870817606688921549768231 55306226410033382324652347)
        ·
          refine ⟨82959339615050073486978521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55306226410033382324652347 82959339615050073486978521)
          ·
            refine ⟨62219504711287555115233891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82959339615050073486978521 62219504711287555115233891)
            ·
              refine ⟨93329257066931332672850837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62219504711287555115233891 93329257066931332672850837)
              ·
                refine ⟨4374808925012406219039883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93329257066931332672850837 4374808925012406219039883)
                ·
                  refine ⟨6562213387518609328559825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374808925012406219039883 6562213387518609328559825)
                  ·
                    refine ⟨4921660040638956996419869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562213387518609328559825 4921660040638956996419869)
                    ·
                      refine ⟨1845622515239608873657451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921660040638956996419869 1845622515239608873657451)
                      ·
                        rfl

theorem cell23_3594337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3594337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594337 prefixEnd_3594337 := by exact prefixLift 3594337
  have htrace : WordTrace (prefixWord ++ tailWord_3594337) baseStart_3594337 baseEnd_3594337 := by
    simpa [prefixWord, tailWord_3594337, baseEnd_3594337] using wordTrace_append hprefix tailTrace_3594337
  have hstable : (prefixWord ++ tailWord_3594337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594337).length < 2 ^ (prefixWord ++ tailWord_3594337).sum := by decide
  have hdescent : baseEnd_3594337 < baseStart_3594337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594338 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3594338 : Nat := 118140960795 + 3594338 * 2 ^ 59
def prefixEnd_3594338 : Nat := 4983230072969 + 3 ^ 40 * 3594338 * 2
def baseEnd_3594338 : Nat := 1845623028720263369744947

theorem tailTrace_3594338 : CollatzResearch.WordTrace tailWord_3594338 prefixEnd_3594338 1845623028720263369744947 := by
  unfold tailWord_3594338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32774069213083691225823917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87397517901556509935530445 32774069213083691225823917)
  ·
    refine ⟨12290275954906384209683969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32774069213083691225823917 12290275954906384209683969)
    ·
      refine ⟨9217706966179788157262977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12290275954906384209683969 9217706966179788157262977)
      ·
        refine ⟨6913280224634841117947233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217706966179788157262977 6913280224634841117947233)
        ·
          refine ⟨5184960168476130838460425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913280224634841117947233 5184960168476130838460425)
          ·
            refine ⟨3888720126357098128845319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184960168476130838460425 3888720126357098128845319)
            ·
              refine ⟨5833080189535647193267979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888720126357098128845319 5833080189535647193267979)
              ·
                refine ⟨8749620284303470789901969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833080189535647193267979 8749620284303470789901969)
                ·
                  refine ⟨6562215213227603092426477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749620284303470789901969 6562215213227603092426477)
                  ·
                    refine ⟨2460830704960351159659929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6562215213227603092426477 2460830704960351159659929)
                    ·
                      refine ⟨1845623028720263369744947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460830704960351159659929 1845623028720263369744947)
                      ·
                        rfl

theorem cell23_3594338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3594338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594338 prefixEnd_3594338 := by exact prefixLift 3594338
  have htrace : WordTrace (prefixWord ++ tailWord_3594338) baseStart_3594338 baseEnd_3594338 := by
    simpa [prefixWord, tailWord_3594338, baseEnd_3594338] using wordTrace_append hprefix tailTrace_3594338
  have hstable : (prefixWord ++ tailWord_3594338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594338).length < 2 ^ (prefixWord ++ tailWord_3594338).sum := by decide
  have hdescent : baseEnd_3594338 < baseStart_3594338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594351 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 1, 2, 2]
def baseStart_3594351 : Nat := 118140960795 + 3594351 * 2 ^ 59
def prefixEnd_3594351 : Nat := 4983230072969 + 3 ^ 40 * 3594351 * 2
def baseEnd_3594351 : Nat := 1845629703968771818882387

theorem tailTrace_3594351 : CollatzResearch.WordTrace tailWord_3594351 prefixEnd_3594351 1845629703968771818882387 := by
  unfold tailWord_3594351
  simp only [CollatzResearch.WordTrace]
  refine ⟨131096751001287668123518907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87397834000858445415679271 131096751001287668123518907)
  ·
    refine ⟨196645126501931502185278361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131096751001287668123518907 196645126501931502185278361)
    ·
      refine ⟨147483844876448626638958771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196645126501931502185278361 147483844876448626638958771)
      ·
        refine ⟨221225767314672939958438157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147483844876448626638958771 221225767314672939958438157)
        ·
          refine ⟨82959662743002352484414309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221225767314672939958438157 82959662743002352484414309)
          ·
            refine ⟨15554936764312941090827683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82959662743002352484414309 15554936764312941090827683)
            ·
              refine ⟨23332405146469411636241525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15554936764312941090827683 23332405146469411636241525)
              ·
                refine ⟨2187412982481507340897643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23332405146469411636241525 2187412982481507340897643)
                ·
                  refine ⟨3281119473722261011346465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187412982481507340897643 3281119473722261011346465)
                  ·
                    refine ⟨2460839605291695758509849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3281119473722261011346465 2460839605291695758509849)
                    ·
                      refine ⟨1845629703968771818882387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460839605291695758509849 1845629703968771818882387)
                      ·
                        rfl

theorem cell23_3594351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 2, 2].length) (baseStart_3594351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594351 prefixEnd_3594351 := by exact prefixLift 3594351
  have htrace : WordTrace (prefixWord ++ tailWord_3594351) baseStart_3594351 baseEnd_3594351 := by
    simpa [prefixWord, tailWord_3594351, baseEnd_3594351] using wordTrace_append hprefix tailTrace_3594351
  have hstable : (prefixWord ++ tailWord_3594351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594351).length < 2 ^ (prefixWord ++ tailWord_3594351).sum := by decide
  have hdescent : baseEnd_3594351 < baseStart_3594351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594354 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3594354 : Nat := 118140960795 + 3594354 * 2 ^ 59
def prefixEnd_3594354 : Nat := 4983230072969 + 3 ^ 40 * 3594354 * 2
def baseEnd_3594354 : Nat := 1845631244410735307144873

theorem tailTrace_3594354 : CollatzResearch.WordTrace tailWord_3594354 prefixEnd_3594354 1845631244410735307144873 := by
  unfold tailWord_3594354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32774215105069199908969529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87397906946851199757252077 32774215105069199908969529)
  ·
    refine ⟨24580661328801899931727147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32774215105069199908969529 24580661328801899931727147)
    ·
      refine ⟨36870991993202849897590721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24580661328801899931727147 36870991993202849897590721)
      ·
        refine ⟨27653243994902137423193041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36870991993202849897590721 27653243994902137423193041)
        ·
          refine ⟨20739932996176603067394781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27653243994902137423193041 20739932996176603067394781)
          ·
            refine ⟨7777474873566226150273043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20739932996176603067394781 7777474873566226150273043)
            ·
              refine ⟨11666212310349339225409565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777474873566226150273043 11666212310349339225409565)
              ·
                refine ⟨4374829616381002209528587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11666212310349339225409565 4374829616381002209528587)
                ·
                  refine ⟨6562244424571503314292881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374829616381002209528587 6562244424571503314292881)
                  ·
                    refine ⟨4921683318428627485719661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562244424571503314292881 4921683318428627485719661)
                    ·
                      refine ⟨1845631244410735307144873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921683318428627485719661 1845631244410735307144873)
                      ·
                        rfl

theorem cell23_3594354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3594354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594354 prefixEnd_3594354 := by exact prefixLift 3594354
  have htrace : WordTrace (prefixWord ++ tailWord_3594354) baseStart_3594354 baseEnd_3594354 := by
    simpa [prefixWord, tailWord_3594354, baseEnd_3594354] using wordTrace_append hprefix tailTrace_3594354
  have hstable : (prefixWord ++ tailWord_3594354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594354).length < 2 ^ (prefixWord ++ tailWord_3594354).sum := by decide
  have hdescent : baseEnd_3594354 < baseStart_3594354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594388 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3594388 : Nat := 118140960795 + 3594388 * 2 ^ 59
def prefixEnd_3594388 : Nat := 4983230072969 + 3 ^ 40 * 3594388 * 2
def baseEnd_3594388 : Nat := 1845648702752988174119717

theorem tailTrace_3594388 : CollatzResearch.WordTrace tailWord_3594388 prefixEnd_3594388 1845648702752988174119717 := by
  unfold tailWord_3594388
  simp only [CollatzResearch.WordTrace]
  refine ⟨65549050251076811721307909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87398733668102415628410545 65549050251076811721307909)
  ·
    refine ⟨12290446922076902197745233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65549050251076811721307909 12290446922076902197745233)
    ·
      refine ⟨9217835191557676648308925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12290446922076902197745233 9217835191557676648308925)
      ·
        refine ⟨3456688196834128743115847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9217835191557676648308925 3456688196834128743115847)
        ·
          refine ⟨5185032295251193114673771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456688196834128743115847 5185032295251193114673771)
          ·
            refine ⟨7777548442876789672010657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185032295251193114673771 7777548442876789672010657)
            ·
              refine ⟨5833161332157592254007993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7777548442876789672010657 5833161332157592254007993)
              ·
                refine ⟨4374870999118194190505995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833161332157592254007993 4374870999118194190505995)
                ·
                  refine ⟨6562306498677291285758993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374870999118194190505995 6562306498677291285758993)
                  ·
                    refine ⟨4921729874007968464319245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562306498677291285758993 4921729874007968464319245)
                    ·
                      refine ⟨1845648702752988174119717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4921729874007968464319245 1845648702752988174119717)
                      ·
                        rfl

theorem cell23_3594388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3594388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594388 prefixEnd_3594388 := by exact prefixLift 3594388
  have htrace : WordTrace (prefixWord ++ tailWord_3594388) baseStart_3594388 baseEnd_3594388 := by
    simpa [prefixWord, tailWord_3594388, baseEnd_3594388] using wordTrace_append hprefix tailTrace_3594388
  have hstable : (prefixWord ++ tailWord_3594388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594388).length < 2 ^ (prefixWord ++ tailWord_3594388).sum := by decide
  have hdescent : baseEnd_3594388 < baseStart_3594388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594424 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_3594424 : Nat := 118140960795 + 3594424 * 2 ^ 59
def prefixEnd_3594424 : Nat := 4983230072969 + 3 ^ 40 * 3594424 * 2
def baseEnd_3594424 : Nat := 1845667188056550033269551

theorem tailTrace_3594424 : CollatzResearch.WordTrace tailWord_3594424 prefixEnd_3594424 1845667188056550033269551 := by
  unfold tailWord_3594424
  simp only [CollatzResearch.WordTrace]
  refine ⟨65549706765011600795463163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87399609020015467727284217 65549706765011600795463163)
  ·
    refine ⟨98324560147517401193194745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65549706765011600795463163 98324560147517401193194745)
    ·
      refine ⟨73743420110638050894896059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98324560147517401193194745 73743420110638050894896059)
      ·
        refine ⟨110615130165957076342344089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73743420110638050894896059 110615130165957076342344089)
        ·
          refine ⟨82961347624467807256758067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110615130165957076342344089 82961347624467807256758067)
          ·
            refine ⟨124442021436701710885137101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82961347624467807256758067 124442021436701710885137101)
            ·
              refine ⟨46665758038763141581926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124442021436701710885137101 46665758038763141581926413)
              ·
                refine ⟨17499659264536178093222405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46665758038763141581926413 17499659264536178093222405)
                ·
                  refine ⟨3281186112100533392479201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17499659264536178093222405 3281186112100533392479201)
                  ·
                    refine ⟨2460889584075400044359401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3281186112100533392479201 2460889584075400044359401)
                    ·
                      refine ⟨1845667188056550033269551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2460889584075400044359401 1845667188056550033269551)
                      ·
                        rfl

theorem cell23_3594424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_3594424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594424 prefixEnd_3594424 := by exact prefixLift 3594424
  have htrace : WordTrace (prefixWord ++ tailWord_3594424) baseStart_3594424 baseEnd_3594424 := by
    simpa [prefixWord, tailWord_3594424, baseEnd_3594424] using wordTrace_append hprefix tailTrace_3594424
  have hstable : (prefixWord ++ tailWord_3594424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594424).length < 2 ^ (prefixWord ++ tailWord_3594424).sum := by decide
  have hdescent : baseEnd_3594424 < baseStart_3594424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594497 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3594497 : Nat := 118140960795 + 3594497 * 2 ^ 59
def prefixEnd_3594497 : Nat := 4983230072969 + 3 ^ 40 * 3594497 * 2
def baseEnd_3594497 : Nat := 1845704672144328247656715

theorem tailTrace_3594497 : CollatzResearch.WordTrace tailWord_3594497 prefixEnd_3594497 1845704672144328247656715 := by
  unfold tailWord_3594497
  simp only [CollatzResearch.WordTrace]
  refine ⟨131102076058758735058333745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87401384039172490038889163 131102076058758735058333745)
  ·
    refine ⟨98326557044069051293750309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131102076058758735058333745 98326557044069051293750309)
    ·
      refine ⟨18436229445762947117578183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98326557044069051293750309 18436229445762947117578183)
      ·
        refine ⟨27654344168644420676367275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436229445762947117578183 27654344168644420676367275)
        ·
          refine ⟨41481516252966631014550913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27654344168644420676367275 41481516252966631014550913)
          ·
            refine ⟨31111137189724973260913185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41481516252966631014550913 31111137189724973260913185)
            ·
              refine ⟨23333352892293729945684889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31111137189724973260913185 23333352892293729945684889)
              ·
                refine ⟨17500014669220297459263667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23333352892293729945684889 17500014669220297459263667)
                ·
                  refine ⟨26250022003830446188895501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17500014669220297459263667 26250022003830446188895501)
                  ·
                    refine ⟨9843758251436417320835813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26250022003830446188895501 9843758251436417320835813)
                    ·
                      refine ⟨1845704672144328247656715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9843758251436417320835813 1845704672144328247656715)
                      ·
                        rfl

theorem cell23_3594497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3594497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594497 prefixEnd_3594497 := by exact prefixLift 3594497
  have htrace : WordTrace (prefixWord ++ tailWord_3594497) baseStart_3594497 baseEnd_3594497 := by
    simpa [prefixWord, tailWord_3594497, baseEnd_3594497] using wordTrace_append hprefix tailTrace_3594497
  have hstable : (prefixWord ++ tailWord_3594497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594497).length < 2 ^ (prefixWord ++ tailWord_3594497).sum := by decide
  have hdescent : baseEnd_3594497 < baseStart_3594497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594527 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3594527 : Nat := 118140960795 + 3594527 * 2 ^ 59
def prefixEnd_3594527 : Nat := 4983230072969 + 3 ^ 40 * 3594527 * 2
def baseEnd_3594527 : Nat := 1845720076563963130281577

theorem tailTrace_3594527 : CollatzResearch.WordTrace tailWord_3594527 prefixEnd_3594527 1845720076563963130281577 := by
  unfold tailWord_3594527
  simp only [CollatzResearch.WordTrace]
  refine ⟨131103170248650050181925835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87402113499100033454617223 131103170248650050181925835)
  ·
    refine ⟨196654755372975075272888753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131103170248650050181925835 196654755372975075272888753)
    ·
      refine ⟨147491066529731306454666565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196654755372975075272888753 147491066529731306454666565)
      ·
        refine ⟨27654574974324619960249981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147491066529731306454666565 27654574974324619960249981)
        ·
          refine ⟨10370465615371732485093743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27654574974324619960249981 10370465615371732485093743)
          ·
            refine ⟨15555698423057598727640615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370465615371732485093743 15555698423057598727640615)
            ·
              refine ⟨23333547634586398091460923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555698423057598727640615 23333547634586398091460923)
              ·
                refine ⟨35000321451879597137191385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333547634586398091460923 35000321451879597137191385)
                ·
                  refine ⟨26250241088909697852893539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35000321451879597137191385 26250241088909697852893539)
                  ·
                    refine ⟨39375361633364546779340309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26250241088909697852893539 39375361633364546779340309)
                    ·
                      refine ⟨1845720076563963130281577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39375361633364546779340309 1845720076563963130281577)
                      ·
                        rfl

theorem cell23_3594527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3594527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594527 prefixEnd_3594527 := by exact prefixLift 3594527
  have htrace : WordTrace (prefixWord ++ tailWord_3594527) baseStart_3594527 baseEnd_3594527 := by
    simpa [prefixWord, tailWord_3594527, baseEnd_3594527] using wordTrace_append hprefix tailTrace_3594527
  have hstable : (prefixWord ++ tailWord_3594527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594527).length < 2 ^ (prefixWord ++ tailWord_3594527).sum := by decide
  have hdescent : baseEnd_3594527 < baseStart_3594527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594607 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_3594607 : Nat := 118140960795 + 3594607 * 2 ^ 59
def prefixEnd_3594607 : Nat := 4983230072969 + 3 ^ 40 * 3594607 * 2
def baseEnd_3594607 : Nat := 1845761155016322817281209

theorem tailTrace_3594607 : CollatzResearch.WordTrace tailWord_3594607 prefixEnd_3594607 1845761155016322817281209 := by
  unfold tailWord_3594607
  simp only [CollatzResearch.WordTrace]
  refine ⟨131106088088360223844838075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87404058725573482563225383 131106088088360223844838075)
  ·
    refine ⟨196659132132540335767257113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131106088088360223844838075 196659132132540335767257113)
    ·
      refine ⟨147494349099405251825442835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196659132132540335767257113 147494349099405251825442835)
      ·
        refine ⟨221241523649107877738164253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147494349099405251825442835 221241523649107877738164253)
        ·
          refine ⟨82965571368415454151811595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221241523649107877738164253 82965571368415454151811595)
          ·
            refine ⟨124448357052623181227717393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82965571368415454151811595 124448357052623181227717393)
            ·
              refine ⟨93336267789467385920788045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124448357052623181227717393 93336267789467385920788045)
              ·
                refine ⟨35001100421050269720295517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93336267789467385920788045 35001100421050269720295517)
                ·
                  refine ⟨13125412657893851145110819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35001100421050269720295517 13125412657893851145110819)
                  ·
                    refine ⟨19688118986840776717666229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13125412657893851145110819 19688118986840776717666229)
                    ·
                      refine ⟨1845761155016322817281209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19688118986840776717666229 1845761155016322817281209)
                      ·
                        rfl

theorem cell23_3594607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_3594607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594607 prefixEnd_3594607 := by exact prefixLift 3594607
  have htrace : WordTrace (prefixWord ++ tailWord_3594607) baseStart_3594607 baseEnd_3594607 := by
    simpa [prefixWord, tailWord_3594607, baseEnd_3594607] using wordTrace_append hprefix tailTrace_3594607
  have hstable : (prefixWord ++ tailWord_3594607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594607).length < 2 ^ (prefixWord ++ tailWord_3594607).sum := by decide
  have hdescent : baseEnd_3594607 < baseStart_3594607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594621 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_3594621 : Nat := 118140960795 + 3594621 * 2 ^ 59
def prefixEnd_3594621 : Nat := 4983230072969 + 3 ^ 40 * 3594621 * 2
def baseEnd_3594621 : Nat := 1845768343745485762506145

theorem tailTrace_3594621 : CollatzResearch.WordTrace tailWord_3594621 prefixEnd_3594621 1845768343745485762506145 := by
  unfold tailWord_3594621
  simp only [CollatzResearch.WordTrace]
  refine ⟨131106598710309504235847717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87404399140206336157231811 131106598710309504235847717)
  ·
    refine ⟨24582487258183032044221447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131106598710309504235847717 24582487258183032044221447)
    ·
      refine ⟨36873730887274548066332171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24582487258183032044221447 36873730887274548066332171)
      ·
        refine ⟨55310596330911822099498257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36873730887274548066332171 55310596330911822099498257)
        ·
          refine ⟨41482947248183866574623693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55310596330911822099498257 41482947248183866574623693)
          ·
            refine ⟨15556105218068949965483885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41482947248183866574623693 15556105218068949965483885)
            ·
              refine ⟨5833539456775856237056457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15556105218068949965483885 5833539456775856237056457)
              ·
                refine ⟨4375154592581892177792343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833539456775856237056457 4375154592581892177792343)
                ·
                  refine ⟨6562731888872838266688515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375154592581892177792343 6562731888872838266688515)
                  ·
                    refine ⟨9844097833309257400032773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562731888872838266688515 9844097833309257400032773)
                    ·
                      refine ⟨1845768343745485762506145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9844097833309257400032773 1845768343745485762506145)
                      ·
                        rfl

theorem cell23_3594621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_3594621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594621 prefixEnd_3594621 := by exact prefixLift 3594621
  have htrace : WordTrace (prefixWord ++ tailWord_3594621) baseStart_3594621 baseEnd_3594621 := by
    simpa [prefixWord, tailWord_3594621, baseEnd_3594621] using wordTrace_append hprefix tailTrace_3594621
  have hstable : (prefixWord ++ tailWord_3594621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594621).length < 2 ^ (prefixWord ++ tailWord_3594621).sum := by decide
  have hdescent : baseEnd_3594621 < baseStart_3594621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594644 : List Nat := [2, 4, 2, 1, 3, 11]
def baseStart_3594644 : Nat := 118140960795 + 3594644 * 2 ^ 59
def prefixEnd_3594644 : Nat := 4983230072969 + 3 ^ 40 * 3594644 * 2
def baseEnd_3594644 : Nat := 7595803102059831985673

theorem tailTrace_3594644 : CollatzResearch.WordTrace tailWord_3594644 prefixEnd_3594644 7595803102059831985673 := by
  unfold tailWord_3594644
  simp only [CollatzResearch.WordTrace]
  refine ⟨65553718794613089581967493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87404958392817452775956657 65553718794613089581967493)
  ·
    refine ⟨12291322273989954296618905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65553718794613089581967493 12291322273989954296618905)
    ·
      refine ⟨9218491705492465722464179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12291322273989954296618905 9218491705492465722464179)
      ·
        refine ⟨13827737558238698583696269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218491705492465722464179 13827737558238698583696269)
        ·
          refine ⟨5185401584339511968886101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13827737558238698583696269 5185401584339511968886101)
          ·
            refine ⟨7595803102059831985673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5185401584339511968886101 7595803102059831985673)
            ·
              rfl

theorem cell23_3594644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 11].length) (baseStart_3594644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594644 prefixEnd_3594644 := by exact prefixLift 3594644
  have htrace : WordTrace (prefixWord ++ tailWord_3594644) baseStart_3594644 baseEnd_3594644 := by
    simpa [prefixWord, tailWord_3594644, baseEnd_3594644] using wordTrace_append hprefix tailTrace_3594644
  have hstable : (prefixWord ++ tailWord_3594644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594644).length < 2 ^ (prefixWord ++ tailWord_3594644).sum := by decide
  have hdescent : baseEnd_3594644 < baseStart_3594644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594648 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_3594648 : Nat := 118140960795 + 3594648 * 2 ^ 59
def prefixEnd_3594648 : Nat := 4983230072969 + 3 ^ 40 * 3594648 * 2
def baseEnd_3594648 : Nat := 615260735907719052289507

theorem tailTrace_3594648 : CollatzResearch.WordTrace tailWord_3594648 prefixEnd_3594648 615260735907719052289507 := by
  unfold tailWord_3594648
  simp only [CollatzResearch.WordTrace]
  refine ⟨65553791740605843923540299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87405055654141125231387065 65553791740605843923540299)
  ·
    refine ⟨98330687610908765885310449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65553791740605843923540299 98330687610908765885310449)
    ·
      refine ⟨73748015708181574413982837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98330687610908765885310449 73748015708181574413982837)
      ·
        refine ⟨6913876472642022601310891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73748015708181574413982837 6913876472642022601310891)
        ·
          refine ⟨10370814708963033901966337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913876472642022601310891 10370814708963033901966337)
          ·
            refine ⟨7778111031722275426474753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10370814708963033901966337 7778111031722275426474753)
            ·
              refine ⟨5833583273791706569856065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778111031722275426474753 5833583273791706569856065)
              ·
                refine ⟨4375187455343779927392049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833583273791706569856065 4375187455343779927392049)
                ·
                  refine ⟨3281390591507834945544037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4375187455343779927392049 3281390591507834945544037)
                  ·
                    refine ⟨615260735907719052289507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281390591507834945544037 615260735907719052289507)
                    ·
                      rfl

theorem cell23_3594648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_3594648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594648 prefixEnd_3594648 := by exact prefixLift 3594648
  have htrace : WordTrace (prefixWord ++ tailWord_3594648) baseStart_3594648 baseEnd_3594648 := by
    simpa [prefixWord, tailWord_3594648, baseEnd_3594648] using wordTrace_append hprefix tailTrace_3594648
  have hstable : (prefixWord ++ tailWord_3594648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594648).length < 2 ^ (prefixWord ++ tailWord_3594648).sum := by decide
  have hdescent : baseEnd_3594648 < baseStart_3594648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594655 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3594655 : Nat := 118140960795 + 3594655 * 2 ^ 59
def prefixEnd_3594655 : Nat := 4983230072969 + 3 ^ 40 * 3594655 * 2
def baseEnd_3594655 : Nat := 1845785802087738629480989

theorem tailTrace_3594655 : CollatzResearch.WordTrace tailWord_3594655 prefixEnd_3594655 1845785802087738629480989 := by
  unfold tailWord_3594655
  simp only [CollatzResearch.WordTrace]
  refine ⟨131107838792186328042585419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87405225861457552028390279 131107838792186328042585419)
  ·
    refine ⟨196661758188279492063878129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131107838792186328042585419 196661758188279492063878129)
    ·
      refine ⟨147496318641209619047908597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196661758188279492063878129 147496318641209619047908597)
      ·
        refine ⟨13827779872613401785741431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147496318641209619047908597 13827779872613401785741431)
        ·
          refine ⟨20741669808920102678612147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827779872613401785741431 20741669808920102678612147)
          ·
            refine ⟨31112504713380154017918221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20741669808920102678612147 31112504713380154017918221)
            ·
              refine ⟨11667189267517557756719333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31112504713380154017918221 11667189267517557756719333)
              ·
                refine ⟨2187597987659542079384875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11667189267517557756719333 2187597987659542079384875)
                ·
                  refine ⟨3281396981489313119077313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187597987659542079384875 3281396981489313119077313)
                  ·
                    refine ⟨2461047736116984839307985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3281396981489313119077313 2461047736116984839307985)
                    ·
                      refine ⟨1845785802087738629480989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461047736116984839307985 1845785802087738629480989)
                      ·
                        rfl

theorem cell23_3594655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3594655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594655 prefixEnd_3594655 := by exact prefixLift 3594655
  have htrace : WordTrace (prefixWord ++ tailWord_3594655) baseStart_3594655 baseEnd_3594655 := by
    simpa [prefixWord, tailWord_3594655, baseEnd_3594655] using wordTrace_append hprefix tailTrace_3594655
  have hstable : (prefixWord ++ tailWord_3594655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594655).length < 2 ^ (prefixWord ++ tailWord_3594655).sum := by decide
  have hdescent : baseEnd_3594655 < baseStart_3594655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594689 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3594689 : Nat := 118140960795 + 3594689 * 2 ^ 59
def prefixEnd_3594689 : Nat := 4983230072969 + 3 ^ 40 * 3594689 * 2
def baseEnd_3594689 : Nat := 1845803260429991496455833

theorem tailTrace_3594689 : CollatzResearch.WordTrace tailWord_3594689 prefixEnd_3594689 1845803260429991496455833 := by
  unfold tailWord_3594689
  simp only [CollatzResearch.WordTrace]
  refine ⟨131109078874063151849323121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87406052582708767899548747 131109078874063151849323121)
  ·
    refine ⟨98331809155547363886992341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131109078874063151849323121 98331809155547363886992341)
    ·
      refine ⟨2304651777083141341101383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98331809155547363886992341 2304651777083141341101383)
      ·
        refine ⟨3456977665624712011652075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304651777083141341101383 3456977665624712011652075)
        ·
          refine ⟨5185466498437068017478113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456977665624712011652075 5185466498437068017478113)
          ·
            refine ⟨3889099873827801013108585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185466498437068017478113 3889099873827801013108585)
            ·
              refine ⟨2916824905370850759831439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889099873827801013108585 2916824905370850759831439)
              ·
                refine ⟨4375237358056276139747159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916824905370850759831439 4375237358056276139747159)
                ·
                  refine ⟨6562856037084414209620739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375237358056276139747159 6562856037084414209620739)
                  ·
                    refine ⟨9844284055626621314431109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562856037084414209620739 9844284055626621314431109)
                    ·
                      refine ⟨1845803260429991496455833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9844284055626621314431109 1845803260429991496455833)
                      ·
                        rfl

theorem cell23_3594689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3594689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594689 prefixEnd_3594689 := by exact prefixLift 3594689
  have htrace : WordTrace (prefixWord ++ tailWord_3594689) baseStart_3594689 baseEnd_3594689 := by
    simpa [prefixWord, tailWord_3594689, baseEnd_3594689] using wordTrace_append hprefix tailTrace_3594689
  have hstable : (prefixWord ++ tailWord_3594689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594689).length < 2 ^ (prefixWord ++ tailWord_3594689).sum := by decide
  have hdescent : baseEnd_3594689 < baseStart_3594689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594692 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3594692 : Nat := 118140960795 + 3594692 * 2 ^ 59
def prefixEnd_3594692 : Nat := 4983230072969 + 3 ^ 40 * 3594692 * 2
def baseEnd_3594692 : Nat := 1845804800871954984718319

theorem tailTrace_3594692 : CollatzResearch.WordTrace tailWord_3594692 prefixEnd_3594692 1845804800871954984718319 := by
  unfold tailWord_3594692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65554594146526141680841165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87406125528701522241121553 65554594146526141680841165)
  ·
    refine ⟨24582972804947303130315437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65554594146526141680841165 24582972804947303130315437)
    ·
      refine ⟨9218614801855238673868289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24582972804947303130315437 9218614801855238673868289)
      ·
        refine ⟨6913961101391429005401217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9218614801855238673868289 6913961101391429005401217)
        ·
          refine ⟨5185470826043571754050913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913961101391429005401217 5185470826043571754050913)
          ·
            refine ⟨3889103119532678815538185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185470826043571754050913 3889103119532678815538185)
            ·
              refine ⟨2916827339649509111653639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889103119532678815538185 2916827339649509111653639)
              ·
                refine ⟨4375241009474263667480459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916827339649509111653639 4375241009474263667480459)
                ·
                  refine ⟨6562861514211395501220689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375241009474263667480459 6562861514211395501220689)
                  ·
                    refine ⟨4922146135658546625915517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6562861514211395501220689 4922146135658546625915517)
                    ·
                      refine ⟨1845804800871954984718319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922146135658546625915517 1845804800871954984718319)
                      ·
                        rfl

theorem cell23_3594692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3594692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594692 prefixEnd_3594692 := by exact prefixLift 3594692
  have htrace : WordTrace (prefixWord ++ tailWord_3594692) baseStart_3594692 baseEnd_3594692 := by
    simpa [prefixWord, tailWord_3594692, baseEnd_3594692] using wordTrace_append hprefix tailTrace_3594692
  have hstable : (prefixWord ++ tailWord_3594692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594692).length < 2 ^ (prefixWord ++ tailWord_3594692).sum := by decide
  have hdescent : baseEnd_3594692 < baseStart_3594692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594698 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_3594698 : Nat := 118140960795 + 3594698 * 2 ^ 59
def prefixEnd_3594698 : Nat := 4983230072969 + 3 ^ 40 * 3594698 * 2
def baseEnd_3594698 : Nat := 1845807881755881961243291

theorem tailTrace_3594698 : CollatzResearch.WordTrace tailWord_3594698 prefixEnd_3594698 1845807881755881961243291 := by
  unfold tailWord_3594698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32777351782757636596600187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87406271420687030924267165 32777351782757636596600187)
  ·
    refine ⟨49166027674136454894900281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32777351782757636596600187 49166027674136454894900281)
    ·
      refine ⟨36874520755602341171175211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49166027674136454894900281 36874520755602341171175211)
      ·
        refine ⟨55311781133403511756762817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874520755602341171175211 55311781133403511756762817)
        ·
          refine ⟨41483835850052633817572113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55311781133403511756762817 41483835850052633817572113)
          ·
            refine ⟨31112876887539475363179085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41483835850052633817572113 31112876887539475363179085)
            ·
              refine ⟨11667328832827303261192157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31112876887539475363179085 11667328832827303261192157)
              ·
                refine ⟨4375248312310238722947059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11667328832827303261192157 4375248312310238722947059)
                ·
                  refine ⟨6562872468465358084420589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375248312310238722947059 6562872468465358084420589)
                  ·
                    refine ⟨2461077175674509281657721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6562872468465358084420589 2461077175674509281657721)
                    ·
                      refine ⟨1845807881755881961243291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461077175674509281657721 1845807881755881961243291)
                      ·
                        rfl

theorem cell23_3594698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_3594698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594698 prefixEnd_3594698 := by exact prefixLift 3594698
  have htrace : WordTrace (prefixWord ++ tailWord_3594698) baseStart_3594698 baseEnd_3594698 := by
    simpa [prefixWord, tailWord_3594698, baseEnd_3594698] using wordTrace_append hprefix tailTrace_3594698
  have hstable : (prefixWord ++ tailWord_3594698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594698).length < 2 ^ (prefixWord ++ tailWord_3594698).sum := by decide
  have hdescent : baseEnd_3594698 < baseStart_3594698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594722 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3594722 : Nat := 118140960795 + 3594722 * 2 ^ 59
def prefixEnd_3594722 : Nat := 4983230072969 + 3 ^ 40 * 3594722 * 2
def baseEnd_3594722 : Nat := 1845820205291589867343181

theorem tailTrace_3594722 : CollatzResearch.WordTrace tailWord_3594722 prefixEnd_3594722 1845820205291589867343181 := by
  unfold tailWord_3594722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32777570620735899621318605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87406854988629065656849613 32777570620735899621318605)
  ·
    refine ⟨12291588982775962357994477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32777570620735899621318605 12291588982775962357994477)
    ·
      refine ⟨4609345868540985884247929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12291588982775962357994477 4609345868540985884247929)
      ·
        refine ⟨3457009401405739413185947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609345868540985884247929 3457009401405739413185947)
        ·
          refine ⟨5185514102108609119778921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457009401405739413185947 5185514102108609119778921)
          ·
            refine ⟨3889135576581456839834191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185514102108609119778921 3889135576581456839834191)
            ·
              refine ⟨5833703364872185259751287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889135576581456839834191 5833703364872185259751287)
              ·
                refine ⟨8750555047308277889626931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833703364872185259751287 8750555047308277889626931)
                ·
                  refine ⟨13125832570962416834440397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750555047308277889626931 13125832570962416834440397)
                  ·
                    refine ⟨4922187214110906312915149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13125832570962416834440397 4922187214110906312915149)
                    ·
                      refine ⟨1845820205291589867343181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922187214110906312915149 1845820205291589867343181)
                      ·
                        rfl

theorem cell23_3594722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3594722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594722 prefixEnd_3594722 := by exact prefixLift 3594722
  have htrace : WordTrace (prefixWord ++ tailWord_3594722) baseStart_3594722 baseEnd_3594722 := by
    simpa [prefixWord, tailWord_3594722, baseEnd_3594722] using wordTrace_append hprefix tailTrace_3594722
  have hstable : (prefixWord ++ tailWord_3594722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594722).length < 2 ^ (prefixWord ++ tailWord_3594722).sum := by decide
  have hdescent : baseEnd_3594722 < baseStart_3594722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594728 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3594728 : Nat := 118140960795 + 3594728 * 2 ^ 59
def prefixEnd_3594728 : Nat := 4983230072969 + 3 ^ 40 * 3594728 * 2
def baseEnd_3594728 : Nat := 1845823286175516843868153

theorem tailTrace_3594728 : CollatzResearch.WordTrace tailWord_3594728 prefixEnd_3594728 1845823286175516843868153 := by
  unfold tailWord_3594728
  simp only [CollatzResearch.WordTrace]
  refine ⟨65555250660460930754996419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87407000880614574339995225 65555250660460930754996419)
  ·
    refine ⟨98332875990691396132494629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65555250660460930754996419 98332875990691396132494629)
    ·
      refine ⟨18437414248254636774842743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98332875990691396132494629 18437414248254636774842743)
      ·
        refine ⟨27656121372381955162264115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18437414248254636774842743 27656121372381955162264115)
        ·
          refine ⟨41484182058572932743396173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27656121372381955162264115 41484182058572932743396173)
          ·
            refine ⟨15556568271964849778773565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41484182058572932743396173 15556568271964849778773565)
            ·
              refine ⟨5833713101986818667040087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15556568271964849778773565 5833713101986818667040087)
              ·
                refine ⟨8750569652980228000560131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833713101986818667040087 8750569652980228000560131)
                ·
                  refine ⟨13125854479470342000840197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8750569652980228000560131 13125854479470342000840197)
                  ·
                    refine ⟨2461097714900689125157537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13125854479470342000840197 2461097714900689125157537)
                    ·
                      refine ⟨1845823286175516843868153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461097714900689125157537 1845823286175516843868153)
                      ·
                        rfl

theorem cell23_3594728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3594728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594728 prefixEnd_3594728 := by exact prefixLift 3594728
  have htrace : WordTrace (prefixWord ++ tailWord_3594728) baseStart_3594728 baseEnd_3594728 := by
    simpa [prefixWord, tailWord_3594728, baseEnd_3594728] using wordTrace_append hprefix tailTrace_3594728
  have hstable : (prefixWord ++ tailWord_3594728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594728).length < 2 ^ (prefixWord ++ tailWord_3594728).sum := by decide
  have hdescent : baseEnd_3594728 < baseStart_3594728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594771 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 5, 2]
def baseStart_3594771 : Nat := 118140960795 + 3594771 * 2 ^ 59
def prefixEnd_3594771 : Nat := 4983230072969 + 3 ^ 40 * 3594771 * 2
def baseEnd_3594771 : Nat := 1845845365843660175630455

theorem tailTrace_3594771 : CollatzResearch.WordTrace tailWord_3594771 prefixEnd_3594771 1845845365843660175630455 := by
  unfold tailWord_3594771
  simp only [CollatzResearch.WordTrace]
  refine ⟨131112069659766079853808167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87408046439844053235872111 131112069659766079853808167)
  ·
    refine ⟨196668104489649119780712251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131112069659766079853808167 196668104489649119780712251)
    ·
      refine ⟨295002156734473679671068377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196668104489649119780712251 295002156734473679671068377)
      ·
        refine ⟨221251617550855259753301283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295002156734473679671068377 221251617550855259753301283)
        ·
          refine ⟨331877426326282889629951925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221251617550855259753301283 331877426326282889629951925)
          ·
            refine ⟨31113508718089020902807993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331877426326282889629951925 31113508718089020902807993)
            ·
              refine ⟨23335131538566765677105995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31113508718089020902807993 23335131538566765677105995)
              ·
                refine ⟨35002697307850148515658993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23335131538566765677105995 35002697307850148515658993)
                ·
                  refine ⟨26252022980887611386744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35002697307850148515658993 26252022980887611386744245)
                  ·
                    refine ⟨2461127154458213567507273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26252022980887611386744245 2461127154458213567507273)
                    ·
                      refine ⟨1845845365843660175630455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461127154458213567507273 1845845365843660175630455)
                      ·
                        rfl

theorem cell23_3594771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5, 2].length) (baseStart_3594771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594771 prefixEnd_3594771 := by exact prefixLift 3594771
  have htrace : WordTrace (prefixWord ++ tailWord_3594771) baseStart_3594771 baseEnd_3594771 := by
    simpa [prefixWord, tailWord_3594771, baseEnd_3594771] using wordTrace_append hprefix tailTrace_3594771
  have hstable : (prefixWord ++ tailWord_3594771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594771).length < 2 ^ (prefixWord ++ tailWord_3594771).sum := by decide
  have hdescent : baseEnd_3594771 < baseStart_3594771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594801 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3594801 : Nat := 118140960795 + 3594801 * 2 ^ 59
def prefixEnd_3594801 : Nat := 4983230072969 + 3 ^ 40 * 3594801 * 2
def baseEnd_3594801 : Nat := 1845860770263295058255317

theorem tailTrace_3594801 : CollatzResearch.WordTrace tailWord_3594801 prefixEnd_3594801 1845860770263295058255317 := by
  unfold tailWord_3594801
  simp only [CollatzResearch.WordTrace]
  refine ⟨131113163849657394977400257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87408775899771596651600171 131113163849657394977400257)
  ·
    refine ⟨98334872887243046233050193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131113163849657394977400257 98334872887243046233050193)
    ·
      refine ⟨73751154665432284674787645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98334872887243046233050193 73751154665432284674787645)
      ·
        refine ⟨27656682999537106753045367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73751154665432284674787645 27656682999537106753045367)
        ·
          refine ⟨41485024499305660129568051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27656682999537106753045367 41485024499305660129568051)
          ·
            refine ⟨62227536748958490194352077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41485024499305660129568051 62227536748958490194352077)
            ·
              refine ⟨23335326280859433822882029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62227536748958490194352077 23335326280859433822882029)
              ·
                refine ⟨8750747355322287683580761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23335326280859433822882029 8750747355322287683580761)
                ·
                  refine ⟨6563060516491715762685571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8750747355322287683580761 6563060516491715762685571)
                  ·
                    refine ⟨9844590774737573644028357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563060516491715762685571 9844590774737573644028357)
                    ·
                      refine ⟨1845860770263295058255317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9844590774737573644028357 1845860770263295058255317)
                      ·
                        rfl

theorem cell23_3594801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3594801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594801 prefixEnd_3594801 := by exact prefixLift 3594801
  have htrace : WordTrace (prefixWord ++ tailWord_3594801) baseStart_3594801 baseEnd_3594801 := by
    simpa [prefixWord, tailWord_3594801, baseEnd_3594801] using wordTrace_append hprefix tailTrace_3594801
  have hstable : (prefixWord ++ tailWord_3594801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594801).length < 2 ^ (prefixWord ++ tailWord_3594801).sum := by decide
  have hdescent : baseEnd_3594801 < baseStart_3594801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594824 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 8]
def baseStart_3594824 : Nat := 118140960795 + 3594824 * 2 ^ 59
def prefixEnd_3594824 : Nat := 4983230072969 + 3 ^ 40 * 3594824 * 2
def baseEnd_3594824 : Nat := 205096953368705385363079

theorem tailTrace_3594824 : CollatzResearch.WordTrace tailWord_3594824 prefixEnd_3594824 205096953368705385363079 := by
  unfold tailWord_3594824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65557001364287034952743763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87409335152382713270325017 65557001364287034952743763)
  ·
    refine ⟨98335502046430552429115645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65557001364287034952743763 98335502046430552429115645)
    ·
      refine ⟨36875813267411457160918367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98335502046430552429115645 36875813267411457160918367)
      ·
        refine ⟨55313719901117185741377551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36875813267411457160918367 55313719901117185741377551)
        ·
          refine ⟨82970579851675778612066327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55313719901117185741377551 82970579851675778612066327)
          ·
            refine ⟨124455869777513667918099491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82970579851675778612066327 124455869777513667918099491)
            ·
              refine ⟨186683804666270501877149237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124455869777513667918099491 186683804666270501877149237)
              ·
                refine ⟨17501606687462859550982741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186683804666270501877149237 17501606687462859550982741)
                ·
                  refine ⟨205096953368705385363079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17501606687462859550982741 205096953368705385363079)
                  ·
                    rfl

theorem cell23_3594824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_3594824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594824 prefixEnd_3594824 := by exact prefixLift 3594824
  have htrace : WordTrace (prefixWord ++ tailWord_3594824) baseStart_3594824 baseEnd_3594824 := by
    simpa [prefixWord, tailWord_3594824, baseEnd_3594824] using wordTrace_append hprefix tailTrace_3594824
  have hstable : (prefixWord ++ tailWord_3594824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594824).length < 2 ^ (prefixWord ++ tailWord_3594824).sum := by decide
  have hdescent : baseEnd_3594824 < baseStart_3594824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594862 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3594862 : Nat := 118140960795 + 3594862 * 2 ^ 59
def prefixEnd_3594862 : Nat := 4983230072969 + 3 ^ 40 * 3594862 * 2
def baseEnd_3594862 : Nat := 615297364194406439864179

theorem tailTrace_3594862 : CollatzResearch.WordTrace tailWord_3594862 prefixEnd_3594862 615297364194406439864179 := by
  unfold tailWord_3594862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389423587804550299421355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87410259134957601596913893 16389423587804550299421355)
  ·
    refine ⟨24584135381706825449132033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16389423587804550299421355 24584135381706825449132033)
    ·
      refine ⟨18438101536280119086849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24584135381706825449132033 18438101536280119086849025)
      ·
        refine ⟨13828576152210089315136769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18438101536280119086849025 13828576152210089315136769)
        ·
          refine ⟨10371432114157566986352577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13828576152210089315136769 10371432114157566986352577)
          ·
            refine ⟨7778574085618175239764433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10371432114157566986352577 7778574085618175239764433)
            ·
              refine ⟨5833930564213631429823325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778574085618175239764433 5833930564213631429823325)
              ·
                refine ⟨2187723961580111786183747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5833930564213631429823325 2187723961580111786183747)
                ·
                  refine ⟨3281585942370167679275621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187723961580111786183747 3281585942370167679275621)
                  ·
                    refine ⟨615297364194406439864179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281585942370167679275621 615297364194406439864179)
                    ·
                      rfl

theorem cell23_3594862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3594862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594862 prefixEnd_3594862 := by exact prefixLift 3594862
  have htrace : WordTrace (prefixWord ++ tailWord_3594862) baseStart_3594862 baseEnd_3594862 := by
    simpa [prefixWord, tailWord_3594862, baseEnd_3594862] using wordTrace_append hprefix tailTrace_3594862
  have hstable : (prefixWord ++ tailWord_3594862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594862).length < 2 ^ (prefixWord ++ tailWord_3594862).sum := by decide
  have hdescent : baseEnd_3594862 < baseStart_3594862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594885 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_3594885 : Nat := 118140960795 + 3594885 * 2 ^ 59
def prefixEnd_3594885 : Nat := 4983230072969 + 3 ^ 40 * 3594885 * 2
def baseEnd_3594885 : Nat := 1845903902638272729604931

theorem tailTrace_3594885 : CollatzResearch.WordTrace tailWord_3594885 prefixEnd_3594885 1845903902638272729604931 := by
  unfold tailWord_3594885
  simp only [CollatzResearch.WordTrace]
  refine ⟨131116227581353077323458109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87410818387568718215638739 131116227581353077323458109)
  ·
    refine ⟨49168585343007403996296791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131116227581353077323458109 49168585343007403996296791)
    ·
      refine ⟨73752878014511105994445187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49168585343007403996296791 73752878014511105994445187)
      ·
        refine ⟨110629317021766658991667781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73752878014511105994445187 110629317021766658991667781)
        ·
          refine ⟨20742996941581248560937709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110629317021766658991667781 20742996941581248560937709)
          ·
            refine ⟨7778623853092968210351641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20742996941581248560937709 7778623853092968210351641)
            ·
              refine ⟨5833967889819726157763731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778623853092968210351641 5833967889819726157763731)
              ·
                refine ⟨8750951834729589236645597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833967889819726157763731 8750951834729589236645597)
                ·
                  refine ⟨3281606938023595963742099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8750951834729589236645597 3281606938023595963742099)
                  ·
                    refine ⟨4922410407035393945613149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281606938023595963742099 4922410407035393945613149)
                    ·
                      refine ⟨1845903902638272729604931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4922410407035393945613149 1845903902638272729604931)
                      ·
                        rfl

theorem cell23_3594885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_3594885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594885 prefixEnd_3594885 := by exact prefixLift 3594885
  have htrace : WordTrace (prefixWord ++ tailWord_3594885) baseStart_3594885 baseEnd_3594885 := by
    simpa [prefixWord, tailWord_3594885, baseEnd_3594885] using wordTrace_append hprefix tailTrace_3594885
  have hstable : (prefixWord ++ tailWord_3594885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594885).length < 2 ^ (prefixWord ++ tailWord_3594885).sum := by decide
  have hdescent : baseEnd_3594885 < baseStart_3594885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594891 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4]
def baseStart_3594891 : Nat := 118140960795 + 3594891 * 2 ^ 59
def prefixEnd_3594891 : Nat := 4983230072969 + 3 ^ 40 * 3594891 * 2
def baseEnd_3594891 : Nat := 1845906983522199706129903

theorem tailTrace_3594891 : CollatzResearch.WordTrace tailWord_3594891 prefixEnd_3594891 1845906983522199706129903 := by
  unfold tailWord_3594891
  simp only [CollatzResearch.WordTrace]
  refine ⟨131116446419331340348176527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87410964279554226898784351 131116446419331340348176527)
  ·
    refine ⟨196674669628997010522264791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131116446419331340348176527 196674669628997010522264791)
    ·
      refine ⟨295012004443495515783397187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196674669628997010522264791 295012004443495515783397187)
      ·
        refine ⟨442518006665243273675095781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295012004443495515783397187 442518006665243273675095781)
        ·
          refine ⟨82972126249733113814080459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442518006665243273675095781 82972126249733113814080459)
          ·
            refine ⟨124458189374599670721120689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82972126249733113814080459 124458189374599670721120689)
            ·
              refine ⟨93343642030949753040840517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124458189374599670721120689 93343642030949753040840517)
              ·
                refine ⟨17501932880803078695157597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93343642030949753040840517 17501932880803078695157597)
                ·
                  refine ⟨6563224830301154510684099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17501932880803078695157597 6563224830301154510684099)
                  ·
                    refine ⟨9844837245451731766026149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563224830301154510684099 9844837245451731766026149)
                    ·
                      refine ⟨1845906983522199706129903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9844837245451731766026149 1845906983522199706129903)
                      ·
                        rfl

theorem cell23_3594891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_3594891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594891 prefixEnd_3594891 := by exact prefixLift 3594891
  have htrace : WordTrace (prefixWord ++ tailWord_3594891) baseStart_3594891 baseEnd_3594891 := by
    simpa [prefixWord, tailWord_3594891, baseEnd_3594891] using wordTrace_append hprefix tailTrace_3594891
  have hstable : (prefixWord ++ tailWord_3594891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594891).length < 2 ^ (prefixWord ++ tailWord_3594891).sum := by decide
  have hdescent : baseEnd_3594891 < baseStart_3594891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594925 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3594925 : Nat := 118140960795 + 3594925 * 2 ^ 59
def prefixEnd_3594925 : Nat := 4983230072969 + 3 ^ 40 * 3594925 * 2
def baseEnd_3594925 : Nat := 1845924441864452573104747

theorem tailTrace_3594925 : CollatzResearch.WordTrace tailWord_3594925 prefixEnd_3594925 1845924441864452573104747 := by
  unfold tailWord_3594925
  simp only [CollatzResearch.WordTrace]
  refine ⟨131117686501208164154914229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87411791000805442769942819 131117686501208164154914229)
  ·
    refine ⟨12292283109488265389523209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131117686501208164154914229 12292283109488265389523209)
    ·
      refine ⟨9219212332116199042142407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292283109488265389523209 9219212332116199042142407)
      ·
        refine ⟨13828818498174298563213611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219212332116199042142407 13828818498174298563213611)
        ·
          refine ⟨20743227747261447844820417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828818498174298563213611 20743227747261447844820417)
          ·
            refine ⟨15557420810446085883615313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20743227747261447844820417 15557420810446085883615313)
            ·
              refine ⟨11668065607834564412711485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15557420810446085883615313 11668065607834564412711485)
              ·
                refine ⟨4375524602937961654766807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11668065607834564412711485 4375524602937961654766807)
                ·
                  refine ⟨6563286904406942482150211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375524602937961654766807 6563286904406942482150211)
                  ·
                    refine ⟨9844930356610413723225317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563286904406942482150211 9844930356610413723225317)
                    ·
                      refine ⟨1845924441864452573104747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9844930356610413723225317 1845924441864452573104747)
                      ·
                        rfl

theorem cell23_3594925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3594925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594925 prefixEnd_3594925 := by exact prefixLift 3594925
  have htrace : WordTrace (prefixWord ++ tailWord_3594925) baseStart_3594925 baseEnd_3594925 := by
    simpa [prefixWord, tailWord_3594925, baseEnd_3594925] using wordTrace_append hprefix tailTrace_3594925
  have hstable : (prefixWord ++ tailWord_3594925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594925).length < 2 ^ (prefixWord ++ tailWord_3594925).sum := by decide
  have hdescent : baseEnd_3594925 < baseStart_3594925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594931 : List Nat := [1, 1, 1, 2, 3, 6, 9]
def baseStart_3594931 : Nat := 118140960795 + 3594931 * 2 ^ 59
def prefixEnd_3594931 : Nat := 4983230072969 + 3 ^ 40 * 3594931 * 2
def baseEnd_3594931 : Nat := 22789228675905920365799

theorem tailTrace_3594931 : CollatzResearch.WordTrace tailWord_3594931 prefixEnd_3594931 22789228675905920365799 := by
  unfold tailWord_3594931
  simp only [CollatzResearch.WordTrace]
  refine ⟨131117905339186427179632647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87411936892790951453088431 131117905339186427179632647)
  ·
    refine ⟨196676858008779640769448971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131117905339186427179632647 196676858008779640769448971)
    ·
      refine ⟨295015287013169461154173457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196676858008779640769448971 295015287013169461154173457)
      ·
        refine ⟨221261465259877095865630093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295015287013169461154173457 221261465259877095865630093)
        ·
          refine ⟨82973049472453910949611285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221261465259877095865630093 82973049472453910949611285)
          ·
            refine ⟨3889361694021277075763029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82973049472453910949611285 3889361694021277075763029)
            ·
              refine ⟨22789228675905920365799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3889361694021277075763029 22789228675905920365799)
              ·
                rfl

theorem cell23_3594931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 9].length) (baseStart_3594931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594931 prefixEnd_3594931 := by exact prefixLift 3594931
  have htrace : WordTrace (prefixWord ++ tailWord_3594931) baseStart_3594931 baseEnd_3594931 := by
    simpa [prefixWord, tailWord_3594931, baseEnd_3594931] using wordTrace_append hprefix tailTrace_3594931
  have hstable : (prefixWord ++ tailWord_3594931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594931).length < 2 ^ (prefixWord ++ tailWord_3594931).sum := by decide
  have hdescent : baseEnd_3594931 < baseStart_3594931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594948 : List Nat := [2, 3, 3, 1, 1, 3, 2, 8]
def baseStart_3594948 : Nat := 118140960795 + 3594948 * 2 ^ 59
def prefixEnd_3594948 : Nat := 4983230072969 + 3 ^ 40 * 3594948 * 2
def baseEnd_3594948 : Nat := 68368009330352073448783

theorem tailTrace_3594948 : CollatzResearch.WordTrace tailWord_3594948 prefixEnd_3594948 68368009330352073448783 := by
  unfold tailWord_3594948
  simp only [CollatzResearch.WordTrace]
  refine ⟨65559262690062419541500749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87412350253416559388667665 65559262690062419541500749)
  ·
    refine ⟨24584723508773407328062781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65559262690062419541500749 24584723508773407328062781)
    ·
      refine ⟨9219271315790027748023543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24584723508773407328062781 9219271315790027748023543)
      ·
        refine ⟨13828906973685041622035315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219271315790027748023543 13828906973685041622035315)
        ·
          refine ⟨20743360460527562433052973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828906973685041622035315 20743360460527562433052973)
          ·
            refine ⟨7778760172697835912394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20743360460527562433052973 7778760172697835912394865)
            ·
              refine ⟨5834070129523376934296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7778760172697835912394865 5834070129523376934296149)
              ·
                refine ⟨68368009330352073448783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5834070129523376934296149 68368009330352073448783)
                ·
                  rfl

theorem cell23_3594948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 8].length) (baseStart_3594948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594948 prefixEnd_3594948 := by exact prefixLift 3594948
  have htrace : WordTrace (prefixWord ++ tailWord_3594948) baseStart_3594948 baseEnd_3594948 := by
    simpa [prefixWord, tailWord_3594948, baseEnd_3594948] using wordTrace_append hprefix tailTrace_3594948
  have hstable : (prefixWord ++ tailWord_3594948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594948).length < 2 ^ (prefixWord ++ tailWord_3594948).sum := by decide
  have hdescent : baseEnd_3594948 < baseStart_3594948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594952 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_3594952 : Nat := 118140960795 + 3594952 * 2 ^ 59
def prefixEnd_3594952 : Nat := 4983230072969 + 3 ^ 40 * 3594952 * 2
def baseEnd_3594952 : Nat := 615312768614041322489041

theorem tailTrace_3594952 : CollatzResearch.WordTrace tailWord_3594952 prefixEnd_3594952 615312768614041322489041 := by
  unfold tailWord_3594952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65559335636055173883073555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87412447514740231844098073 65559335636055173883073555)
  ·
    refine ⟨98339003454082760824610333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65559335636055173883073555 98339003454082760824610333)
    ·
      refine ⟨36877126295281035309228875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98339003454082760824610333 36877126295281035309228875)
      ·
        refine ⟨55315689442921552963843313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36877126295281035309228875 55315689442921552963843313)
        ·
          refine ⟨41486767082191164722882485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55315689442921552963843313 41486767082191164722882485)
          ·
            refine ⟨3889384413955421692770233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41486767082191164722882485 3889384413955421692770233)
            ·
              refine ⟨2917038310466566269577675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889384413955421692770233 2917038310466566269577675)
              ·
                refine ⟨4375557465699849404366513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917038310466566269577675 4375557465699849404366513)
                ·
                  refine ⟨3281668099274887053274885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4375557465699849404366513 3281668099274887053274885)
                  ·
                    refine ⟨615312768614041322489041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3281668099274887053274885 615312768614041322489041)
                    ·
                      rfl

theorem cell23_3594952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_3594952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594952 prefixEnd_3594952 := by exact prefixLift 3594952
  have htrace : WordTrace (prefixWord ++ tailWord_3594952) baseStart_3594952 baseEnd_3594952 := by
    simpa [prefixWord, tailWord_3594952, baseEnd_3594952] using wordTrace_append hprefix tailTrace_3594952
  have hstable : (prefixWord ++ tailWord_3594952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594952).length < 2 ^ (prefixWord ++ tailWord_3594952).sum := by decide
  have hdescent : baseEnd_3594952 < baseStart_3594952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594985 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 1, 3, 2]
def baseStart_3594985 : Nat := 118140960795 + 3594985 * 2 ^ 59
def prefixEnd_3594985 : Nat := 4983230072969 + 3 ^ 40 * 3594985 * 2
def baseEnd_3594985 : Nat := 1845955250703722338354471

theorem tailTrace_3594985 : CollatzResearch.WordTrace tailWord_3594985 prefixEnd_3594985 1845955250703722338354471 := by
  unfold tailWord_3594985
  simp only [CollatzResearch.WordTrace]
  refine ⟨131119874880990794402098409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87413249920660529601398939 131119874880990794402098409)
  ·
    refine ⟨98339906160743095801573807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131119874880990794402098409 98339906160743095801573807)
    ·
      refine ⟨147509859241114643702360711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98339906160743095801573807 147509859241114643702360711)
      ·
        refine ⟨221264788861671965553541067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147509859241114643702360711 221264788861671965553541067)
        ·
          refine ⟨331897183292507948330311601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221264788861671965553541067 331897183292507948330311601)
          ·
            refine ⟨248922887469380961247733701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331897183292507948330311601 248922887469380961247733701)
            ·
              refine ⟨46673041400508930233950069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248922887469380961247733701 46673041400508930233950069)
              ·
                refine ⟨4375597631297712209432819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46673041400508930233950069 4375597631297712209432819)
                ·
                  refine ⟨6563396446946568314149229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375597631297712209432819 6563396446946568314149229)
                  ·
                    refine ⟨2461273667604963117805961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6563396446946568314149229 2461273667604963117805961)
                    ·
                      refine ⟨1845955250703722338354471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2461273667604963117805961 1845955250703722338354471)
                      ·
                        rfl

theorem cell23_3594985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3, 2].length) (baseStart_3594985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594985 prefixEnd_3594985 := by exact prefixLift 3594985
  have htrace : WordTrace (prefixWord ++ tailWord_3594985) baseStart_3594985 baseEnd_3594985 := by
    simpa [prefixWord, tailWord_3594985, baseEnd_3594985] using wordTrace_append hprefix tailTrace_3594985
  have hstable : (prefixWord ++ tailWord_3594985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594985).length < 2 ^ (prefixWord ++ tailWord_3594985).sum := by decide
  have hdescent : baseEnd_3594985 < baseStart_3594985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594998 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3594998 : Nat := 118140960795 + 3594998 * 2 ^ 59
def prefixEnd_3594998 : Nat := 4983230072969 + 3 ^ 40 * 3594998 * 2
def baseEnd_3594998 : Nat := 1845961925952230787491911

theorem tailTrace_3594998 : CollatzResearch.WordTrace tailWord_3594998 prefixEnd_3594998 1845961925952230787491911 := by
  unfold tailWord_3594998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195021814371481101395103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87413566019962465081547765 8195021814371481101395103)
  ·
    refine ⟨12292532721557221652092655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195021814371481101395103 12292532721557221652092655)
    ·
      refine ⟨18438799082335832478138983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12292532721557221652092655 18438799082335832478138983)
      ·
        refine ⟨27658198623503748717208475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18438799082335832478138983 27658198623503748717208475)
        ·
          refine ⟨41487297935255623075812713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27658198623503748717208475 41487297935255623075812713)
          ·
            refine ⟨31115473451441717306859535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41487297935255623075812713 31115473451441717306859535)
            ·
              refine ⟨46673210177162575960289303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31115473451441717306859535 46673210177162575960289303)
              ·
                refine ⟨70009815265743863940433955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46673210177162575960289303 70009815265743863940433955)
                ·
                  refine ⟨105014722898615795910650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70009815265743863940433955 105014722898615795910650933)
                  ·
                    refine ⟨9845130271745230866623525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105014722898615795910650933 9845130271745230866623525)
                    ·
                      refine ⟨1845961925952230787491911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9845130271745230866623525 1845961925952230787491911)
                      ·
                        rfl

theorem cell23_3594998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3594998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3594998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3594998 prefixEnd_3594998 := by exact prefixLift 3594998
  have htrace : WordTrace (prefixWord ++ tailWord_3594998) baseStart_3594998 baseEnd_3594998 := by
    simpa [prefixWord, tailWord_3594998, baseEnd_3594998] using wordTrace_append hprefix tailTrace_3594998
  have hstable : (prefixWord ++ tailWord_3594998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594998).length < 2 ^ (prefixWord ++ tailWord_3594998).sum := by decide
  have hdescent : baseEnd_3594998 < baseStart_3594998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
