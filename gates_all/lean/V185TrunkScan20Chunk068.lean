import V185TrunkScan20Chunk067

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_413430 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_413430 : Nat := 118140960795 + 413430 * 2 ^ 59
def prefixEnd_413430 : Nat := 4983230072969 + 3 ^ 40 * 413430 * 2
def baseEnd_413430 : Nat := 188700717323042388376601

theorem tailTrace_413430 : CollatzResearch.WordTrace tailWord_413430 prefixEnd_413430 188700717323042388376601 := by
  unfold tailWord_413430
  simp only [CollatzResearch.WordTrace]
  refine ⟨942439430763824566731359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10052687261480795378467829 942439430763824566731359)
  ·
    refine ⟨1413659146145736850097039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942439430763824566731359 1413659146145736850097039)
    ·
      refine ⟨2120488719218605275145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413659146145736850097039 2120488719218605275145559)
      ·
        refine ⟨3180733078827907912718339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120488719218605275145559 3180733078827907912718339)
        ·
          refine ⟨4771099618241861869077509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180733078827907912718339 4771099618241861869077509)
          ·
            refine ⟨894581178420349100452033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4771099618241861869077509 894581178420349100452033)
            ·
              refine ⟨670935883815261825339025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894581178420349100452033 670935883815261825339025)
              ·
                refine ⟨503201912861446369004269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670935883815261825339025 503201912861446369004269)
                ·
                  refine ⟨188700717323042388376601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503201912861446369004269 188700717323042388376601)
                  ·
                    rfl

theorem cell20_413430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_413430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413430 prefixEnd_413430 := by exact prefixLift 413430
  have htrace : WordTrace (prefixWord ++ tailWord_413430) baseStart_413430 baseEnd_413430 := by
    simpa [prefixWord, tailWord_413430, baseEnd_413430] using wordTrace_append hprefix tailTrace_413430
  have hstable : (prefixWord ++ tailWord_413430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413430).length < 2 ^ (prefixWord ++ tailWord_413430).sum := by decide
  have hdescent : baseEnd_413430 < baseStart_413430 := by decide
  rcases family_descends (prefixWord ++ tailWord_413430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413444 : List Nat := [2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_413444 : Nat := 118140960795 + 413444 * 2 ^ 59
def prefixEnd_413444 : Nat := 4983230072969 + 3 ^ 40 * 413444 * 2
def baseEnd_413444 : Nat := 62902369101506853969959

theorem tailTrace_413444 : CollatzResearch.WordTrace tailWord_413444 prefixEnd_413444 62902369101506853969959 := by
  unfold tailWord_413444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539770757085236729355693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10053027676113648972474257 7539770757085236729355693)
  ·
    refine ⟨2827414033906963773508385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7539770757085236729355693 2827414033906963773508385)
    ·
      refine ⟨2120560525430222830131289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2827414033906963773508385 2120560525430222830131289)
      ·
        refine ⟨1590420394072667122598467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2120560525430222830131289 1590420394072667122598467)
        ·
          refine ⟨2385630591109000683897701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590420394072667122598467 2385630591109000683897701)
          ·
            refine ⟨447305735832937628230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2385630591109000683897701 447305735832937628230819)
            ·
              refine ⟨670958603749406442346229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447305735832937628230819 670958603749406442346229)
              ·
                refine ⟨62902369101506853969959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670958603749406442346229 62902369101506853969959)
                ·
                  rfl

theorem cell20_413444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_413444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413444 prefixEnd_413444 := by exact prefixLift 413444
  have htrace : WordTrace (prefixWord ++ tailWord_413444) baseStart_413444 baseEnd_413444 := by
    simpa [prefixWord, tailWord_413444, baseEnd_413444] using wordTrace_append hprefix tailTrace_413444
  have hstable : (prefixWord ++ tailWord_413444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413444).length < 2 ^ (prefixWord ++ tailWord_413444).sum := by decide
  have hdescent : baseEnd_413444 < baseStart_413444 := by decide
  rcases family_descends (prefixWord ++ tailWord_413444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413472 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_413472 : Nat := 118140960795 + 413472 * 2 ^ 59
def prefixEnd_413472 : Nat := 4983230072969 + 3 ^ 40 * 413472 * 2
def baseEnd_413472 : Nat := 188719887267476908976429

theorem tailTrace_413472 : CollatzResearch.WordTrace tailWord_413472 prefixEnd_413472 188719887267476908976429 := by
  unfold tailWord_413472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540281379034517120365335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10053708505379356160487113 7540281379034517120365335)
  ·
    refine ⟨11310422068551775680548003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540281379034517120365335 11310422068551775680548003)
    ·
      refine ⟨16965633102827663520822005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310422068551775680548003 16965633102827663520822005)
      ·
        refine ⟨1590528103390093455077063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16965633102827663520822005 1590528103390093455077063)
        ·
          refine ⟨2385792155085140182615595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590528103390093455077063 2385792155085140182615595)
          ·
            refine ⟨3578688232627710273923393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385792155085140182615595 3578688232627710273923393)
            ·
              refine ⟨2684016174470782705442545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3578688232627710273923393 2684016174470782705442545)
              ·
                refine ⟨2013012130853087029081909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684016174470782705442545 2013012130853087029081909)
                ·
                  refine ⟨188719887267476908976429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2013012130853087029081909 188719887267476908976429)
                  ·
                    rfl

theorem cell20_413472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_413472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413472 prefixEnd_413472 := by exact prefixLift 413472
  have htrace : WordTrace (prefixWord ++ tailWord_413472) baseStart_413472 baseEnd_413472 := by
    simpa [prefixWord, tailWord_413472, baseEnd_413472] using wordTrace_append hprefix tailTrace_413472
  have hstable : (prefixWord ++ tailWord_413472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413472).length < 2 ^ (prefixWord ++ tailWord_413472).sum := by decide
  have hdescent : baseEnd_413472 < baseStart_413472 := by decide
  rcases family_descends (prefixWord ++ tailWord_413472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413489 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_413489 : Nat := 118140960795 + 413489 * 2 ^ 59
def prefixEnd_413489 : Nat := 4983230072969 + 3 ^ 40 * 413489 * 2
def baseEnd_413489 : Nat := 188727646530700405409693

theorem tailTrace_413489 : CollatzResearch.WordTrace tailWord_413489 prefixEnd_413489 188727646530700405409693 := by
  unfold tailWord_413489
  simp only [CollatzResearch.WordTrace]
  refine ⟨15081182799007446144099521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10054121866004964096066347 15081182799007446144099521)
  ·
    refine ⟨11310887099255584608074641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15081182799007446144099521 11310887099255584608074641)
    ·
      refine ⟨8483165324441688456055981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11310887099255584608074641 8483165324441688456055981)
      ·
        refine ⟨3181186996665633171020993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8483165324441688456055981 3181186996665633171020993)
        ·
          refine ⟨2385890247499224878265745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3181186996665633171020993 2385890247499224878265745)
          ·
            refine ⟨1789417685624418658699309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385890247499224878265745 1789417685624418658699309)
            ·
              refine ⟨671031632109156997012241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1789417685624418658699309 671031632109156997012241)
              ·
                refine ⟨503273724081867747759181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671031632109156997012241 503273724081867747759181)
                ·
                  refine ⟨188727646530700405409693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503273724081867747759181 188727646530700405409693)
                  ·
                    rfl

theorem cell20_413489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_413489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413489 prefixEnd_413489 := by exact prefixLift 413489
  have htrace : WordTrace (prefixWord ++ tailWord_413489) baseStart_413489 baseEnd_413489 := by
    simpa [prefixWord, tailWord_413489, baseEnd_413489] using wordTrace_append hprefix tailTrace_413489
  have hstable : (prefixWord ++ tailWord_413489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413489).length < 2 ^ (prefixWord ++ tailWord_413489).sum := by decide
  have hdescent : baseEnd_413489 < baseStart_413489 := by decide
  rcases family_descends (prefixWord ++ tailWord_413489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413492 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_413492 : Nat := 118140960795 + 413492 * 2 ^ 59
def prefixEnd_413492 : Nat := 4983230072969 + 3 ^ 40 * 413492 * 2
def baseEnd_413492 : Nat := 188729015812445728309681

theorem tailTrace_413492 : CollatzResearch.WordTrace tailWord_413492 prefixEnd_413492 188729015812445728309681 := by
  unfold tailWord_413492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540646108998288828229365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10054194811997718437639153 7540646108998288828229365)
  ·
    refine ⟨706935572718589577646503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7540646108998288828229365 706935572718589577646503)
    ·
      refine ⟨1060403359077884366469755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706935572718589577646503 1060403359077884366469755)
      ·
        refine ⟨1590605038616826549704633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060403359077884366469755 1590605038616826549704633)
        ·
          refine ⟨1192953778962619912278475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590605038616826549704633 1192953778962619912278475)
          ·
            refine ⟨1789430668443929868417713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192953778962619912278475 1789430668443929868417713)
            ·
              refine ⟨1342073001332947401313285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789430668443929868417713 1342073001332947401313285)
              ·
                refine ⟨251638687749927637746241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1342073001332947401313285 251638687749927637746241)
                ·
                  refine ⟨188729015812445728309681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251638687749927637746241 188729015812445728309681)
                  ·
                    rfl

theorem cell20_413492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_413492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413492 prefixEnd_413492 := by exact prefixLift 413492
  have htrace : WordTrace (prefixWord ++ tailWord_413492) baseStart_413492 baseEnd_413492 := by
    simpa [prefixWord, tailWord_413492, baseEnd_413492] using wordTrace_append hprefix tailTrace_413492
  have hstable : (prefixWord ++ tailWord_413492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413492).length < 2 ^ (prefixWord ++ tailWord_413492).sum := by decide
  have hdescent : baseEnd_413492 < baseStart_413492 := by decide
  rcases family_descends (prefixWord ++ tailWord_413492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413496 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_413496 : Nat := 118140960795 + 413496 * 2 ^ 59
def prefixEnd_413496 : Nat := 4983230072969 + 3 ^ 40 * 413496 * 2
def baseEnd_413496 : Nat := 188730841521439492176331

theorem tailTrace_413496 : CollatzResearch.WordTrace tailWord_413496 prefixEnd_413496 188730841521439492176331 := by
  unfold tailWord_413496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540719054991043169802171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10054292073321390893069561 7540719054991043169802171)
  ·
    refine ⟨11311078582486564754703257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540719054991043169802171 11311078582486564754703257)
    ·
      refine ⟨8483308936864923566027443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11311078582486564754703257 8483308936864923566027443)
      ·
        refine ⟨12724963405297385349041165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483308936864923566027443 12724963405297385349041165)
        ·
          refine ⟨4771861276986519505890437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12724963405297385349041165 4771861276986519505890437)
          ·
            refine ⟨894723989434972407354457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4771861276986519505890437 894723989434972407354457)
            ·
              refine ⟨671042992076229305515843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894723989434972407354457 671042992076229305515843)
              ·
                refine ⟨1006564488114343958273765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671042992076229305515843 1006564488114343958273765)
                ·
                  refine ⟨188730841521439492176331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006564488114343958273765 188730841521439492176331)
                  ·
                    rfl

theorem cell20_413496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_413496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413496 prefixEnd_413496 := by exact prefixLift 413496
  have htrace : WordTrace (prefixWord ++ tailWord_413496) baseStart_413496 baseEnd_413496 := by
    simpa [prefixWord, tailWord_413496, baseEnd_413496] using wordTrace_append hprefix tailTrace_413496
  have hstable : (prefixWord ++ tailWord_413496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413496).length < 2 ^ (prefixWord ++ tailWord_413496).sum := by decide
  have hdescent : baseEnd_413496 < baseStart_413496 := by decide
  rcases family_descends (prefixWord ++ tailWord_413496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413548 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_413548 : Nat := 118140960795 + 413548 * 2 ^ 59
def prefixEnd_413548 : Nat := 4983230072969 + 3 ^ 40 * 413548 * 2
def baseEnd_413548 : Nat := 188754575738358422442785

theorem tailTrace_413548 : CollatzResearch.WordTrace tailWord_413548 prefixEnd_413548 188754575738358422442785 := by
  unfold tailWord_413548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541667352896849610248649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10055556470529132813664865 7541667352896849610248649)
  ·
    refine ⟨5656250514672637207686487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7541667352896849610248649 5656250514672637207686487)
    ·
      refine ⟨8484375772008955811529731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656250514672637207686487 8484375772008955811529731)
      ·
        refine ⟨12726563658013433717294597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484375772008955811529731 12726563658013433717294597)
        ·
          refine ⟨2386230685877518821992737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12726563658013433717294597 2386230685877518821992737)
          ·
            refine ⟨1789673014408139116494553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386230685877518821992737 1789673014408139116494553)
            ·
              refine ⟨1342254760806104337370915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789673014408139116494553 1342254760806104337370915)
              ·
                refine ⟨2013382141209156506056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342254760806104337370915 2013382141209156506056373)
                ·
                  refine ⟨188754575738358422442785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2013382141209156506056373 188754575738358422442785)
                  ·
                    rfl

theorem cell20_413548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_413548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413548 prefixEnd_413548 := by exact prefixLift 413548
  have htrace : WordTrace (prefixWord ++ tailWord_413548) baseStart_413548 baseEnd_413548 := by
    simpa [prefixWord, tailWord_413548, baseEnd_413548] using wordTrace_append hprefix tailTrace_413548
  have hstable : (prefixWord ++ tailWord_413548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413548).length < 2 ^ (prefixWord ++ tailWord_413548).sum := by decide
  have hdescent : baseEnd_413548 < baseStart_413548 := by decide
  rcases family_descends (prefixWord ++ tailWord_413548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413562 : List Nat := [3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_413562 : Nat := 118140960795 + 413562 * 2 ^ 59
def prefixEnd_413562 : Nat := 4983230072969 + 3 ^ 40 * 413562 * 2
def baseEnd_413562 : Nat := 62920321906612198658687

theorem tailTrace_413562 : CollatzResearch.WordTrace tailWord_413562 prefixEnd_413562 62920321906612198658687 := by
  unfold tailWord_413562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770961331935744902876735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10055896885161986407671293 3770961331935744902876735)
  ·
    refine ⟨5656441997903617354315103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3770961331935744902876735 5656441997903617354315103)
    ·
      refine ⟨8484662996855426031472655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656441997903617354315103 8484662996855426031472655)
      ·
        refine ⟨12726994495283139047208983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484662996855426031472655 12726994495283139047208983)
        ·
          refine ⟨19090491742924708570813475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12726994495283139047208983 19090491742924708570813475)
          ·
            refine ⟨28635737614387062856220213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19090491742924708570813475 28635737614387062856220213)
            ·
              refine ⟨2684600401348787142770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28635737614387062856220213 2684600401348787142770645)
              ·
                refine ⟨62920321906612198658687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2684600401348787142770645 62920321906612198658687)
                ·
                  rfl

theorem cell20_413562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_413562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413562 prefixEnd_413562 := by exact prefixLift 413562
  have htrace : WordTrace (prefixWord ++ tailWord_413562) baseStart_413562 baseEnd_413562 := by
    simpa [prefixWord, tailWord_413562, baseEnd_413562] using wordTrace_append hprefix tailTrace_413562
  have hstable : (prefixWord ++ tailWord_413562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413562).length < 2 ^ (prefixWord ++ tailWord_413562).sum := by decide
  have hdescent : baseEnd_413562 < baseStart_413562 := by decide
  rcases family_descends (prefixWord ++ tailWord_413562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413602 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_413602 : Nat := 118140960795 + 413602 * 2 ^ 59
def prefixEnd_413602 : Nat := 4983230072969 + 3 ^ 40 * 413602 * 2
def baseEnd_413602 : Nat := 188779222809774234642565

theorem tailTrace_413602 : CollatzResearch.WordTrace tailWord_413602 prefixEnd_413602 188779222809774234642565 := by
  unfold tailWord_413602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771326061899516610740765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10056869498398710961975373 3771326061899516610740765)
  ·
    refine ⟨1414247273212318729027787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3771326061899516610740765 1414247273212318729027787)
    ·
      refine ⟨2121370909818478093541681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414247273212318729027787 2121370909818478093541681)
      ·
        refine ⟨1591028182363858570156261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121370909818478093541681 1591028182363858570156261)
        ·
          refine ⟨298317784193223481904299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1591028182363858570156261 298317784193223481904299)
          ·
            refine ⟨447476676289835222856449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298317784193223481904299 447476676289835222856449)
            ·
              refine ⟨335607507217376417142337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447476676289835222856449 335607507217376417142337)
              ·
                refine ⟨251705630413032312856753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335607507217376417142337 251705630413032312856753)
                ·
                  refine ⟨188779222809774234642565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251705630413032312856753 188779222809774234642565)
                  ·
                    rfl

theorem cell20_413602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_413602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413602 prefixEnd_413602 := by exact prefixLift 413602
  have htrace : WordTrace (prefixWord ++ tailWord_413602) baseStart_413602 baseEnd_413602 := by
    simpa [prefixWord, tailWord_413602, baseEnd_413602] using wordTrace_append hprefix tailTrace_413602
  have hstable : (prefixWord ++ tailWord_413602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413602).length < 2 ^ (prefixWord ++ tailWord_413602).sum := by decide
  have hdescent : baseEnd_413602 < baseStart_413602 := by decide
  rcases family_descends (prefixWord ++ tailWord_413602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413617 : List Nat := [1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_413617 : Nat := 118140960795 + 413617 * 2 ^ 59
def prefixEnd_413617 : Nat := 4983230072969 + 3 ^ 40 * 413617 * 2
def baseEnd_413617 : Nat := 62928689739500283047501

theorem tailTrace_413617 : CollatzResearch.WordTrace tailWord_413617 prefixEnd_413617 62928689739500283047501 := by
  unfold tailWord_413617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15085851342543724004759105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10057234228362482669839403 15085851342543724004759105)
  ·
    refine ⟨11314388506907793003569329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15085851342543724004759105 11314388506907793003569329)
    ·
      refine ⟨8485791380180844752676997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11314388506907793003569329 8485791380180844752676997)
      ·
        refine ⟨1591085883783908391126937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8485791380180844752676997 1591085883783908391126937)
        ·
          refine ⟨1193314412837931293345203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591085883783908391126937 1193314412837931293345203)
          ·
            refine ⟨1789971619256896940017805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193314412837931293345203 1789971619256896940017805)
            ·
              refine ⟨671239357221336352506677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1789971619256896940017805 671239357221336352506677)
              ·
                refine ⟨62928689739500283047501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671239357221336352506677 62928689739500283047501)
                ·
                  rfl

theorem cell20_413617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_413617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413617 prefixEnd_413617 := by exact prefixLift 413617
  have htrace : WordTrace (prefixWord ++ tailWord_413617) baseStart_413617 baseEnd_413617 := by
    simpa [prefixWord, tailWord_413617, baseEnd_413617] using wordTrace_append hprefix tailTrace_413617
  have hstable : (prefixWord ++ tailWord_413617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413617).length < 2 ^ (prefixWord ++ tailWord_413617).sum := by decide
  have hdescent : baseEnd_413617 < baseStart_413617 := by decide
  rcases family_descends (prefixWord ++ tailWord_413617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413624 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_413624 : Nat := 118140960795 + 413624 * 2 ^ 59
def prefixEnd_413624 : Nat := 4983230072969 + 3 ^ 40 * 413624 * 2
def baseEnd_413624 : Nat := 188789264209239935909141

theorem tailTrace_413624 : CollatzResearch.WordTrace tailWord_413624 prefixEnd_413624 188789264209239935909141 := by
  unfold tailWord_413624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543053326759182100131963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10057404435678909466842617 7543053326759182100131963)
  ·
    refine ⟨11314579990138773150197945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543053326759182100131963 11314579990138773150197945)
    ·
      refine ⟨8485934992604079862648459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11314579990138773150197945 8485934992604079862648459)
      ·
        refine ⟨12728902488906119793972689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485934992604079862648459 12728902488906119793972689)
        ·
          refine ⟨9546676866679589845479517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12728902488906119793972689 9546676866679589845479517)
          ·
            refine ⟨3580003825004846192054819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9546676866679589845479517 3580003825004846192054819)
            ·
              refine ⟨5370005737507269288082229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580003825004846192054819 5370005737507269288082229)
              ·
                refine ⟨503438037891306495757709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5370005737507269288082229 503438037891306495757709)
                ·
                  refine ⟨188789264209239935909141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503438037891306495757709 188789264209239935909141)
                  ·
                    rfl

theorem cell20_413624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_413624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413624 prefixEnd_413624 := by exact prefixLift 413624
  have htrace : WordTrace (prefixWord ++ tailWord_413624) baseStart_413624 baseEnd_413624 := by
    simpa [prefixWord, tailWord_413624, baseEnd_413624] using wordTrace_append hprefix tailTrace_413624
  have hstable : (prefixWord ++ tailWord_413624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413624).length < 2 ^ (prefixWord ++ tailWord_413624).sum := by decide
  have hdescent : baseEnd_413624 < baseStart_413624 := by decide
  rcases family_descends (prefixWord ++ tailWord_413624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413631 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_413631 : Nat := 118140960795 + 413631 * 2 ^ 59
def prefixEnd_413631 : Nat := 4983230072969 + 3 ^ 40 * 413631 * 2
def baseEnd_413631 : Nat := 188792459199979022675779

theorem tailTrace_413631 : CollatzResearch.WordTrace tailWord_413631 prefixEnd_413631 188792459199979022675779 := by
  unfold tailWord_413631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086361964493004395768747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10057574642995336263845831 15086361964493004395768747)
  ·
    refine ⟨22629542946739506593653121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15086361964493004395768747 22629542946739506593653121)
    ·
      refine ⟨16972157210054629945239841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22629542946739506593653121 16972157210054629945239841)
      ·
        refine ⟨12729117907540972458929881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16972157210054629945239841 12729117907540972458929881)
        ·
          refine ⟨9546838430655729344197411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12729117907540972458929881 9546838430655729344197411)
          ·
            refine ⟨14320257645983594016296117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546838430655729344197411 14320257645983594016296117)
            ·
              refine ⟨1342524154310961939027761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14320257645983594016296117 1342524154310961939027761)
              ·
                refine ⟨1006893115733221454270821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342524154310961939027761 1006893115733221454270821)
                ·
                  refine ⟨188792459199979022675779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006893115733221454270821 188792459199979022675779)
                  ·
                    rfl

theorem cell20_413631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_413631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413631 prefixEnd_413631 := by exact prefixLift 413631
  have htrace : WordTrace (prefixWord ++ tailWord_413631) baseStart_413631 baseEnd_413631 := by
    simpa [prefixWord, tailWord_413631, baseEnd_413631] using wordTrace_append hprefix tailTrace_413631
  have hstable : (prefixWord ++ tailWord_413631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413631).length < 2 ^ (prefixWord ++ tailWord_413631).sum := by decide
  have hdescent : baseEnd_413631 < baseStart_413631 := by decide
  rcases family_descends (prefixWord ++ tailWord_413631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413648 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_413648 : Nat := 118140960795 + 413648 * 2 ^ 59
def prefixEnd_413648 : Nat := 4983230072969 + 3 ^ 40 * 413648 * 2
def baseEnd_413648 : Nat := 188800218463202519109043

theorem tailTrace_413648 : CollatzResearch.WordTrace tailWord_413648 prefixEnd_413648 188800218463202519109043 := by
  unfold tailWord_413648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543491002715708149568799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10057988003620944199425065 7543491002715708149568799)
  ·
    refine ⟨11315236504073562224353199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543491002715708149568799 11315236504073562224353199)
    ·
      refine ⟨16972854756110343336529799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315236504073562224353199 16972854756110343336529799)
      ·
        refine ⟨25459282134165515004794699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16972854756110343336529799 25459282134165515004794699)
        ·
          refine ⟨38188923201248272507192049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25459282134165515004794699 38188923201248272507192049)
          ·
            refine ⟨28641692400936204380394037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38188923201248272507192049 28641692400936204380394037)
            ·
              refine ⟨2685158662587769160661941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28641692400936204380394037 2685158662587769160661941)
              ·
                refine ⟨251733624617603358812057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2685158662587769160661941 251733624617603358812057)
                ·
                  refine ⟨188800218463202519109043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251733624617603358812057 188800218463202519109043)
                  ·
                    rfl

theorem cell20_413648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_413648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413648 prefixEnd_413648 := by exact prefixLift 413648
  have htrace : WordTrace (prefixWord ++ tailWord_413648) baseStart_413648 baseEnd_413648 := by
    simpa [prefixWord, tailWord_413648, baseEnd_413648] using wordTrace_append hprefix tailTrace_413648
  have hstable : (prefixWord ++ tailWord_413648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413648).length < 2 ^ (prefixWord ++ tailWord_413648).sum := by decide
  have hdescent : baseEnd_413648 < baseStart_413648 := by decide
  rcases family_descends (prefixWord ++ tailWord_413648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413654 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_413654 : Nat := 118140960795 + 413654 * 2 ^ 59
def prefixEnd_413654 : Nat := 4983230072969 + 3 ^ 40 * 413654 * 2
def baseEnd_413654 : Nat := 188802957026693164909019

theorem tailTrace_413654 : CollatzResearch.WordTrace tailWord_413654 prefixEnd_413654 188802957026693164909019 := by
  unfold tailWord_413654
  simp only [CollatzResearch.WordTrace]
  refine ⟨942950052713104957741001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10058133895606452882570677 942950052713104957741001)
  ·
    refine ⟨707212539534828718305751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 942950052713104957741001 707212539534828718305751)
    ·
      refine ⟨1060818809302243077458627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707212539534828718305751 1060818809302243077458627)
      ·
        refine ⟨1591228213953364616187941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060818809302243077458627 1591228213953364616187941)
        ·
          refine ⟨298355290116255865535239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1591228213953364616187941 298355290116255865535239)
          ·
            refine ⟨447532935174383798302859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298355290116255865535239 447532935174383798302859)
            ·
              refine ⟨671299402761575697454289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447532935174383798302859 671299402761575697454289)
              ·
                refine ⟨503474552071181773090717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671299402761575697454289 503474552071181773090717)
                ·
                  refine ⟨188802957026693164909019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503474552071181773090717 188802957026693164909019)
                  ·
                    rfl

theorem cell20_413654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_413654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413654 prefixEnd_413654 := by exact prefixLift 413654
  have htrace : WordTrace (prefixWord ++ tailWord_413654) baseStart_413654 baseEnd_413654 := by
    simpa [prefixWord, tailWord_413654, baseEnd_413654] using wordTrace_append hprefix tailTrace_413654
  have hstable : (prefixWord ++ tailWord_413654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413654).length < 2 ^ (prefixWord ++ tailWord_413654).sum := by decide
  have hdescent : baseEnd_413654 < baseStart_413654 := by decide
  rcases family_descends (prefixWord ++ tailWord_413654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413658 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_413658 : Nat := 118140960795 + 413658 * 2 ^ 59
def prefixEnd_413658 : Nat := 4983230072969 + 3 ^ 40 * 413658 * 2
def baseEnd_413658 : Nat := 188804782735686928775669

theorem tailTrace_413658 : CollatzResearch.WordTrace tailWord_413658 prefixEnd_413658 188804782735686928775669 := by
  unfold tailWord_413658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771836683848797001750407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10058231156930125338001085 3771836683848797001750407)
  ·
    refine ⟨5657755025773195502625611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3771836683848797001750407 5657755025773195502625611)
    ·
      refine ⟨8486632538659793253938417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5657755025773195502625611 8486632538659793253938417)
      ·
        refine ⟨6364974403994844940453813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8486632538659793253938417 6364974403994844940453813)
        ·
          refine ⟨596716350374516713167545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6364974403994844940453813 596716350374516713167545)
          ·
            refine ⟨447537262780887534875659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596716350374516713167545 447537262780887534875659)
            ·
              refine ⟨671305894171331302313489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447537262780887534875659 671305894171331302313489)
              ·
                refine ⟨503479420628498476735117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671305894171331302313489 503479420628498476735117)
                ·
                  refine ⟨188804782735686928775669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503479420628498476735117 188804782735686928775669)
                  ·
                    rfl

theorem cell20_413658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_413658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413658 prefixEnd_413658 := by exact prefixLift 413658
  have htrace : WordTrace (prefixWord ++ tailWord_413658) baseStart_413658 baseEnd_413658 := by
    simpa [prefixWord, tailWord_413658, baseEnd_413658] using wordTrace_append hprefix tailTrace_413658
  have hstable : (prefixWord ++ tailWord_413658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413658).length < 2 ^ (prefixWord ++ tailWord_413658).sum := by decide
  have hdescent : baseEnd_413658 < baseStart_413658 := by decide
  rcases family_descends (prefixWord ++ tailWord_413658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413679 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_413679 : Nat := 118140960795 + 413679 * 2 ^ 59
def prefixEnd_413679 : Nat := 4983230072969 + 3 ^ 40 * 413679 * 2
def baseEnd_413679 : Nat := 188814367707904189075583

theorem tailTrace_413679 : CollatzResearch.WordTrace tailWord_413679 prefixEnd_413679 188814367707904189075583 := by
  unfold tailWord_413679
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088112668319108593516091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10058741778879405729010727 15088112668319108593516091)
  ·
    refine ⟨22632169002478662890274137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088112668319108593516091 22632169002478662890274137)
    ·
      refine ⟨16974126751858997167705603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22632169002478662890274137 16974126751858997167705603)
      ·
        refine ⟨25461190127788495751558405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16974126751858997167705603 25461190127788495751558405)
        ·
          refine ⟨4773973148960342953417201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25461190127788495751558405 4773973148960342953417201)
          ·
            refine ⟨3580479861720257215062901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773973148960342953417201 3580479861720257215062901)
            ·
              refine ⟨335669987036274113912147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3580479861720257215062901 335669987036274113912147)
              ·
                refine ⟨503504980554411170868221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335669987036274113912147 503504980554411170868221)
                ·
                  refine ⟨188814367707904189075583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503504980554411170868221 188814367707904189075583)
                  ·
                    rfl

theorem cell20_413679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_413679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413679 prefixEnd_413679 := by exact prefixLift 413679
  have htrace : WordTrace (prefixWord ++ tailWord_413679) baseStart_413679 baseEnd_413679 := by
    simpa [prefixWord, tailWord_413679, baseEnd_413679] using wordTrace_append hprefix tailTrace_413679
  have hstable : (prefixWord ++ tailWord_413679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413679).length < 2 ^ (prefixWord ++ tailWord_413679).sum := by decide
  have hdescent : baseEnd_413679 < baseStart_413679 := by decide
  rcases family_descends (prefixWord ++ tailWord_413679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413693 : List Nat := [1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_413693 : Nat := 118140960795 + 413693 * 2 ^ 59
def prefixEnd_413693 : Nat := 4983230072969 + 3 ^ 40 * 413693 * 2
def baseEnd_413693 : Nat := 62940252563127454202953

theorem tailTrace_413693 : CollatzResearch.WordTrace tailWord_413693 prefixEnd_413693 62940252563127454202953 := by
  unfold tailWord_413693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088623290268388984525733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10059082193512259323017155 15088623290268388984525733)
  ·
    refine ⟨2829116866925322934598575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15088623290268388984525733 2829116866925322934598575)
    ·
      refine ⟨4243675300387984401897863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2829116866925322934598575 4243675300387984401897863)
      ·
        refine ⟨6365512950581976602846795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243675300387984401897863 6365512950581976602846795)
        ·
          refine ⟨9548269425872964904270193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365512950581976602846795 9548269425872964904270193)
          ·
            refine ⟨7161202069404723678202645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548269425872964904270193 7161202069404723678202645)
            ·
              refine ⟨335681347003346422415749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7161202069404723678202645 335681347003346422415749)
              ·
                refine ⟨62940252563127454202953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335681347003346422415749 62940252563127454202953)
                ·
                  rfl

theorem cell20_413693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_413693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413693 prefixEnd_413693 := by exact prefixLift 413693
  have htrace : WordTrace (prefixWord ++ tailWord_413693) baseStart_413693 baseEnd_413693 := by
    simpa [prefixWord, tailWord_413693, baseEnd_413693] using wordTrace_append hprefix tailTrace_413693
  have hstable : (prefixWord ++ tailWord_413693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413693).length < 2 ^ (prefixWord ++ tailWord_413693).sum := by decide
  have hdescent : baseEnd_413693 < baseStart_413693 := by decide
  rcases family_descends (prefixWord ++ tailWord_413693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413703 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 2]
def baseStart_413703 : Nat := 118140960795 + 413703 * 2 ^ 59
def prefixEnd_413703 : Nat := 4983230072969 + 3 ^ 40 * 413703 * 2
def baseEnd_413703 : Nat := 188825321961866772275485

theorem tailTrace_413703 : CollatzResearch.WordTrace tailWord_413703 prefixEnd_413703 188825321961866772275485 := by
  unfold tailWord_413703
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088988020232160692389763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10059325346821440461593175 15088988020232160692389763)
  ·
    refine ⟨22633482030348241038584645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088988020232160692389763 22633482030348241038584645)
    ·
      refine ⟨4243777880690295194734621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22633482030348241038584645 4243777880690295194734621)
      ·
        refine ⟨1591416705258860698025483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4243777880690295194734621 1591416705258860698025483)
        ·
          refine ⟨2387125057888291047038225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591416705258860698025483 2387125057888291047038225)
          ·
            refine ⟨1790343793416218285278669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2387125057888291047038225 1790343793416218285278669)
            ·
              refine ⟨671378922531081856979501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1790343793416218285278669 671378922531081856979501)
              ·
                refine ⟨251767095949155696367313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671378922531081856979501 251767095949155696367313)
                ·
                  refine ⟨188825321961866772275485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251767095949155696367313 188825321961866772275485)
                  ·
                    rfl

theorem cell20_413703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2].length) (baseStart_413703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413703 prefixEnd_413703 := by exact prefixLift 413703
  have htrace : WordTrace (prefixWord ++ tailWord_413703) baseStart_413703 baseEnd_413703 := by
    simpa [prefixWord, tailWord_413703, baseEnd_413703] using wordTrace_append hprefix tailTrace_413703
  have hstable : (prefixWord ++ tailWord_413703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413703).length < 2 ^ (prefixWord ++ tailWord_413703).sum := by decide
  have hdescent : baseEnd_413703 < baseStart_413703 := by decide
  rcases family_descends (prefixWord ++ tailWord_413703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413716 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_413716 : Nat := 118140960795 + 413716 * 2 ^ 59
def prefixEnd_413716 : Nat := 4983230072969 + 3 ^ 40 * 413716 * 2
def baseEnd_413716 : Nat := 188831255516096504842099

theorem tailTrace_413716 : CollatzResearch.WordTrace tailWord_413716 prefixEnd_413716 188831255516096504842099 := by
  unfold tailWord_413716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544731084592531956306501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10059641446123375941742001 7544731084592531956306501)
  ·
    refine ⟨1414637078361099741807469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7544731084592531956306501 1414637078361099741807469)
    ·
      refine ⟨530488904385412403177801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1414637078361099741807469 530488904385412403177801)
      ·
        refine ⟨397866678289059302383351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530488904385412403177801 397866678289059302383351)
        ·
          refine ⟨596800017433588953575027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397866678289059302383351 596800017433588953575027)
          ·
            refine ⟨895200026150383430362541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596800017433588953575027 895200026150383430362541)
            ·
              refine ⟨335700009806393786385953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895200026150383430362541 335700009806393786385953)
              ·
                refine ⟨251775007354795339789465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335700009806393786385953 251775007354795339789465)
                ·
                  refine ⟨188831255516096504842099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251775007354795339789465 188831255516096504842099)
                  ·
                    rfl

theorem cell20_413716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_413716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413716 prefixEnd_413716 := by exact prefixLift 413716
  have htrace : WordTrace (prefixWord ++ tailWord_413716) baseStart_413716 baseEnd_413716 := by
    simpa [prefixWord, tailWord_413716, baseEnd_413716] using wordTrace_append hprefix tailTrace_413716
  have hstable : (prefixWord ++ tailWord_413716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413716).length < 2 ^ (prefixWord ++ tailWord_413716).sum := by decide
  have hdescent : baseEnd_413716 < baseStart_413716 := by decide
  rcases family_descends (prefixWord ++ tailWord_413716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413724 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_413724 : Nat := 118140960795 + 413724 * 2 ^ 59
def prefixEnd_413724 : Nat := 4983230072969 + 3 ^ 40 * 413724 * 2
def baseEnd_413724 : Nat := 188834906934084032575399

theorem tailTrace_413724 : CollatzResearch.WordTrace tailWord_413724 prefixEnd_413724 188834906934084032575399 := by
  unfold tailWord_413724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544876976578040639452113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10059835968770720852602817 7544876976578040639452113)
  ·
    refine ⟨5658657732433530479589085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7544876976578040639452113 5658657732433530479589085)
    ·
      refine ⟨2121996649662573929845907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5658657732433530479589085 2121996649662573929845907)
      ·
        refine ⟨3182994974493860894768861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121996649662573929845907 3182994974493860894768861)
        ·
          refine ⟨1193623115435197835538323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3182994974493860894768861 1193623115435197835538323)
          ·
            refine ⟨1790434673152796753307485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193623115435197835538323 1790434673152796753307485)
            ·
              refine ⟨671413002432298782490307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1790434673152796753307485 671413002432298782490307)
              ·
                refine ⟨1007119503648448173735461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671413002432298782490307 1007119503648448173735461)
                ·
                  refine ⟨188834906934084032575399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007119503648448173735461 188834906934084032575399)
                  ·
                    rfl

theorem cell20_413724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_413724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413724 prefixEnd_413724 := by exact prefixLift 413724
  have htrace : WordTrace (prefixWord ++ tailWord_413724) baseStart_413724 baseEnd_413724 := by
    simpa [prefixWord, tailWord_413724, baseEnd_413724] using wordTrace_append hprefix tailTrace_413724
  have hstable : (prefixWord ++ tailWord_413724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413724).length < 2 ^ (prefixWord ++ tailWord_413724).sum := by decide
  have hdescent : baseEnd_413724 < baseStart_413724 := by decide
  rcases family_descends (prefixWord ++ tailWord_413724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413759 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_413759 : Nat := 118140960795 + 413759 * 2 ^ 59
def prefixEnd_413759 : Nat := 4983230072969 + 3 ^ 40 * 413759 * 2
def baseEnd_413759 : Nat := 188850881887779466408589

theorem tailTrace_413759 : CollatzResearch.WordTrace tailWord_413759 prefixEnd_413759 188850881887779466408589 := by
  unfold tailWord_413759
  simp only [CollatzResearch.WordTrace]
  refine ⟨15091030508029282256428331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10060687005352854837618887 15091030508029282256428331)
  ·
    refine ⟨22636545762043923384642497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15091030508029282256428331 22636545762043923384642497)
    ·
      refine ⟨16977409321532942538481873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22636545762043923384642497 16977409321532942538481873)
      ·
        refine ⟨12733056991149706903861405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16977409321532942538481873 12733056991149706903861405)
        ·
          refine ⟨4774896371681140088948027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12733056991149706903861405 4774896371681140088948027)
          ·
            refine ⟨7162344557521710133422041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774896371681140088948027 7162344557521710133422041)
            ·
              refine ⟨5371758418141282600066531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7162344557521710133422041 5371758418141282600066531)
              ·
                refine ⟨8057637627211923900099797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371758418141282600066531 8057637627211923900099797)
                ·
                  refine ⟨188850881887779466408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8057637627211923900099797 188850881887779466408589)
                  ·
                    rfl

theorem cell20_413759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_413759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413759 prefixEnd_413759 := by exact prefixLift 413759
  have htrace : WordTrace (prefixWord ++ tailWord_413759) baseStart_413759 baseEnd_413759 := by
    simpa [prefixWord, tailWord_413759, baseEnd_413759] using wordTrace_append hprefix tailTrace_413759
  have hstable : (prefixWord ++ tailWord_413759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413759).length < 2 ^ (prefixWord ++ tailWord_413759).sum := by decide
  have hdescent : baseEnd_413759 < baseStart_413759 := by decide
  rcases family_descends (prefixWord ++ tailWord_413759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413807 : List Nat := [1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_413807 : Nat := 118140960795 + 413807 * 2 ^ 59
def prefixEnd_413807 : Nat := 4983230072969 + 3 ^ 40 * 413807 * 2
def baseEnd_413807 : Nat := 62957596798568210936131

theorem tailTrace_413807 : CollatzResearch.WordTrace tailWord_413807 prefixEnd_413807 62957596798568210936131 := by
  unfold tailWord_413807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092781211855386454175675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061854141236924302783783 15092781211855386454175675)
  ·
    refine ⟨22639171817783079681263513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15092781211855386454175675 22639171817783079681263513)
    ·
      refine ⟨16979378863337309760947635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22639171817783079681263513 16979378863337309760947635)
      ·
        refine ⟨25469068295005964641421453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16979378863337309760947635 25469068295005964641421453)
        ·
          refine ⟨9550900610627236740533045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25469068295005964641421453 9550900610627236740533045)
          ·
            refine ⟨895396932246303444424973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9550900610627236740533045 895396932246303444424973)
            ·
              refine ⟨335773849592363791659365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895396932246303444424973 335773849592363791659365)
              ·
                refine ⟨62957596798568210936131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335773849592363791659365 62957596798568210936131)
                ·
                  rfl

theorem cell20_413807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_413807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413807 prefixEnd_413807 := by exact prefixLift 413807
  have htrace : WordTrace (prefixWord ++ tailWord_413807) baseStart_413807 baseEnd_413807 := by
    simpa [prefixWord, tailWord_413807, baseEnd_413807] using wordTrace_append hprefix tailTrace_413807
  have hstable : (prefixWord ++ tailWord_413807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413807).length < 2 ^ (prefixWord ++ tailWord_413807).sum := by decide
  have hdescent : baseEnd_413807 < baseStart_413807 := by decide
  rcases family_descends (prefixWord ++ tailWord_413807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413817 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 2]
def baseStart_413817 : Nat := 118140960795 + 413817 * 2 ^ 59
def prefixEnd_413817 : Nat := 4983230072969 + 3 ^ 40 * 413817 * 2
def baseEnd_413817 : Nat := 188877354668189042475019

theorem tailTrace_413817 : CollatzResearch.WordTrace tailWord_413817 prefixEnd_413817 188877354668189042475019 := by
  unfold tailWord_413817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093145941819158162039705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10062097294546105441359803 15093145941819158162039705)
  ·
    refine ⟨11319859456364368621529779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15093145941819158162039705 11319859456364368621529779)
    ·
      refine ⟨16979789184546552932294669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319859456364368621529779 16979789184546552932294669)
      ·
        refine ⟨6367420944204957349610501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16979789184546552932294669 6367420944204957349610501)
        ·
          refine ⟨1193891427038429503051969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6367420944204957349610501 1193891427038429503051969)
          ·
            refine ⟨895418570278822127288977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193891427038429503051969 895418570278822127288977)
            ·
              refine ⟨671563927709116595466733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895418570278822127288977 671563927709116595466733)
              ·
                refine ⟨251836472890918723300025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671563927709116595466733 251836472890918723300025)
                ·
                  refine ⟨188877354668189042475019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251836472890918723300025 188877354668189042475019)
                  ·
                    rfl

theorem cell20_413817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_413817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413817 prefixEnd_413817 := by exact prefixLift 413817
  have htrace : WordTrace (prefixWord ++ tailWord_413817) baseStart_413817 baseEnd_413817 := by
    simpa [prefixWord, tailWord_413817, baseEnd_413817] using wordTrace_append hprefix tailTrace_413817
  have hstable : (prefixWord ++ tailWord_413817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413817).length < 2 ^ (prefixWord ++ tailWord_413817).sum := by decide
  have hdescent : baseEnd_413817 < baseStart_413817 := by decide
  rcases family_descends (prefixWord ++ tailWord_413817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413828 : List Nat := [2, 3, 2, 1, 2, 1, 9]
def baseStart_413828 : Nat := 118140960795 + 413828 * 2 ^ 59
def prefixEnd_413828 : Nat := 4983230072969 + 3 ^ 40 * 413828 * 2
def baseEnd_413828 : Nat := 20986930596435765900923

theorem tailTrace_413828 : CollatzResearch.WordTrace tailWord_413828 prefixEnd_413828 20986930596435765900923 := by
  unfold tailWord_413828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546773572389653520345069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10062364763186204693793425 7546773572389653520345069)
  ·
    refine ⟨2830040089646120070129401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7546773572389653520345069 2830040089646120070129401)
    ·
      refine ⟨2122530067234590052597051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2830040089646120070129401 2122530067234590052597051)
      ·
        refine ⟨3183795100851885078895577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122530067234590052597051 3183795100851885078895577)
        ·
          refine ⟨2387846325638913809171683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3183795100851885078895577 2387846325638913809171683)
          ·
            refine ⟨3581769488458370713757525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387846325638913809171683 3581769488458370713757525)
            ·
              refine ⟨20986930596435765900923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3581769488458370713757525 20986930596435765900923)
              ·
                rfl

theorem cell20_413828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_413828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413828 prefixEnd_413828 := by exact prefixLift 413828
  have htrace : WordTrace (prefixWord ++ tailWord_413828) baseStart_413828 baseEnd_413828 := by
    simpa [prefixWord, tailWord_413828, baseEnd_413828] using wordTrace_append hprefix tailTrace_413828
  have hstable : (prefixWord ++ tailWord_413828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413828).length < 2 ^ (prefixWord ++ tailWord_413828).sum := by decide
  have hdescent : baseEnd_413828 < baseStart_413828 := by decide
  rcases family_descends (prefixWord ++ tailWord_413828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413848 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_413848 : Nat := 118140960795 + 413848 * 2 ^ 59
def prefixEnd_413848 : Nat := 4983230072969 + 3 ^ 40 * 413848 * 2
def baseEnd_413848 : Nat := 188891503912890712441559

theorem tailTrace_413848 : CollatzResearch.WordTrace tailWord_413848 prefixEnd_413848 188891503912890712441559 := by
  unfold tailWord_413848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547138302353425228209099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10062851069804566970945465 7547138302353425228209099)
  ·
    refine ⟨11320707453530137842313649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7547138302353425228209099 11320707453530137842313649)
    ·
      refine ⟨8490530590147603381735237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11320707453530137842313649 8490530590147603381735237)
      ·
        refine ⟨1591974485652675634075357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8490530590147603381735237 1591974485652675634075357)
        ·
          refine ⟨596990432119753362778259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1591974485652675634075357 596990432119753362778259)
          ·
            refine ⟨895485648179630044167389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596990432119753362778259 895485648179630044167389)
            ·
              refine ⟨335807118067361266562771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895485648179630044167389 335807118067361266562771)
              ·
                refine ⟨503710677101041899844157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335807118067361266562771 503710677101041899844157)
                ·
                  refine ⟨188891503912890712441559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503710677101041899844157 188891503912890712441559)
                  ·
                    rfl

theorem cell20_413848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_413848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413848 prefixEnd_413848 := by exact prefixLift 413848
  have htrace : WordTrace (prefixWord ++ tailWord_413848) baseStart_413848 baseEnd_413848 := by
    simpa [prefixWord, tailWord_413848, baseEnd_413848] using wordTrace_append hprefix tailTrace_413848
  have hstable : (prefixWord ++ tailWord_413848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413848).length < 2 ^ (prefixWord ++ tailWord_413848).sum := by decide
  have hdescent : baseEnd_413848 < baseStart_413848 := by decide
  rcases family_descends (prefixWord ++ tailWord_413848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413889 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 2]
def baseStart_413889 : Nat := 118140960795 + 413889 * 2 ^ 59
def prefixEnd_413889 : Nat := 4983230072969 + 3 ^ 40 * 413889 * 2
def baseEnd_413889 : Nat := 188910217430076792074725

theorem tailTrace_413889 : CollatzResearch.WordTrace tailWord_413889 prefixEnd_413889 188910217430076792074725 := by
  unfold tailWord_413889
  simp only [CollatzResearch.WordTrace]
  refine ⟨15095771997558314458660721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10063847998372209639107147 15095771997558314458660721)
  ·
    refine ⟨11321828998168735843995541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15095771997558314458660721 11321828998168735843995541)
    ·
      refine ⟨530710734289159492687291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11321828998168735843995541 530710734289159492687291)
      ·
        refine ⟨796066101433739239030937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530710734289159492687291 796066101433739239030937)
        ·
          refine ⟨597049576075304429273203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796066101433739239030937 597049576075304429273203)
          ·
            refine ⟨895574364112956643909805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597049576075304429273203 895574364112956643909805)
            ·
              refine ⟨335840386542358741466177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895574364112956643909805 335840386542358741466177)
              ·
                refine ⟨251880289906769056099633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335840386542358741466177 251880289906769056099633)
                ·
                  refine ⟨188910217430076792074725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251880289906769056099633 188910217430076792074725)
                  ·
                    rfl

theorem cell20_413889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_413889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413889 prefixEnd_413889 := by exact prefixLift 413889
  have htrace : WordTrace (prefixWord ++ tailWord_413889) baseStart_413889 baseEnd_413889 := by
    simpa [prefixWord, tailWord_413889, baseEnd_413889] using wordTrace_append hprefix tailTrace_413889
  have hstable : (prefixWord ++ tailWord_413889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413889).length < 2 ^ (prefixWord ++ tailWord_413889).sum := by decide
  have hdescent : baseEnd_413889 < baseStart_413889 := by decide
  rcases family_descends (prefixWord ++ tailWord_413889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413900 : List Nat := [2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_413900 : Nat := 118140960795 + 413900 * 2 ^ 59
def prefixEnd_413900 : Nat := 4983230072969 + 3 ^ 40 * 413900 * 2
def baseEnd_413900 : Nat := 62971746043269880902671

theorem tailTrace_413900 : CollatzResearch.WordTrace tailWord_413900 prefixEnd_413900 62971746043269880902671 := by
  unfold tailWord_413900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548086600259231668655577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10064115467012308891540769 7548086600259231668655577)
  ·
    refine ⟨5661064950194423751491683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7548086600259231668655577 5661064950194423751491683)
    ·
      refine ⟨8491597425291635627237525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661064950194423751491683 8491597425291635627237525)
      ·
        refine ⟨398043629310545420026759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8491597425291635627237525 398043629310545420026759)
        ·
          refine ⟨597065443965818130040139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398043629310545420026759 597065443965818130040139)
          ·
            refine ⟨895598165948727195060209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597065443965818130040139 895598165948727195060209)
            ·
              refine ⟨671698624461545396295157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895598165948727195060209 671698624461545396295157)
              ·
                refine ⟨62971746043269880902671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671698624461545396295157 62971746043269880902671)
                ·
                  rfl

theorem cell20_413900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_413900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413900 prefixEnd_413900 := by exact prefixLift 413900
  have htrace : WordTrace (prefixWord ++ tailWord_413900) baseStart_413900 baseEnd_413900 := by
    simpa [prefixWord, tailWord_413900, baseEnd_413900] using wordTrace_append hprefix tailTrace_413900
  have hstable : (prefixWord ++ tailWord_413900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413900).length < 2 ^ (prefixWord ++ tailWord_413900).sum := by decide
  have hdescent : baseEnd_413900 < baseStart_413900 := by decide
  rcases family_descends (prefixWord ++ tailWord_413900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413948 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_413948 : Nat := 118140960795 + 413948 * 2 ^ 59
def prefixEnd_413948 : Nat := 4983230072969 + 3 ^ 40 * 413948 * 2
def baseEnd_413948 : Nat := 188937146637734809107817

theorem tailTrace_413948 : CollatzResearch.WordTrace tailWord_413948 prefixEnd_413948 188937146637734809107817 := by
  unfold tailWord_413948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548961952172283767529249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10065282602896378356705665 7548961952172283767529249)
  ·
    refine ⟨5661721464129212825646937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7548961952172283767529249 5661721464129212825646937)
    ·
      refine ⟨4246291098096909619235203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5661721464129212825646937 4246291098096909619235203)
      ·
        refine ⟨6369436647145364428852805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246291098096909619235203 6369436647145364428852805)
        ·
          refine ⟨1194269371339755830409901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6369436647145364428852805 1194269371339755830409901)
          ·
            refine ⟨447851014252408436403713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1194269371339755830409901 447851014252408436403713)
            ·
              refine ⟨335888260689306327302785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447851014252408436403713 335888260689306327302785)
              ·
                refine ⟨251916195516979745477089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335888260689306327302785 251916195516979745477089)
                ·
                  refine ⟨188937146637734809107817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251916195516979745477089 188937146637734809107817)
                  ·
                    rfl

theorem cell20_413948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_413948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413948 prefixEnd_413948 := by exact prefixLift 413948
  have htrace : WordTrace (prefixWord ++ tailWord_413948) baseStart_413948 baseEnd_413948 := by
    simpa [prefixWord, tailWord_413948, baseEnd_413948] using wordTrace_append hprefix tailTrace_413948
  have hstable : (prefixWord ++ tailWord_413948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413948).length < 2 ^ (prefixWord ++ tailWord_413948).sum := by decide
  have hdescent : baseEnd_413948 < baseStart_413948 := by decide
  rcases family_descends (prefixWord ++ tailWord_413948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413949 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_413949 : Nat := 118140960795 + 413949 * 2 ^ 59
def prefixEnd_413949 : Nat := 4983230072969 + 3 ^ 40 * 413949 * 2
def baseEnd_413949 : Nat := 188937603064983250074479

theorem tailTrace_413949 : CollatzResearch.WordTrace tailWord_413949 prefixEnd_413949 188937603064983250074479 := by
  unfold tailWord_413949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15097960377340944705844901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10065306918227296470563267 15097960377340944705844901)
  ·
    refine ⟨2830867570751427132345919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15097960377340944705844901 2830867570751427132345919)
    ·
      refine ⟨4246301356127140698518879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830867570751427132345919 4246301356127140698518879)
      ·
        refine ⟨6369452034190711047778319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246301356127140698518879 6369452034190711047778319)
        ·
          refine ⟨9554178051286066571667479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369452034190711047778319 9554178051286066571667479)
          ·
            refine ⟨14331267076929099857501219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554178051286066571667479 14331267076929099857501219)
            ·
              refine ⟨21496900615393649786251829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14331267076929099857501219 21496900615393649786251829)
              ·
                refine ⟨2015334432693154667461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21496900615393649786251829 2015334432693154667461109)
                ·
                  refine ⟨188937603064983250074479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015334432693154667461109 188937603064983250074479)
                  ·
                    rfl

theorem cell20_413949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_413949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413949 prefixEnd_413949 := by exact prefixLift 413949
  have htrace : WordTrace (prefixWord ++ tailWord_413949) baseStart_413949 baseEnd_413949 := by
    simpa [prefixWord, tailWord_413949, baseEnd_413949] using wordTrace_append hprefix tailTrace_413949
  have hstable : (prefixWord ++ tailWord_413949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413949).length < 2 ^ (prefixWord ++ tailWord_413949).sum := by decide
  have hdescent : baseEnd_413949 < baseStart_413949 := by decide
  rcases family_descends (prefixWord ++ tailWord_413949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413966 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_413966 : Nat := 118140960795 + 413966 * 2 ^ 59
def prefixEnd_413966 : Nat := 4983230072969 + 3 ^ 40 * 413966 * 2
def baseEnd_413966 : Nat := 188945362328206746507743

theorem tailTrace_413966 : CollatzResearch.WordTrace tailWord_413966 prefixEnd_413966 188945362328206746507743 := by
  unfold tailWord_413966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887322552284919576151719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10065720278852904406142501 1887322552284919576151719)
  ·
    refine ⟨2830983828427379364227579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887322552284919576151719 2830983828427379364227579)
    ·
      refine ⟨4246475742641069046341369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830983828427379364227579 4246475742641069046341369)
      ·
        refine ⟨3184856806980801784756027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246475742641069046341369 3184856806980801784756027)
        ·
          refine ⟨4777285210471202677134041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184856806980801784756027 4777285210471202677134041)
          ·
            refine ⟨3582963907853402007850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777285210471202677134041 3582963907853402007850531)
            ·
              refine ⟨5374445861780103011775797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582963907853402007850531 5374445861780103011775797)
              ·
                refine ⟨503854299541884657353981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5374445861780103011775797 503854299541884657353981)
                ·
                  refine ⟨188945362328206746507743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503854299541884657353981 188945362328206746507743)
                  ·
                    rfl

theorem cell20_413966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_413966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413966 prefixEnd_413966 := by exact prefixLift 413966
  have htrace : WordTrace (prefixWord ++ tailWord_413966) baseStart_413966 baseEnd_413966 := by
    simpa [prefixWord, tailWord_413966, baseEnd_413966] using wordTrace_append hprefix tailTrace_413966
  have hstable : (prefixWord ++ tailWord_413966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413966).length < 2 ^ (prefixWord ++ tailWord_413966).sum := by decide
  have hdescent : baseEnd_413966 < baseStart_413966 := by decide
  rcases family_descends (prefixWord ++ tailWord_413966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413987 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_413987 : Nat := 118140960795 + 413987 * 2 ^ 59
def prefixEnd_413987 : Nat := 4983230072969 + 3 ^ 40 * 413987 * 2
def baseEnd_413987 : Nat := 188954947300424006807657

theorem tailTrace_413987 : CollatzResearch.WordTrace tailWord_413987 prefixEnd_413987 188954947300424006807657 := by
  unfold tailWord_413987
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099346351203277195728215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10066230900802184797152143 15099346351203277195728215)
  ·
    refine ⟨22649019526804915793592323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099346351203277195728215 22649019526804915793592323)
    ·
      refine ⟨33973529290207373690388485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649019526804915793592323 33973529290207373690388485)
      ·
        refine ⟨6370036741913882566947841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33973529290207373690388485 6370036741913882566947841)
        ·
          refine ⟨4777527556435411925210881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6370036741913882566947841 4777527556435411925210881)
          ·
            refine ⟨3583145667326558943908161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777527556435411925210881 3583145667326558943908161)
            ·
              refine ⟨2687359250494919207931121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583145667326558943908161 2687359250494919207931121)
              ·
                refine ⟨2015519437871189405948341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687359250494919207931121 2015519437871189405948341)
                ·
                  refine ⟨188954947300424006807657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015519437871189405948341 188954947300424006807657)
                  ·
                    rfl

theorem cell20_413987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_413987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413987 prefixEnd_413987 := by exact prefixLift 413987
  have htrace : WordTrace (prefixWord ++ tailWord_413987) baseStart_413987 baseEnd_413987 := by
    simpa [prefixWord, tailWord_413987, baseEnd_413987] using wordTrace_append hprefix tailTrace_413987
  have hstable : (prefixWord ++ tailWord_413987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413987).length < 2 ^ (prefixWord ++ tailWord_413987).sum := by decide
  have hdescent : baseEnd_413987 < baseStart_413987 := by decide
  rcases family_descends (prefixWord ++ tailWord_413987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414056 : List Nat := [2, 1, 4, 2, 2, 1, 8]
def baseStart_414056 : Nat := 118140960795 + 414056 * 2 ^ 59
def prefixEnd_414056 : Nat := 4983230072969 + 3 ^ 40 * 414056 * 2
def baseEnd_414056 : Nat := 20998493420062937056375

theorem tailTrace_414056 : CollatzResearch.WordTrace tailWord_414056 prefixEnd_414056 20998493420062937056375 := by
  unfold tailWord_414056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550931493976650989995011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10067908658635534653326681 7550931493976650989995011)
  ·
    refine ⟨11326397240964976484992517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550931493976650989995011 11326397240964976484992517)
    ·
      refine ⟨2123699482680933090936097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11326397240964976484992517 2123699482680933090936097)
      ·
        refine ⟨1592774612010699818202073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2123699482680933090936097 1592774612010699818202073)
        ·
          refine ⟨1194580959008024863651555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1592774612010699818202073 1194580959008024863651555)
          ·
            refine ⟨1791871438512037295477333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194580959008024863651555 1791871438512037295477333)
            ·
              refine ⟨20998493420062937056375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1791871438512037295477333 20998493420062937056375)
              ·
                rfl

theorem cell20_414056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_414056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414056 prefixEnd_414056 := by exact prefixLift 414056
  have htrace : WordTrace (prefixWord ++ tailWord_414056) baseStart_414056 baseEnd_414056 := by
    simpa [prefixWord, tailWord_414056, baseEnd_414056] using wordTrace_append hprefix tailTrace_414056
  have hstable : (prefixWord ++ tailWord_414056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414056).length < 2 ^ (prefixWord ++ tailWord_414056).sum := by decide
  have hdescent : baseEnd_414056 < baseStart_414056 := by decide
  rcases family_descends (prefixWord ++ tailWord_414056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414066 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_414066 : Nat := 118140960795 + 414066 * 2 ^ 59
def prefixEnd_414066 : Nat := 4983230072969 + 3 ^ 40 * 414066 * 2
def baseEnd_414066 : Nat := 188991005053050843174001

theorem tailTrace_414066 : CollatzResearch.WordTrace tailWord_414066 prefixEnd_414066 188991005053050843174001 := by
  unfold tailWord_414066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775556929479268421963513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10068151811944715791902701 3775556929479268421963513)
  ·
    refine ⟨2831667697109451316472635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3775556929479268421963513 2831667697109451316472635)
    ·
      refine ⟨4247501545664176974708953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831667697109451316472635 4247501545664176974708953)
      ·
        refine ⟨3185626159248132731031715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247501545664176974708953 3185626159248132731031715)
        ·
          refine ⟨4778439238872199096547573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185626159248132731031715 4778439238872199096547573)
          ·
            refine ⟨447978678644268665301335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4778439238872199096547573 447978678644268665301335)
            ·
              refine ⟨671968017966402997952003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447978678644268665301335 671968017966402997952003)
              ·
                refine ⟨1007952026949604496928005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671968017966402997952003 1007952026949604496928005)
                ·
                  refine ⟨188991005053050843174001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007952026949604496928005 188991005053050843174001)
                  ·
                    rfl

theorem cell20_414066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_414066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414066 prefixEnd_414066 := by exact prefixLift 414066
  have htrace : WordTrace (prefixWord ++ tailWord_414066) baseStart_414066 baseEnd_414066 := by
    simpa [prefixWord, tailWord_414066, baseEnd_414066] using wordTrace_append hprefix tailTrace_414066
  have hstable : (prefixWord ++ tailWord_414066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414066).length < 2 ^ (prefixWord ++ tailWord_414066).sum := by decide
  have hdescent : baseEnd_414066 < baseStart_414066 := by decide
  rcases family_descends (prefixWord ++ tailWord_414066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414115 : List Nat := [1, 1, 1, 4, 1, 12]
def baseStart_414115 : Nat := 118140960795 + 414115 * 2 ^ 59
def prefixEnd_414115 : Nat := 4983230072969 + 3 ^ 40 * 414115 * 2
def baseEnd_414115 : Nat := 7000495184749053723721

theorem tailTrace_414115 : CollatzResearch.WordTrace tailWord_414115 prefixEnd_414115 7000495184749053723721 := by
  unfold tailWord_414115
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104014894739555056387799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10069343263159703370925199 15104014894739555056387799)
  ·
    refine ⟨22656022342109332584581699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104014894739555056387799 22656022342109332584581699)
    ·
      refine ⟨33984033513163998876872549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22656022342109332584581699 33984033513163998876872549)
      ·
        refine ⟨6372006283718249789413603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33984033513163998876872549 6372006283718249789413603)
        ·
          refine ⟨9558009425577374684120405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372006283718249789413603 9558009425577374684120405)
          ·
            refine ⟨7000495184749053723721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9558009425577374684120405 7000495184749053723721)
            ·
              rfl

theorem cell20_414115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_414115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414115 prefixEnd_414115 := by exact prefixLift 414115
  have htrace : WordTrace (prefixWord ++ tailWord_414115) baseStart_414115 baseEnd_414115 := by
    simpa [prefixWord, tailWord_414115, baseEnd_414115] using wordTrace_append hprefix tailTrace_414115
  have hstable : (prefixWord ++ tailWord_414115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414115).length < 2 ^ (prefixWord ++ tailWord_414115).sum := by decide
  have hdescent : baseEnd_414115 < baseStart_414115 := by decide
  rcases family_descends (prefixWord ++ tailWord_414115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414153 : List Nat := [1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_414153 : Nat := 118140960795 + 414153 * 2 ^ 59
def prefixEnd_414153 : Nat := 4983230072969 + 3 ^ 40 * 414153 * 2
def baseEnd_414153 : Nat := 63010238074555069091215

theorem tailTrace_414153 : CollatzResearch.WordTrace tailWord_414153 prefixEnd_414153 63010238074555069091215 := by
  unfold tailWord_414153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105400868601887546271113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10070267245734591697514075 15105400868601887546271113)
  ·
    refine ⟨11329050651451415659703335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15105400868601887546271113 11329050651451415659703335)
    ·
      refine ⟨16993575977177123489555003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11329050651451415659703335 16993575977177123489555003)
      ·
        refine ⟨25490363965765685234332505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993575977177123489555003 25490363965765685234332505)
        ·
          refine ⟨19117772974324263925749379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25490363965765685234332505 19117772974324263925749379)
          ·
            refine ⟨28676659461486395888624069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19117772974324263925749379 28676659461486395888624069)
            ·
              refine ⟨5376873649028699229117013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28676659461486395888624069 5376873649028699229117013)
              ·
                refine ⟨63010238074555069091215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5376873649028699229117013 63010238074555069091215)
                ·
                  rfl

theorem cell20_414153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_414153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414153 prefixEnd_414153 := by exact prefixLift 414153
  have htrace : WordTrace (prefixWord ++ tailWord_414153) baseStart_414153 baseEnd_414153 := by
    simpa [prefixWord, tailWord_414153, baseEnd_414153] using wordTrace_append hprefix tailTrace_414153
  have hstable : (prefixWord ++ tailWord_414153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414153).length < 2 ^ (prefixWord ++ tailWord_414153).sum := by decide
  have hdescent : baseEnd_414153 < baseStart_414153 := by decide
  rcases family_descends (prefixWord ++ tailWord_414153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414177 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_414177 : Nat := 118140960795 + 414177 * 2 ^ 59
def prefixEnd_414177 : Nat := 4983230072969 + 3 ^ 40 * 414177 * 2
def baseEnd_414177 : Nat := 189041668477627790473547

theorem tailTrace_414177 : CollatzResearch.WordTrace tailWord_414177 prefixEnd_414177 189041668477627790473547 := by
  unfold tailWord_414177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106276220514939645144785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10070850813676626430096523 15106276220514939645144785)
  ·
    refine ⟨11329707165386204733858589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15106276220514939645144785 11329707165386204733858589)
    ·
      refine ⟨4248640187019826775196971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11329707165386204733858589 4248640187019826775196971)
      ·
        refine ⟨6372960280529740162795457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248640187019826775196971 6372960280529740162795457)
        ·
          refine ⟨4779720210397305122096593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6372960280529740162795457 4779720210397305122096593)
          ·
            refine ⟨3584790157797978841572445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779720210397305122096593 3584790157797978841572445)
            ·
              refine ⟨1344296309174242065589667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3584790157797978841572445 1344296309174242065589667)
              ·
                refine ⟨2016444463761363098384501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344296309174242065589667 2016444463761363098384501)
                ·
                  refine ⟨189041668477627790473547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016444463761363098384501 189041668477627790473547)
                  ·
                    rfl

theorem cell20_414177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_414177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414177 prefixEnd_414177 := by exact prefixLift 414177
  have htrace : WordTrace (prefixWord ++ tailWord_414177) baseStart_414177 baseEnd_414177 := by
    simpa [prefixWord, tailWord_414177, baseEnd_414177] using wordTrace_append hprefix tailTrace_414177
  have hstable : (prefixWord ++ tailWord_414177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414177).length < 2 ^ (prefixWord ++ tailWord_414177).sum := by decide
  have hdescent : baseEnd_414177 < baseStart_414177 := by decide
  rcases family_descends (prefixWord ++ tailWord_414177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414191 : List Nat := [1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_414191 : Nat := 118140960795 + 414191 * 2 ^ 59
def prefixEnd_414191 : Nat := 4983230072969 + 3 ^ 40 * 414191 * 2
def baseEnd_414191 : Nat := 63016019486368654668941

theorem tailTrace_414191 : CollatzResearch.WordTrace tailWord_414191 prefixEnd_414191 63016019486368654668941 := by
  unfold tailWord_414191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106786842464220036154427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10071191228309480024102951 15106786842464220036154427)
  ·
    refine ⟨22660180263696330054231641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106786842464220036154427 22660180263696330054231641)
    ·
      refine ⟨16995135197772247540673731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22660180263696330054231641 16995135197772247540673731)
      ·
        refine ⟨25492702796658371311010597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995135197772247540673731 25492702796658371311010597)
        ·
          refine ⟨4779881774373444620814487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25492702796658371311010597 4779881774373444620814487)
          ·
            refine ⟨7169822661560166931221731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779881774373444620814487 7169822661560166931221731)
            ·
              refine ⟨10754733992340250396832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169822661560166931221731 10754733992340250396832597)
              ·
                refine ⟨63016019486368654668941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10754733992340250396832597 63016019486368654668941)
                ·
                  rfl

theorem cell20_414191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_414191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414191 prefixEnd_414191 := by exact prefixLift 414191
  have htrace : WordTrace (prefixWord ++ tailWord_414191) baseStart_414191 baseEnd_414191 := by
    simpa [prefixWord, tailWord_414191, baseEnd_414191] using wordTrace_append hprefix tailTrace_414191
  have hstable : (prefixWord ++ tailWord_414191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414191).length < 2 ^ (prefixWord ++ tailWord_414191).sum := by decide
  have hdescent : baseEnd_414191 < baseStart_414191 := by decide
  rcases family_descends (prefixWord ++ tailWord_414191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414338 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_414338 : Nat := 118140960795 + 414338 * 2 ^ 59
def prefixEnd_414338 : Nat := 4983230072969 + 3 ^ 40 * 414338 * 2
def baseEnd_414338 : Nat := 189115153264626786106223

theorem tailTrace_414338 : CollatzResearch.WordTrace tailWord_414338 prefixEnd_414338 189115153264626786106223 := by
  unfold tailWord_414338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778037093232916035438917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10074765581954442761170445 3778037093232916035438917)
  ·
    refine ⟨708381954981171756644797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3778037093232916035438917 708381954981171756644797)
    ·
      refine ⟨265643233117939408741799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708381954981171756644797 265643233117939408741799)
      ·
        refine ⟨398464849676909113112699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265643233117939408741799 398464849676909113112699)
        ·
          refine ⟨597697274515363669669049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398464849676909113112699 597697274515363669669049)
          ·
            refine ⟨448272955886522752251787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597697274515363669669049 448272955886522752251787)
            ·
              refine ⟨672409433829784128377681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448272955886522752251787 672409433829784128377681)
              ·
                refine ⟨504307075372338096283261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672409433829784128377681 504307075372338096283261)
                ·
                  refine ⟨189115153264626786106223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504307075372338096283261 189115153264626786106223)
                  ·
                    rfl

theorem cell20_414338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_414338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414338 prefixEnd_414338 := by exact prefixLift 414338
  have htrace : WordTrace (prefixWord ++ tailWord_414338) baseStart_414338 baseEnd_414338 := by
    simpa [prefixWord, tailWord_414338, baseEnd_414338] using wordTrace_append hprefix tailTrace_414338
  have hstable : (prefixWord ++ tailWord_414338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414338).length < 2 ^ (prefixWord ++ tailWord_414338).sum := by decide
  have hdescent : baseEnd_414338 < baseStart_414338 := by decide
  rcases family_descends (prefixWord ++ tailWord_414338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414343 : List Nat := [1, 1, 4, 2, 1, 2, 9]
def baseStart_414343 : Nat := 118140960795 + 414343 * 2 ^ 59
def prefixEnd_414343 : Nat := 4983230072969 + 3 ^ 40 * 414343 * 2
def baseEnd_414343 : Nat := 21013048377874332326615

theorem tailTrace_414343 : CollatzResearch.WordTrace tailWord_414343 prefixEnd_414343 21013048377874332326615 := by
  unfold tailWord_414343
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112330737913549995687683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10074887158609033330458455 15112330737913549995687683)
  ·
    refine ⟨22668496106870324993531525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112330737913549995687683 22668496106870324993531525)
    ·
      refine ⟨4250343020038185936287161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22668496106870324993531525 4250343020038185936287161)
      ·
        refine ⟨3187757265028639452215371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4250343020038185936287161 3187757265028639452215371)
        ·
          refine ⟨4781635897542959178323057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187757265028639452215371 4781635897542959178323057)
          ·
            refine ⟨3586226923157219383742293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781635897542959178323057 3586226923157219383742293)
            ·
              refine ⟨21013048377874332326615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3586226923157219383742293 21013048377874332326615)
              ·
                rfl

theorem cell20_414343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_414343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414343 prefixEnd_414343 := by exact prefixLift 414343
  have htrace : WordTrace (prefixWord ++ tailWord_414343) baseStart_414343 baseEnd_414343 := by
    simpa [prefixWord, tailWord_414343, baseEnd_414343] using wordTrace_append hprefix tailTrace_414343
  have hstable : (prefixWord ++ tailWord_414343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414343).length < 2 ^ (prefixWord ++ tailWord_414343).sum := by decide
  have hdescent : baseEnd_414343 < baseStart_414343 := by decide
  rcases family_descends (prefixWord ++ tailWord_414343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414346 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_414346 : Nat := 118140960795 + 414346 * 2 ^ 59
def prefixEnd_414346 : Nat := 4983230072969 + 3 ^ 40 * 414346 * 2
def baseEnd_414346 : Nat := 189118804682614313839523

theorem tailTrace_414346 : CollatzResearch.WordTrace tailWord_414346 prefixEnd_414346 189118804682614313839523 := by
  unfold tailWord_414346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778110039225670377011723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10074960104601787672031261 3778110039225670377011723)
  ·
    refine ⟨5667165058838505565517585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778110039225670377011723 5667165058838505565517585)
    ·
      refine ⟨4250373794128879174138189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5667165058838505565517585 4250373794128879174138189)
      ·
        refine ⟨1593890172798329690301821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4250373794128879174138189 1593890172798329690301821)
        ·
          refine ⟨597708814799373633863183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1593890172798329690301821 597708814799373633863183)
          ·
            refine ⟨896563222199060450794775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597708814799373633863183 896563222199060450794775)
            ·
              refine ⟨1344844833298590676192163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896563222199060450794775 1344844833298590676192163)
              ·
                refine ⟨2017267249947886014288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344844833298590676192163 2017267249947886014288245)
                ·
                  refine ⟨189118804682614313839523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017267249947886014288245 189118804682614313839523)
                  ·
                    rfl

theorem cell20_414346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_414346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414346 prefixEnd_414346 := by exact prefixLift 414346
  have htrace : WordTrace (prefixWord ++ tailWord_414346) baseStart_414346 baseEnd_414346 := by
    simpa [prefixWord, tailWord_414346, baseEnd_414346] using wordTrace_append hprefix tailTrace_414346
  have hstable : (prefixWord ++ tailWord_414346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414346).length < 2 ^ (prefixWord ++ tailWord_414346).sum := by decide
  have hdescent : baseEnd_414346 < baseStart_414346 := by decide
  rcases family_descends (prefixWord ++ tailWord_414346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414418 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_414418 : Nat := 118140960795 + 414418 * 2 ^ 59
def prefixEnd_414418 : Nat := 4983230072969 + 3 ^ 40 * 414418 * 2
def baseEnd_414418 : Nat := 189151667444502063439229

theorem tailTrace_414418 : CollatzResearch.WordTrace tailWord_414418 prefixEnd_414418 189151667444502063439229 := by
  unfold tailWord_414418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778766553160459451166977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10076710808427891869778605 3778766553160459451166977)
  ·
    refine ⟨2834074914870344588375233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3778766553160459451166977 2834074914870344588375233)
    ·
      refine ⟨2125556186152758441281425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2834074914870344588375233 2125556186152758441281425)
      ·
        refine ⟨1594167139614568830961069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2125556186152758441281425 1594167139614568830961069)
        ·
          refine ⟨597812677355463311610401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1594167139614568830961069 597812677355463311610401)
          ·
            refine ⟨448359508016597483707801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597812677355463311610401 448359508016597483707801)
            ·
              refine ⟨336269631012448112780851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448359508016597483707801 336269631012448112780851)
              ·
                refine ⟨504404446518672169171277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336269631012448112780851 504404446518672169171277)
                ·
                  refine ⟨189151667444502063439229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504404446518672169171277 189151667444502063439229)
                  ·
                    rfl

theorem cell20_414418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_414418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414418 prefixEnd_414418 := by exact prefixLift 414418
  have htrace : WordTrace (prefixWord ++ tailWord_414418) baseStart_414418 baseEnd_414418 := by
    simpa [prefixWord, tailWord_414418, baseEnd_414418] using wordTrace_append hprefix tailTrace_414418
  have hstable : (prefixWord ++ tailWord_414418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414418).length < 2 ^ (prefixWord ++ tailWord_414418).sum := by decide
  have hdescent : baseEnd_414418 < baseStart_414418 := by decide
  rcases family_descends (prefixWord ++ tailWord_414418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414453 : List Nat := [1, 3, 6, 1, 9]
def baseStart_414453 : Nat := 118140960795 + 414453 * 2 ^ 59
def prefixEnd_414453 : Nat := 4983230072969 + 3 ^ 40 * 414453 * 2
def baseEnd_414453 : Nat := 2335402992570339472499

theorem tailTrace_414453 : CollatzResearch.WordTrace tailWord_414453 prefixEnd_414453 2335402992570339472499 := by
  unfold tailWord_414453
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116342767515038782192013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10077561845010025854794675 15116342767515038782192013)
  ·
    refine ⟨5668628537818139543322005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15116342767515038782192013 5668628537818139543322005)
    ·
      refine ⟨265716962710225291093219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5668628537818139543322005 265716962710225291093219)
      ·
        refine ⟨398575444065337936639829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265716962710225291093219 398575444065337936639829)
        ·
          refine ⟨2335402992570339472499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 398575444065337936639829 2335402992570339472499)
          ·
            rfl

theorem cell20_414453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 9].length) (baseStart_414453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414453 prefixEnd_414453 := by exact prefixLift 414453
  have htrace : WordTrace (prefixWord ++ tailWord_414453) baseStart_414453 baseEnd_414453 := by
    simpa [prefixWord, tailWord_414453, baseEnd_414453] using wordTrace_append hprefix tailTrace_414453
  have hstable : (prefixWord ++ tailWord_414453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414453).length < 2 ^ (prefixWord ++ tailWord_414453).sum := by decide
  have hdescent : baseEnd_414453 < baseStart_414453 := by decide
  rcases family_descends (prefixWord ++ tailWord_414453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414460 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_414460 : Nat := 118140960795 + 414460 * 2 ^ 59
def prefixEnd_414460 : Nat := 4983230072969 + 3 ^ 40 * 414460 * 2
def baseEnd_414460 : Nat := 189170837388936584039057

theorem tailTrace_414460 : CollatzResearch.WordTrace tailWord_414460 prefixEnd_414460 189170837388936584039057 := by
  unfold tailWord_414460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558299039244839488848417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10077732052326452651797889 7558299039244839488848417)
  ·
    refine ⟨5668724279433629616636313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7558299039244839488848417 5668724279433629616636313)
    ·
      refine ⟨4251543209575222212477235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5668724279433629616636313 4251543209575222212477235)
      ·
        refine ⟨6377314814362833318715853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251543209575222212477235 6377314814362833318715853)
        ·
          refine ⟨2391493055386062494518445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6377314814362833318715853 2391493055386062494518445)
          ·
            refine ⟨896809895769773435444417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2391493055386062494518445 896809895769773435444417)
            ·
              refine ⟨672607421827330076583313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896809895769773435444417 672607421827330076583313)
              ·
                refine ⟨504455566370497557437485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672607421827330076583313 504455566370497557437485)
                ·
                  refine ⟨189170837388936584039057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504455566370497557437485 189170837388936584039057)
                  ·
                    rfl

theorem cell20_414460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_414460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414460 prefixEnd_414460 := by exact prefixLift 414460
  have htrace : WordTrace (prefixWord ++ tailWord_414460) baseStart_414460 baseEnd_414460 := by
    simpa [prefixWord, tailWord_414460, baseEnd_414460] using wordTrace_append hprefix tailTrace_414460
  have hstable : (prefixWord ++ tailWord_414460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414460).length < 2 ^ (prefixWord ++ tailWord_414460).sum := by decide
  have hdescent : baseEnd_414460 < baseStart_414460 := by decide
  rcases family_descends (prefixWord ++ tailWord_414460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414481 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_414481 : Nat := 118140960795 + 414481 * 2 ^ 59
def prefixEnd_414481 : Nat := 4983230072969 + 3 ^ 40 * 414481 * 2
def baseEnd_414481 : Nat := 189180422361153844338971

theorem tailTrace_414481 : CollatzResearch.WordTrace tailWord_414481 prefixEnd_414481 189180422361153844338971 := by
  unfold tailWord_414481
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117364011413599564211297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10078242674275733042807531 15117364011413599564211297)
  ·
    refine ⟨11338023008560199673158473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15117364011413599564211297 11338023008560199673158473)
    ·
      refine ⟨8503517256420149754868855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11338023008560199673158473 8503517256420149754868855)
      ·
        refine ⟨12755275884630224632303283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503517256420149754868855 12755275884630224632303283)
        ·
          refine ⟨19132913826945336948454925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755275884630224632303283 19132913826945336948454925)
          ·
            refine ⟨7174842685104501355670597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19132913826945336948454925 7174842685104501355670597)
            ·
              refine ⟨1345283003457094004188237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7174842685104501355670597 1345283003457094004188237)
              ·
                refine ⟨504481126296410251570589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1345283003457094004188237 504481126296410251570589)
                ·
                  refine ⟨189180422361153844338971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504481126296410251570589 189180422361153844338971)
                  ·
                    rfl

theorem cell20_414481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_414481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414481 prefixEnd_414481 := by exact prefixLift 414481
  have htrace : WordTrace (prefixWord ++ tailWord_414481) baseStart_414481 baseEnd_414481 := by
    simpa [prefixWord, tailWord_414481, baseEnd_414481] using wordTrace_append hprefix tailTrace_414481
  have hstable : (prefixWord ++ tailWord_414481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414481).length < 2 ^ (prefixWord ++ tailWord_414481).sum := by decide
  have hdescent : baseEnd_414481 < baseStart_414481 := by decide
  rcases family_descends (prefixWord ++ tailWord_414481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414536 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_414536 : Nat := 118140960795 + 414536 * 2 ^ 59
def prefixEnd_414536 : Nat := 4983230072969 + 3 ^ 40 * 414536 * 2
def baseEnd_414536 : Nat := 189205525859818097505413

theorem tailTrace_414536 : CollatzResearch.WordTrace tailWord_414536 prefixEnd_414536 189205525859818097505413 := by
  unfold tailWord_414536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559685013107171978731731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10079580017476229304975641 7559685013107171978731731)
  ·
    refine ⟨11339527519660757968097597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7559685013107171978731731 11339527519660757968097597)
    ·
      refine ⟨4252322819872784238036599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11339527519660757968097597 4252322819872784238036599)
      ·
        refine ⟨6378484229809176357054899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252322819872784238036599 6378484229809176357054899)
        ·
          refine ⟨9567726344713764535582349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378484229809176357054899 9567726344713764535582349)
          ·
            refine ⟨3587897379267661700843381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9567726344713764535582349 3587897379267661700843381)
            ·
              refine ⟨336365379306343284454067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3587897379267661700843381 336365379306343284454067)
              ·
                refine ⟨504548068959514926681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336365379306343284454067 504548068959514926681101)
                ·
                  refine ⟨189205525859818097505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504548068959514926681101 189205525859818097505413)
                  ·
                    rfl

theorem cell20_414536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_414536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414536 prefixEnd_414536 := by exact prefixLift 414536
  have htrace : WordTrace (prefixWord ++ tailWord_414536) baseStart_414536 baseEnd_414536 := by
    simpa [prefixWord, tailWord_414536, baseEnd_414536] using wordTrace_append hprefix tailTrace_414536
  have hstable : (prefixWord ++ tailWord_414536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414536).length < 2 ^ (prefixWord ++ tailWord_414536).sum := by decide
  have hdescent : baseEnd_414536 < baseStart_414536 := by decide
  rcases family_descends (prefixWord ++ tailWord_414536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414581 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_414581 : Nat := 118140960795 + 414581 * 2 ^ 59
def prefixEnd_414581 : Nat := 4983230072969 + 3 ^ 40 * 414581 * 2
def baseEnd_414581 : Nat := 189226065085997941005229

theorem tailTrace_414581 : CollatzResearch.WordTrace tailWord_414581 prefixEnd_414581 189226065085997941005229 := by
  unfold tailWord_414581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121011311051316642851597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10080674207367544428567731 15121011311051316642851597)
  ·
    refine ⟨5670379241644243741069349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15121011311051316642851597 5670379241644243741069349)
    ·
      refine ⟨1063196107808295701450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5670379241644243741069349 1063196107808295701450503)
      ·
        refine ⟨1594794161712443552175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063196107808295701450503 1594794161712443552175755)
        ·
          refine ⟨2392191242568665328263633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594794161712443552175755 2392191242568665328263633)
          ·
            refine ⟨1794143431926498996197725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392191242568665328263633 1794143431926498996197725)
            ·
              refine ⟨672803786972437123574147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1794143431926498996197725 672803786972437123574147)
              ·
                refine ⟨1009205680458655685361221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672803786972437123574147 1009205680458655685361221)
                ·
                  refine ⟨189226065085997941005229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009205680458655685361221 189226065085997941005229)
                  ·
                    rfl

theorem cell20_414581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_414581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414581 prefixEnd_414581 := by exact prefixLift 414581
  have htrace : WordTrace (prefixWord ++ tailWord_414581) baseStart_414581 baseEnd_414581 := by
    simpa [prefixWord, tailWord_414581, baseEnd_414581] using wordTrace_append hprefix tailTrace_414581
  have hstable : (prefixWord ++ tailWord_414581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414581).length < 2 ^ (prefixWord ++ tailWord_414581).sum := by decide
  have hdescent : baseEnd_414581 < baseStart_414581 := by decide
  rcases family_descends (prefixWord ++ tailWord_414581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414595 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_414595 : Nat := 118140960795 + 414595 * 2 ^ 59
def prefixEnd_414595 : Nat := 4983230072969 + 3 ^ 40 * 414595 * 2
def baseEnd_414595 : Nat := 189232455067476114538505

theorem tailTrace_414595 : CollatzResearch.WordTrace tailWord_414595 prefixEnd_414595 189232455067476114538505 := by
  unfold tailWord_414595
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121521933000597033861239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10081014622000398022574159 15121521933000597033861239)
  ·
    refine ⟨22682282899500895550791859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15121521933000597033861239 22682282899500895550791859)
    ·
      refine ⟨34023424349251343326187789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22682282899500895550791859 34023424349251343326187789)
      ·
        refine ⟨12758784130969253747320421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34023424349251343326187789 12758784130969253747320421)
        ·
          refine ⟨2392272024556735077622579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12758784130969253747320421 2392272024556735077622579)
          ·
            refine ⟨3588408036835102616433869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392272024556735077622579 3588408036835102616433869)
            ·
              refine ⟨1345653013813163481162701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3588408036835102616433869 1345653013813163481162701)
              ·
                refine ⟨504619880179936305436013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1345653013813163481162701 504619880179936305436013)
                ·
                  refine ⟨189232455067476114538505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504619880179936305436013 189232455067476114538505)
                  ·
                    rfl

theorem cell20_414595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_414595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414595 prefixEnd_414595 := by exact prefixLift 414595
  have htrace : WordTrace (prefixWord ++ tailWord_414595) baseStart_414595 baseEnd_414595 := by
    simpa [prefixWord, tailWord_414595, baseEnd_414595] using wordTrace_append hprefix tailTrace_414595
  have hstable : (prefixWord ++ tailWord_414595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414595).length < 2 ^ (prefixWord ++ tailWord_414595).sum := by decide
  have hdescent : baseEnd_414595 < baseStart_414595 := by decide
  rcases family_descends (prefixWord ++ tailWord_414595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414633 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_414633 : Nat := 118140960795 + 414633 * 2 ^ 59
def prefixEnd_414633 : Nat := 4983230072969 + 3 ^ 40 * 414633 * 2
def baseEnd_414633 : Nat := 189249799302916871271683

theorem tailTrace_414633 : CollatzResearch.WordTrace tailWord_414633 prefixEnd_414633 189249799302916871271683 := by
  unfold tailWord_414633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122907906862929523744553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10081938604575286349163035 15122907906862929523744553)
  ·
    refine ⟨11342180930147197142808415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15122907906862929523744553 11342180930147197142808415)
    ·
      refine ⟨17013271395220795714212623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342180930147197142808415 17013271395220795714212623)
      ·
        refine ⟨25519907092831193571318935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013271395220795714212623 25519907092831193571318935)
        ·
          refine ⟨38279860639246790356978403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25519907092831193571318935 38279860639246790356978403)
          ·
            refine ⟨57419790958870185535467605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38279860639246790356978403 57419790958870185535467605)
            ·
              refine ⟨672888175299259986743761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57419790958870185535467605 672888175299259986743761)
              ·
                refine ⟨504666131474444990057821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672888175299259986743761 504666131474444990057821)
                ·
                  refine ⟨189249799302916871271683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504666131474444990057821 189249799302916871271683)
                  ·
                    rfl

theorem cell20_414633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_414633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414633 prefixEnd_414633 := by exact prefixLift 414633
  have htrace : WordTrace (prefixWord ++ tailWord_414633) baseStart_414633 baseEnd_414633 := by
    simpa [prefixWord, tailWord_414633, baseEnd_414633] using wordTrace_append hprefix tailTrace_414633
  have hstable : (prefixWord ++ tailWord_414633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414633).length < 2 ^ (prefixWord ++ tailWord_414633).sum := by decide
  have hdescent : baseEnd_414633 < baseStart_414633 := by decide
  rcases family_descends (prefixWord ++ tailWord_414633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414647 : List Nat := [1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_414647 : Nat := 118140960795 + 414647 * 2 ^ 59
def prefixEnd_414647 : Nat := 4983230072969 + 3 ^ 40 * 414647 * 2
def baseEnd_414647 : Nat := 63085396428131681601653

theorem tailTrace_414647 : CollatzResearch.WordTrace tailWord_414647 prefixEnd_414647 63085396428131681601653 := by
  unfold tailWord_414647
  simp only [CollatzResearch.WordTrace]
  refine ⟨15123418528812209914754195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10082279019208139943169463 15123418528812209914754195)
  ·
    refine ⟨22685127793218314872131293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15123418528812209914754195 22685127793218314872131293)
    ·
      refine ⟨8506922922456868077049235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22685127793218314872131293 8506922922456868077049235)
      ·
        refine ⟨12760384383685302115573853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8506922922456868077049235 12760384383685302115573853)
        ·
          refine ⟨4785144143881988293340195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12760384383685302115573853 4785144143881988293340195)
          ·
            refine ⟨7177716215822982440010293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785144143881988293340195 7177716215822982440010293)
            ·
              refine ⟨672910895233404603750965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7177716215822982440010293 672910895233404603750965)
              ·
                refine ⟨63085396428131681601653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672910895233404603750965 63085396428131681601653)
                ·
                  rfl

theorem cell20_414647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_414647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414647 prefixEnd_414647 := by exact prefixLift 414647
  have htrace : WordTrace (prefixWord ++ tailWord_414647) baseStart_414647 baseEnd_414647 := by
    simpa [prefixWord, tailWord_414647, baseEnd_414647] using wordTrace_append hprefix tailTrace_414647
  have hstable : (prefixWord ++ tailWord_414647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414647).length < 2 ^ (prefixWord ++ tailWord_414647).sum := by decide
  have hdescent : baseEnd_414647 < baseStart_414647 := by decide
  rcases family_descends (prefixWord ++ tailWord_414647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414660 : List Nat := [2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_414660 : Nat := 118140960795 + 414660 * 2 ^ 59
def prefixEnd_414660 : Nat := 4983230072969 + 3 ^ 40 * 414660 * 2
def baseEnd_414660 : Nat := 63087374279541592457191

theorem tailTrace_414660 : CollatzResearch.WordTrace tailWord_414660 prefixEnd_414660 63087374279541592457191 := by
  unfold tailWord_414660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561946338882556567488717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10082595118510075423318289 7561946338882556567488717)
  ·
    refine ⟨2835729877080958712808269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7561946338882556567488717 2835729877080958712808269)
    ·
      refine ⟨1063398703905359517303101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2835729877080958712808269 1063398703905359517303101)
      ·
        refine ⟨398774513964509818988663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1063398703905359517303101 398774513964509818988663)
        ·
          refine ⟨598161770946764728482995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398774513964509818988663 598161770946764728482995)
          ·
            refine ⟨897242656420147092724493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598161770946764728482995 897242656420147092724493)
            ·
              refine ⟨336465996157555159771685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897242656420147092724493 336465996157555159771685)
              ·
                refine ⟨63087374279541592457191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336465996157555159771685 63087374279541592457191)
                ·
                  rfl

theorem cell20_414660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_414660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414660 prefixEnd_414660 := by exact prefixLift 414660
  have htrace : WordTrace (prefixWord ++ tailWord_414660) baseStart_414660 baseEnd_414660 := by
    simpa [prefixWord, tailWord_414660, baseEnd_414660] using wordTrace_append hprefix tailTrace_414660
  have hstable : (prefixWord ++ tailWord_414660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414660).length < 2 ^ (prefixWord ++ tailWord_414660).sum := by decide
  have hdescent : baseEnd_414660 < baseStart_414660 := by decide
  rcases family_descends (prefixWord ++ tailWord_414660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414674 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_414674 : Nat := 118140960795 + 414674 * 2 ^ 59
def prefixEnd_414674 : Nat := 4983230072969 + 3 ^ 40 * 414674 * 2
def baseEnd_414674 : Nat := 189268512820102950904849

theorem tailTrace_414674 : CollatzResearch.WordTrace tailWord_414674 prefixEnd_414674 189268512820102950904849 := by
  unfold tailWord_414674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781100824928598381496769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10082935533142929017324717 3781100824928598381496769)
  ·
    refine ⟨2835825618696448786122577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3781100824928598381496769 2835825618696448786122577)
    ·
      refine ⟨2126869214022336589591933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2835825618696448786122577 2126869214022336589591933)
      ·
        refine ⟨797575955258376221096975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2126869214022336589591933 797575955258376221096975)
        ·
          refine ⟨1196363932887564331645463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797575955258376221096975 1196363932887564331645463)
          ·
            refine ⟨1794545899331346497468195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196363932887564331645463 1794545899331346497468195)
            ·
              refine ⟨2691818848997019746202293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794545899331346497468195 2691818848997019746202293)
              ·
                refine ⟨252358017093470601206465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2691818848997019746202293 252358017093470601206465)
                ·
                  refine ⟨189268512820102950904849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252358017093470601206465 189268512820102950904849)
                  ·
                    rfl

theorem cell20_414674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_414674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414674 prefixEnd_414674 := by exact prefixLift 414674
  have htrace : WordTrace (prefixWord ++ tailWord_414674) baseStart_414674 baseEnd_414674 := by
    simpa [prefixWord, tailWord_414674, baseEnd_414674] using wordTrace_append hprefix tailTrace_414674
  have hstable : (prefixWord ++ tailWord_414674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414674).length < 2 ^ (prefixWord ++ tailWord_414674).sum := by decide
  have hdescent : baseEnd_414674 < baseStart_414674 := by decide
  rcases family_descends (prefixWord ++ tailWord_414674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414695 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_414695 : Nat := 118140960795 + 414695 * 2 ^ 59
def prefixEnd_414695 : Nat := 4983230072969 + 3 ^ 40 * 414695 * 2
def baseEnd_414695 : Nat := 189278097792320211204763

theorem tailTrace_414695 : CollatzResearch.WordTrace tailWord_414695 prefixEnd_414695 189278097792320211204763 := by
  unfold tailWord_414695
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125169232638314112501539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10083446155092209408334359 15125169232638314112501539)
  ·
    refine ⟨22687753848957471168752309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125169232638314112501539 22687753848957471168752309)
    ·
      refine ⟨2126976923339762922070529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22687753848957471168752309 2126976923339762922070529)
      ·
        refine ⟨1595232692504822191552897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2126976923339762922070529 1595232692504822191552897)
        ·
          refine ⟨1196424519378616643664673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595232692504822191552897 1196424519378616643664673)
          ·
            refine ⟨897318389533962482748505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196424519378616643664673 897318389533962482748505)
            ·
              refine ⟨672988792150471862061379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897318389533962482748505 672988792150471862061379)
              ·
                refine ⟨1009483188225707793092069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672988792150471862061379 1009483188225707793092069)
                ·
                  refine ⟨189278097792320211204763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009483188225707793092069 189278097792320211204763)
                  ·
                    rfl

theorem cell20_414695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_414695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414695 prefixEnd_414695 := by exact prefixLift 414695
  have htrace : WordTrace (prefixWord ++ tailWord_414695) baseStart_414695 baseEnd_414695 := by
    simpa [prefixWord, tailWord_414695, baseEnd_414695] using wordTrace_append hprefix tailTrace_414695
  have hstable : (prefixWord ++ tailWord_414695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414695).length < 2 ^ (prefixWord ++ tailWord_414695).sum := by decide
  have hdescent : baseEnd_414695 < baseStart_414695 := by decide
  rcases family_descends (prefixWord ++ tailWord_414695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414716 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_414716 : Nat := 118140960795 + 414716 * 2 ^ 59
def prefixEnd_414716 : Nat := 4983230072969 + 3 ^ 40 * 414716 * 2
def baseEnd_414716 : Nat := 189287682764537471504677

theorem tailTrace_414716 : CollatzResearch.WordTrace tailWord_414716 prefixEnd_414716 189287682764537471504677 := by
  unfold tailWord_414716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562967582781117349508001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10083956777041489799344001 7562967582781117349508001)
  ·
    refine ⟨5672225687085838012131001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7562967582781117349508001 5672225687085838012131001)
    ·
      refine ⟨4254169265314378509098251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5672225687085838012131001 4254169265314378509098251)
      ·
        refine ⟨6381253897971567763647377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254169265314378509098251 6381253897971567763647377)
        ·
          refine ⟨4785940423478675822735533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381253897971567763647377 4785940423478675822735533)
          ·
            refine ⟨1794727658804503433525825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4785940423478675822735533 1794727658804503433525825)
            ·
              refine ⟨1346045744103377575144369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794727658804503433525825 1346045744103377575144369)
              ·
                refine ⟨1009534308077533181358277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346045744103377575144369 1009534308077533181358277)
                ·
                  refine ⟨189287682764537471504677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009534308077533181358277 189287682764537471504677)
                  ·
                    rfl

theorem cell20_414716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_414716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414716 prefixEnd_414716 := by exact prefixLift 414716
  have htrace : WordTrace (prefixWord ++ tailWord_414716) baseStart_414716 baseEnd_414716 := by
    simpa [prefixWord, tailWord_414716, baseEnd_414716] using wordTrace_append hprefix tailTrace_414716
  have hstable : (prefixWord ++ tailWord_414716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414716).length < 2 ^ (prefixWord ++ tailWord_414716).sum := by decide
  have hdescent : baseEnd_414716 < baseStart_414716 := by decide
  rcases family_descends (prefixWord ++ tailWord_414716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414737 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_414737 : Nat := 118140960795 + 414737 * 2 ^ 59
def prefixEnd_414737 : Nat := 4983230072969 + 3 ^ 40 * 414737 * 2
def baseEnd_414737 : Nat := 189297267736754731804591

theorem tailTrace_414737 : CollatzResearch.WordTrace tailWord_414737 prefixEnd_414737 189297267736754731804591 := by
  unfold tailWord_414737
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126701098486155285530465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084467398990770190353643 15126701098486155285530465)
  ·
    refine ⟨11345025823864616464147849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15126701098486155285530465 11345025823864616464147849)
    ·
      refine ⟨8508769367898462348110887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11345025823864616464147849 8508769367898462348110887)
      ·
        refine ⟨12763154051847693522166331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508769367898462348110887 12763154051847693522166331)
        ·
          refine ⟨19144731077771540283249497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12763154051847693522166331 19144731077771540283249497)
          ·
            refine ⟨14358548308328655212437123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19144731077771540283249497 14358548308328655212437123)
            ·
              refine ⟨21537822462492982818655685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358548308328655212437123 21537822462492982818655685)
              ·
                refine ⟨4038341711717434278497941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21537822462492982818655685 4038341711717434278497941)
                ·
                  refine ⟨189297267736754731804591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038341711717434278497941 189297267736754731804591)
                  ·
                    rfl

theorem cell20_414737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_414737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414737 prefixEnd_414737 := by exact prefixLift 414737
  have htrace : WordTrace (prefixWord ++ tailWord_414737) baseStart_414737 baseEnd_414737 := by
    simpa [prefixWord, tailWord_414737, baseEnd_414737] using wordTrace_append hprefix tailTrace_414737
  have hstable : (prefixWord ++ tailWord_414737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414737).length < 2 ^ (prefixWord ++ tailWord_414737).sum := by decide
  have hdescent : baseEnd_414737 < baseStart_414737 := by decide
  rcases family_descends (prefixWord ++ tailWord_414737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414775 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_414775 : Nat := 118140960795 + 414775 * 2 ^ 59
def prefixEnd_414775 : Nat := 4983230072969 + 3 ^ 40 * 414775 * 2
def baseEnd_414775 : Nat := 189314611972195488537769

theorem tailTrace_414775 : CollatzResearch.WordTrace tailWord_414775 prefixEnd_414775 189314611972195488537769 := by
  unfold tailWord_414775
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128087072348487775413779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10085391381565658516942519 15128087072348487775413779)
  ·
    refine ⟨22692130608522731663120669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15128087072348487775413779 22692130608522731663120669)
    ·
      refine ⟨8509548978196024373670251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22692130608522731663120669 8509548978196024373670251)
      ·
        refine ⟨12764323467294036560505377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509548978196024373670251 12764323467294036560505377)
        ·
          refine ⟨9573242600470527420379033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12764323467294036560505377 9573242600470527420379033)
          ·
            refine ⟨7179931950352895565284275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9573242600470527420379033 7179931950352895565284275)
            ·
              refine ⟨10769897925529343347926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179931950352895565284275 10769897925529343347926413)
              ·
                refine ⟨4038711722073503755472405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769897925529343347926413 4038711722073503755472405)
                ·
                  refine ⟨189314611972195488537769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038711722073503755472405 189314611972195488537769)
                  ·
                    rfl

theorem cell20_414775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_414775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414775 prefixEnd_414775 := by exact prefixLift 414775
  have htrace : WordTrace (prefixWord ++ tailWord_414775) baseStart_414775 baseEnd_414775 := by
    simpa [prefixWord, tailWord_414775, baseEnd_414775] using wordTrace_append hprefix tailTrace_414775
  have hstable : (prefixWord ++ tailWord_414775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414775).length < 2 ^ (prefixWord ++ tailWord_414775).sum := by decide
  have hdescent : baseEnd_414775 < baseStart_414775 := by decide
  rcases family_descends (prefixWord ++ tailWord_414775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414802 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_414802 : Nat := 118140960795 + 414802 * 2 ^ 59
def prefixEnd_414802 : Nat := 4983230072969 + 3 ^ 40 * 414802 * 2
def baseEnd_414802 : Nat := 189326935507903394637659

theorem tailTrace_414802 : CollatzResearch.WordTrace tailWord_414802 prefixEnd_414802 189326935507903394637659 := by
  unfold tailWord_414802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782267960812667846661665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10086047895500447591097773 3782267960812667846661665)
  ·
    refine ⟨2836700970609500884996249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3782267960812667846661665 2836700970609500884996249)
    ·
      refine ⟨2127525727957125663747187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836700970609500884996249 2127525727957125663747187)
      ·
        refine ⟨3191288591935688495620781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127525727957125663747187 3191288591935688495620781)
        ·
          refine ⟨1196733221975883185857793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3191288591935688495620781 1196733221975883185857793)
          ·
            refine ⟨897549916481912389393345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196733221975883185857793 897549916481912389393345)
            ·
              refine ⟨673162437361434292045009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897549916481912389393345 673162437361434292045009)
              ·
                refine ⟨504871828021075719033757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673162437361434292045009 504871828021075719033757)
                ·
                  refine ⟨189326935507903394637659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504871828021075719033757 189326935507903394637659)
                  ·
                    rfl

theorem cell20_414802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_414802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414802 prefixEnd_414802 := by exact prefixLift 414802
  have htrace : WordTrace (prefixWord ++ tailWord_414802) baseStart_414802 baseEnd_414802 := by
    simpa [prefixWord, tailWord_414802, baseEnd_414802] using wordTrace_append hprefix tailTrace_414802
  have hstable : (prefixWord ++ tailWord_414802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414802).length < 2 ^ (prefixWord ++ tailWord_414802).sum := by decide
  have hdescent : baseEnd_414802 < baseStart_414802 := by decide
  rcases family_descends (prefixWord ++ tailWord_414802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414823 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_414823 : Nat := 118140960795 + 414823 * 2 ^ 59
def prefixEnd_414823 : Nat := 4983230072969 + 3 ^ 40 * 414823 * 2
def baseEnd_414823 : Nat := 189336520480120654937573

theorem tailTrace_414823 : CollatzResearch.WordTrace tailWord_414823 prefixEnd_414823 189336520480120654937573 := by
  unfold tailWord_414823
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129837776174591973161123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10086558517449727982107415 15129837776174591973161123)
  ·
    refine ⟨22694756664261887959741685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15129837776174591973161123 22694756664261887959741685)
    ·
      refine ⟨2127633437274551996225783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22694756664261887959741685 2127633437274551996225783)
      ·
        refine ⟨3191450155911827994338675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127633437274551996225783 3191450155911827994338675)
        ·
          refine ⟨4787175233867741991508013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191450155911827994338675 4787175233867741991508013)
          ·
            refine ⟨1795190712700403246815505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4787175233867741991508013 1795190712700403246815505)
            ·
              refine ⟨1346393034525302435111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795190712700403246815505 1346393034525302435111629)
              ·
                refine ⟨504897387946988413166861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346393034525302435111629 504897387946988413166861)
                ·
                  refine ⟨189336520480120654937573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504897387946988413166861 189336520480120654937573)
                  ·
                    rfl

theorem cell20_414823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_414823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414823 prefixEnd_414823 := by exact prefixLift 414823
  have htrace : WordTrace (prefixWord ++ tailWord_414823) baseStart_414823 baseEnd_414823 := by
    simpa [prefixWord, tailWord_414823, baseEnd_414823] using wordTrace_append hprefix tailTrace_414823
  have hstable : (prefixWord ++ tailWord_414823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414823).length < 2 ^ (prefixWord ++ tailWord_414823).sum := by decide
  have hdescent : baseEnd_414823 < baseStart_414823 := by decide
  rcases family_descends (prefixWord ++ tailWord_414823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414830 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_414830 : Nat := 118140960795 + 414830 * 2 ^ 59
def prefixEnd_414830 : Nat := 4983230072969 + 3 ^ 40 * 414830 * 2
def baseEnd_414830 : Nat := 189339715470859741704211

theorem tailTrace_414830 : CollatzResearch.WordTrace tailWord_414830 prefixEnd_414830 189339715470859741704211 := by
  unfold tailWord_414830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891261635893654021083243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10086728724766154779110629 1891261635893654021083243)
  ·
    refine ⟨2836892453840481031624865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891261635893654021083243 2836892453840481031624865)
    ·
      refine ⟨2127669340380360773718649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836892453840481031624865 2127669340380360773718649)
      ·
        refine ⟨1595752005285270580288987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127669340380360773718649 1595752005285270580288987)
        ·
          refine ⟨2393628007927905870433481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595752005285270580288987 2393628007927905870433481)
          ·
            refine ⟨1795221005945929402825111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393628007927905870433481 1795221005945929402825111)
            ·
              refine ⟨2692831508918894104237667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795221005945929402825111 2692831508918894104237667)
              ·
                refine ⟨4039247263378341156356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692831508918894104237667 4039247263378341156356501)
                ·
                  refine ⟨189339715470859741704211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039247263378341156356501 189339715470859741704211)
                  ·
                    rfl

theorem cell20_414830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_414830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414830 prefixEnd_414830 := by exact prefixLift 414830
  have htrace : WordTrace (prefixWord ++ tailWord_414830) baseStart_414830 baseEnd_414830 := by
    simpa [prefixWord, tailWord_414830, baseEnd_414830] using wordTrace_append hprefix tailTrace_414830
  have hstable : (prefixWord ++ tailWord_414830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414830).length < 2 ^ (prefixWord ++ tailWord_414830).sum := by decide
  have hdescent : baseEnd_414830 < baseStart_414830 := by decide
  rcases family_descends (prefixWord ++ tailWord_414830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414844 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_414844 : Nat := 118140960795 + 414844 * 2 ^ 59
def prefixEnd_414844 : Nat := 4983230072969 + 3 ^ 40 * 414844 * 2
def baseEnd_414844 : Nat := 189346105452337915237487

theorem tailTrace_414844 : CollatzResearch.WordTrace tailWord_414844 prefixEnd_414844 189346105452337915237487 := by
  unfold tailWord_414844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565301854549256279837793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10087069139399008373117057 7565301854549256279837793)
  ·
    refine ⟨5673976390911942209878345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7565301854549256279837793 5673976390911942209878345)
    ·
      refine ⟨4255482293183956657408759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5673976390911942209878345 4255482293183956657408759)
      ·
        refine ⟨6383223439775934986113139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255482293183956657408759 6383223439775934986113139)
        ·
          refine ⟨9574835159663902479169709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383223439775934986113139 9574835159663902479169709)
          ·
            refine ⟨3590563184873963429688641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9574835159663902479169709 3590563184873963429688641)
            ·
              refine ⟨2692922388655472572266481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590563184873963429688641 2692922388655472572266481)
              ·
                refine ⟨2019691791491604429199861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692922388655472572266481 2019691791491604429199861)
                ·
                  refine ⟨189346105452337915237487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2019691791491604429199861 189346105452337915237487)
                  ·
                    rfl

theorem cell20_414844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_414844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414844 prefixEnd_414844 := by exact prefixLift 414844
  have htrace : WordTrace (prefixWord ++ tailWord_414844) baseStart_414844 baseEnd_414844 := by
    simpa [prefixWord, tailWord_414844, baseEnd_414844] using wordTrace_append hprefix tailTrace_414844
  have hstable : (prefixWord ++ tailWord_414844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414844).length < 2 ^ (prefixWord ++ tailWord_414844).sum := by decide
  have hdescent : baseEnd_414844 < baseStart_414844 := by decide
  rcases family_descends (prefixWord ++ tailWord_414844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414851 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_414851 : Nat := 118140960795 + 414851 * 2 ^ 59
def prefixEnd_414851 : Nat := 4983230072969 + 3 ^ 40 * 414851 * 2
def baseEnd_414851 : Nat := 189349300443077002004125

theorem tailTrace_414851 : CollatzResearch.WordTrace tailWord_414851 prefixEnd_414851 189349300443077002004125 := by
  unfold tailWord_414851
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130859020073152755180407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10087239346715435170120271 15130859020073152755180407)
  ·
    refine ⟨22696288530109729132770611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15130859020073152755180407 22696288530109729132770611)
    ·
      refine ⟨34044432795164593699155917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22696288530109729132770611 34044432795164593699155917)
      ·
        refine ⟨12766662298186722637183469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34044432795164593699155917 12766662298186722637183469)
        ·
          refine ⟨4787498361820020988943801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12766662298186722637183469 4787498361820020988943801)
          ·
            refine ⟨3590623771365015741707851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787498361820020988943801 3590623771365015741707851)
            ·
              refine ⟨5385935657047523612561777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590623771365015741707851 5385935657047523612561777)
              ·
                refine ⟨4039451742785642709421333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385935657047523612561777 4039451742785642709421333)
                ·
                  refine ⟨189349300443077002004125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039451742785642709421333 189349300443077002004125)
                  ·
                    rfl

theorem cell20_414851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_414851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414851 prefixEnd_414851 := by exact prefixLift 414851
  have htrace : WordTrace (prefixWord ++ tailWord_414851) baseStart_414851 baseEnd_414851 := by
    simpa [prefixWord, tailWord_414851, baseEnd_414851] using wordTrace_append hprefix tailTrace_414851
  have hstable : (prefixWord ++ tailWord_414851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414851).length < 2 ^ (prefixWord ++ tailWord_414851).sum := by decide
  have hdescent : baseEnd_414851 < baseStart_414851 := by decide
  rcases family_descends (prefixWord ++ tailWord_414851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414896 : List Nat := [2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_414896 : Nat := 118140960795 + 414896 * 2 ^ 59
def prefixEnd_414896 : Nat := 4983230072969 + 3 ^ 40 * 414896 * 2
def baseEnd_414896 : Nat := 63123279889752281834647

theorem tailTrace_414896 : CollatzResearch.WordTrace tailWord_414896 prefixEnd_414896 63123279889752281834647 := by
  unfold tailWord_414896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566250152455062720284271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10088333536606750293712361 7566250152455062720284271)
  ·
    refine ⟨11349375228682594080426407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566250152455062720284271 11349375228682594080426407)
    ·
      refine ⟨17024062843023891120639611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349375228682594080426407 17024062843023891120639611)
      ·
        refine ⟨25536094264535836680959417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17024062843023891120639611 25536094264535836680959417)
        ·
          refine ⟨19152070698401877510719563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25536094264535836680959417 19152070698401877510719563)
          ·
            refine ⟨28728106047602816266079345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152070698401877510719563 28728106047602816266079345)
            ·
              refine ⟨21546079535702112199559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28728106047602816266079345 21546079535702112199559509)
              ·
                refine ⟨63123279889752281834647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21546079535702112199559509 63123279889752281834647)
                ·
                  rfl

theorem cell20_414896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_414896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414896 prefixEnd_414896 := by exact prefixLift 414896
  have htrace : WordTrace (prefixWord ++ tailWord_414896) baseStart_414896 baseEnd_414896 := by
    simpa [prefixWord, tailWord_414896, baseEnd_414896] using wordTrace_append hprefix tailTrace_414896
  have hstable : (prefixWord ++ tailWord_414896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414896).length < 2 ^ (prefixWord ++ tailWord_414896).sum := by decide
  have hdescent : baseEnd_414896 < baseStart_414896 := by decide
  rcases family_descends (prefixWord ++ tailWord_414896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414920 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_414920 : Nat := 118140960795 + 414920 * 2 ^ 59
def prefixEnd_414920 : Nat := 4983230072969 + 3 ^ 40 * 414920 * 2
def baseEnd_414920 : Nat := 189380793923219428703843

theorem tailTrace_414920 : CollatzResearch.WordTrace tailWord_414920 prefixEnd_414920 189380793923219428703843 := by
  unfold tailWord_414920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566687828411588769721107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10088917104548785026294809 7566687828411588769721107)
  ·
    refine ⟨11350031742617383154581661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566687828411588769721107 11350031742617383154581661)
    ·
      refine ⟨4256261903481518682968123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11350031742617383154581661 4256261903481518682968123)
      ·
        refine ⟨6384392855222278024452185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256261903481518682968123 6384392855222278024452185)
        ·
          refine ⟨4788294641416708518339139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6384392855222278024452185 4788294641416708518339139)
          ·
            refine ⟨7182441962125062777508709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788294641416708518339139 7182441962125062777508709)
            ·
              refine ⟨1346707867898449270782883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7182441962125062777508709 1346707867898449270782883)
              ·
                refine ⟨2020061801847673906174325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346707867898449270782883 2020061801847673906174325)
                ·
                  refine ⟨189380793923219428703843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020061801847673906174325 189380793923219428703843)
                  ·
                    rfl

theorem cell20_414920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_414920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414920 prefixEnd_414920 := by exact prefixLift 414920
  have htrace : WordTrace (prefixWord ++ tailWord_414920) baseStart_414920 baseEnd_414920 := by
    simpa [prefixWord, tailWord_414920, baseEnd_414920] using wordTrace_append hprefix tailTrace_414920
  have hstable : (prefixWord ++ tailWord_414920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414920).length < 2 ^ (prefixWord ++ tailWord_414920).sum := by decide
  have hdescent : baseEnd_414920 < baseStart_414920 := by decide
  rcases family_descends (prefixWord ++ tailWord_414920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414927 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_414927 : Nat := 118140960795 + 414927 * 2 ^ 59
def prefixEnd_414927 : Nat := 4983230072969 + 3 ^ 40 * 414927 * 2
def baseEnd_414927 : Nat := 189383988913958515470481

theorem tailTrace_414927 : CollatzResearch.WordTrace tailWord_414927 prefixEnd_414927 189383988913958515470481 := by
  unfold tailWord_414927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133630967797817734947035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10089087311865211823298023 15133630967797817734947035)
  ·
    refine ⟨22700446451696726602420553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133630967797817734947035 22700446451696726602420553)
    ·
      refine ⟨17025334838772544951815415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22700446451696726602420553 17025334838772544951815415)
      ·
        refine ⟨25538002258158817427723123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025334838772544951815415 25538002258158817427723123)
        ·
          refine ⟨38307003387238226141584685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538002258158817427723123 38307003387238226141584685)
          ·
            refine ⟨14365126270214334803094257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38307003387238226141584685 14365126270214334803094257)
            ·
              refine ⟨10773844702660751102320693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14365126270214334803094257 10773844702660751102320693)
              ·
                refine ⟨1010047940874445415842565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10773844702660751102320693 1010047940874445415842565)
                ·
                  refine ⟨189383988913958515470481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010047940874445415842565 189383988913958515470481)
                  ·
                    rfl

theorem cell20_414927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_414927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414927 prefixEnd_414927 := by exact prefixLift 414927
  have htrace : WordTrace (prefixWord ++ tailWord_414927) baseStart_414927 baseEnd_414927 := by
    simpa [prefixWord, tailWord_414927, baseEnd_414927] using wordTrace_append hprefix tailTrace_414927
  have hstable : (prefixWord ++ tailWord_414927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414927).length < 2 ^ (prefixWord ++ tailWord_414927).sum := by decide
  have hdescent : baseEnd_414927 < baseStart_414927 := by decide
  rcases family_descends (prefixWord ++ tailWord_414927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414933 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_414933 : Nat := 118140960795 + 414933 * 2 ^ 59
def prefixEnd_414933 : Nat := 4983230072969 + 3 ^ 40 * 414933 * 2
def baseEnd_414933 : Nat := 189386727477449161270457

theorem tailTrace_414933 : CollatzResearch.WordTrace tailWord_414933 prefixEnd_414933 189386727477449161270457 := by
  unfold tailWord_414933
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133849805776080759665453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10089233203850720506443635 15133849805776080759665453)
  ·
    refine ⟨5675193677166030284874545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15133849805776080759665453 5675193677166030284874545)
    ·
      refine ⟨4256395257874522713655909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5675193677166030284874545 4256395257874522713655909)
      ·
        refine ⟨798074110851473008810483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4256395257874522713655909 798074110851473008810483)
        ·
          refine ⟨1197111166277209513215725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798074110851473008810483 1197111166277209513215725)
          ·
            refine ⟨448916687353953567455897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1197111166277209513215725 448916687353953567455897)
            ·
              refine ⟨336687515515465175591923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448916687353953567455897 336687515515465175591923)
              ·
                refine ⟨505031273273197763387885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336687515515465175591923 505031273273197763387885)
                ·
                  refine ⟨189386727477449161270457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505031273273197763387885 189386727477449161270457)
                  ·
                    rfl

theorem cell20_414933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_414933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414933 prefixEnd_414933 := by exact prefixLift 414933
  have htrace : WordTrace (prefixWord ++ tailWord_414933) baseStart_414933 baseEnd_414933 := by
    simpa [prefixWord, tailWord_414933, baseEnd_414933] using wordTrace_append hprefix tailTrace_414933
  have hstable : (prefixWord ++ tailWord_414933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414933).length < 2 ^ (prefixWord ++ tailWord_414933).sum := by decide
  have hdescent : baseEnd_414933 < baseStart_414933 := by decide
  rcases family_descends (prefixWord ++ tailWord_414933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414958 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_414958 : Nat := 118140960795 + 414958 * 2 ^ 59
def prefixEnd_414958 : Nat := 4983230072969 + 3 ^ 40 * 414958 * 2
def baseEnd_414958 : Nat := 189398138158660185437021

theorem tailTrace_414958 : CollatzResearch.WordTrace tailWord_414958 prefixEnd_414958 189398138158660185437021 := by
  unfold tailWord_414958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891845203835688753665691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10089841087123673352883685 1891845203835688753665691)
  ·
    refine ⟨2837767805753533130498537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891845203835688753665691 2837767805753533130498537)
    ·
      refine ⟨2128325854315149847873903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2837767805753533130498537 2128325854315149847873903)
      ·
        refine ⟨3192488781472724771810855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128325854315149847873903 3192488781472724771810855)
        ·
          refine ⟨4788733172209087157716283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192488781472724771810855 4788733172209087157716283)
          ·
            refine ⟨7183099758313630736574425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788733172209087157716283 7183099758313630736574425)
            ·
              refine ⟨5387324818735223052430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183099758313630736574425 5387324818735223052430819)
              ·
                refine ⟨8080987228102834578646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387324818735223052430819 8080987228102834578646229)
                ·
                  refine ⟨189398138158660185437021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8080987228102834578646229 189398138158660185437021)
                  ·
                    rfl

theorem cell20_414958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_414958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414958 prefixEnd_414958 := by exact prefixLift 414958
  have htrace : WordTrace (prefixWord ++ tailWord_414958) baseStart_414958 baseEnd_414958 := by
    simpa [prefixWord, tailWord_414958, baseEnd_414958] using wordTrace_append hprefix tailTrace_414958
  have hstable : (prefixWord ++ tailWord_414958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414958).length < 2 ^ (prefixWord ++ tailWord_414958).sum := by decide
  have hdescent : baseEnd_414958 < baseStart_414958 := by decide
  rcases family_descends (prefixWord ++ tailWord_414958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414964 : List Nat := [2, 6, 1, 2, 2, 7]
def baseStart_414964 : Nat := 118140960795 + 414964 * 2 ^ 59
def prefixEnd_414964 : Nat := 4983230072969 + 3 ^ 40 * 414964 * 2
def baseEnd_414964 : Nat := 7014847286005586342111

theorem tailTrace_414964 : CollatzResearch.WordTrace tailWord_414964 prefixEnd_414964 7014847286005586342111 := by
  unfold tailWord_414964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567490234331886527021973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10089986979109182036029297 7567490234331886527021973)
  ·
    refine ⟨354726104734307180954155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7567490234331886527021973 354726104734307180954155)
    ·
      refine ⟨532089157101460771431233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354726104734307180954155 532089157101460771431233)
      ·
        refine ⟨399066867826095578573425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532089157101460771431233 399066867826095578573425)
        ·
          refine ⟨299300150869571683930069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399066867826095578573425 299300150869571683930069)
          ·
            refine ⟨7014847286005586342111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299300150869571683930069 7014847286005586342111)
            ·
              rfl

theorem cell20_414964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 7].length) (baseStart_414964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414964 prefixEnd_414964 := by exact prefixLift 414964
  have htrace : WordTrace (prefixWord ++ tailWord_414964) baseStart_414964 baseEnd_414964 := by
    simpa [prefixWord, tailWord_414964, baseEnd_414964] using wordTrace_append hprefix tailTrace_414964
  have hstable : (prefixWord ++ tailWord_414964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414964).length < 2 ^ (prefixWord ++ tailWord_414964).sum := by decide
  have hdescent : baseEnd_414964 < baseStart_414964 := by decide
  rcases family_descends (prefixWord ++ tailWord_414964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414972 : List Nat := [2, 2, 2, 1, 13]
def baseStart_414972 : Nat := 118140960795 + 414972 * 2 ^ 59
def prefixEnd_414972 : Nat := 4983230072969 + 3 ^ 40 * 414972 * 2
def baseEnd_414972 : Nat := 2338327507902942703337

theorem tailTrace_414972 : CollatzResearch.WordTrace tailWord_414972 prefixEnd_414972 2338327507902942703337 := by
  unfold tailWord_414972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7567636126317395210167585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10090181501756526946890113 7567636126317395210167585)
  ·
    refine ⟨5675727094738046407625689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7567636126317395210167585 5675727094738046407625689)
    ·
      refine ⟨4256795321053534805719267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5675727094738046407625689 4256795321053534805719267)
      ·
        refine ⟨6385192981580302208578901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256795321053534805719267 6385192981580302208578901)
        ·
          refine ⟨2338327507902942703337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6385192981580302208578901 2338327507902942703337)
          ·
            rfl

theorem cell20_414972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 13].length) (baseStart_414972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414972 prefixEnd_414972 := by exact prefixLift 414972
  have htrace : WordTrace (prefixWord ++ tailWord_414972) baseStart_414972 baseEnd_414972 := by
    simpa [prefixWord, tailWord_414972, baseEnd_414972] using wordTrace_append hprefix tailTrace_414972
  have hstable : (prefixWord ++ tailWord_414972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414972).length < 2 ^ (prefixWord ++ tailWord_414972).sum := by decide
  have hdescent : baseEnd_414972 < baseStart_414972 := by decide
  rcases family_descends (prefixWord ++ tailWord_414972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414975 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_414975 : Nat := 118140960795 + 414975 * 2 ^ 59
def prefixEnd_414975 : Nat := 4983230072969 + 3 ^ 40 * 414975 * 2
def baseEnd_414975 : Nat := 189405897421883681870285

theorem tailTrace_414975 : CollatzResearch.WordTrace tailWord_414975 prefixEnd_414975 189405897421883681870285 := by
  unfold tailWord_414975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15135381671623921932694379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10090254447749281288462919 15135381671623921932694379)
  ·
    refine ⟨22703072507435882899041569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15135381671623921932694379 22703072507435882899041569)
    ·
      refine ⟨17027304380576912174281177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22703072507435882899041569 17027304380576912174281177)
      ·
        refine ⟨12770478285432684130710883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17027304380576912174281177 12770478285432684130710883)
        ·
          refine ⟨19155717428149026196066325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770478285432684130710883 19155717428149026196066325)
          ·
            refine ⟨897924254444485602940609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19155717428149026196066325 897924254444485602940609)
            ·
              refine ⟨673443190833364202205457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897924254444485602940609 673443190833364202205457)
              ·
                refine ⟨505082393125023151654093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673443190833364202205457 505082393125023151654093)
                ·
                  refine ⟨189405897421883681870285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505082393125023151654093 189405897421883681870285)
                  ·
                    rfl

theorem cell20_414975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_414975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_414975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_414975 prefixEnd_414975 := by exact prefixLift 414975
  have htrace : WordTrace (prefixWord ++ tailWord_414975) baseStart_414975 baseEnd_414975 := by
    simpa [prefixWord, tailWord_414975, baseEnd_414975] using wordTrace_append hprefix tailTrace_414975
  have hstable : (prefixWord ++ tailWord_414975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414975).length < 2 ^ (prefixWord ++ tailWord_414975).sum := by decide
  have hdescent : baseEnd_414975 < baseStart_414975 := by decide
  rcases family_descends (prefixWord ++ tailWord_414975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415016 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_415016 : Nat := 118140960795 + 415016 * 2 ^ 59
def prefixEnd_415016 : Nat := 4983230072969 + 3 ^ 40 * 415016 * 2
def baseEnd_415016 : Nat := 189424610939069761503451

theorem tailTrace_415016 : CollatzResearch.WordTrace tailWord_415016 prefixEnd_415016 189424610939069761503451 := by
  unfold tailWord_415016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568438532237692967468451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10091251376316923956624601 7568438532237692967468451)
  ·
    refine ⟨11352657798356539451202677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7568438532237692967468451 11352657798356539451202677)
    ·
      refine ⟨1064311668595925573550251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11352657798356539451202677 1064311668595925573550251)
      ·
        refine ⟨1596467502893888360325377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064311668595925573550251 1596467502893888360325377)
        ·
          refine ⟨1197350627170416270244033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596467502893888360325377 1197350627170416270244033)
          ·
            refine ⟨898012970377812202683025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197350627170416270244033 898012970377812202683025)
            ·
              refine ⟨673509727783359152012269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898012970377812202683025 673509727783359152012269)
              ·
                refine ⟨252566147918759682004601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673509727783359152012269 252566147918759682004601)
                ·
                  refine ⟨189424610939069761503451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252566147918759682004601 189424610939069761503451)
                  ·
                    rfl

theorem cell20_415016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_415016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415016 prefixEnd_415016 := by exact prefixLift 415016
  have htrace : WordTrace (prefixWord ++ tailWord_415016) baseStart_415016 baseEnd_415016 := by
    simpa [prefixWord, tailWord_415016, baseEnd_415016] using wordTrace_append hprefix tailTrace_415016
  have hstable : (prefixWord ++ tailWord_415016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415016).length < 2 ^ (prefixWord ++ tailWord_415016).sum := by decide
  have hdescent : baseEnd_415016 < baseStart_415016 := by decide
  rcases family_descends (prefixWord ++ tailWord_415016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415034 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_415034 : Nat := 118140960795 + 415034 * 2 ^ 59
def prefixEnd_415034 : Nat := 4983230072969 + 3 ^ 40 * 415034 * 2
def baseEnd_415034 : Nat := 189432826629541698903377

theorem tailTrace_415034 : CollatzResearch.WordTrace tailWord_415034 prefixEnd_415034 189432826629541698903377 := by
  unfold tailWord_415034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784383394602543752273039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10091689052273450006061437 3784383394602543752273039)
  ·
    refine ⟨5676575091903815628409559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784383394602543752273039 5676575091903815628409559)
    ·
      refine ⟨8514862637855723442614339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676575091903815628409559 8514862637855723442614339)
      ·
        refine ⟨12772293956783585163921509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514862637855723442614339 12772293956783585163921509)
        ·
          refine ⟨2394805116896922218235283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12772293956783585163921509 2394805116896922218235283)
          ·
            refine ⟨3592207675345383327352925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394805116896922218235283 3592207675345383327352925)
            ·
              refine ⟨1347077878254518747757347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3592207675345383327352925 1347077878254518747757347)
              ·
                refine ⟨2020616817381778121636021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347077878254518747757347 2020616817381778121636021)
                ·
                  refine ⟨189432826629541698903377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020616817381778121636021 189432826629541698903377)
                  ·
                    rfl

theorem cell20_415034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_415034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415034 prefixEnd_415034 := by exact prefixLift 415034
  have htrace : WordTrace (prefixWord ++ tailWord_415034) baseStart_415034 baseEnd_415034 := by
    simpa [prefixWord, tailWord_415034, baseEnd_415034] using wordTrace_append hprefix tailTrace_415034
  have hstable : (prefixWord ++ tailWord_415034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415034).length < 2 ^ (prefixWord ++ tailWord_415034).sum := by decide
  have hdescent : baseEnd_415034 < baseStart_415034 := by decide
  rcases family_descends (prefixWord ++ tailWord_415034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415048 : List Nat := [2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_415048 : Nat := 118140960795 + 415048 * 2 ^ 59
def prefixEnd_415048 : Nat := 4983230072969 + 3 ^ 40 * 415048 * 2
def baseEnd_415048 : Nat := 63146405537006624145551

theorem tailTrace_415048 : CollatzResearch.WordTrace tailWord_415048 prefixEnd_415048 63146405537006624145551 := by
  unfold tailWord_415048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569022100179727700050899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10092029466906303600067865 7569022100179727700050899)
  ·
    refine ⟨11353533150269591550076349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569022100179727700050899 11353533150269591550076349)
    ·
      refine ⟨4257574931351096831278631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11353533150269591550076349 4257574931351096831278631)
      ·
        refine ⟨6386362397026645246917947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257574931351096831278631 6386362397026645246917947)
        ·
          refine ⟨9579543595539967870376921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386362397026645246917947 9579543595539967870376921)
          ·
            refine ⟨7184657696654975902782691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9579543595539967870376921 7184657696654975902782691)
            ·
              refine ⟨10776986544982463854174037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184657696654975902782691 10776986544982463854174037)
              ·
                refine ⟨63146405537006624145551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10776986544982463854174037 63146405537006624145551)
                ·
                  rfl

theorem cell20_415048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_415048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415048 prefixEnd_415048 := by exact prefixLift 415048
  have htrace : WordTrace (prefixWord ++ tailWord_415048) baseStart_415048 baseEnd_415048 := by
    simpa [prefixWord, tailWord_415048, baseEnd_415048] using wordTrace_append hprefix tailTrace_415048
  have hstable : (prefixWord ++ tailWord_415048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415048).length < 2 ^ (prefixWord ++ tailWord_415048).sum := by decide
  have hdescent : baseEnd_415048 < baseStart_415048 := by decide
  rcases family_descends (prefixWord ++ tailWord_415048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415065 : List Nat := [1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_415065 : Nat := 118140960795 + 415065 * 2 ^ 59
def prefixEnd_415065 : Nat := 4983230072969 + 3 ^ 40 * 415065 * 2
def baseEnd_415065 : Nat := 63148991958081122956639

theorem tailTrace_415065 : CollatzResearch.WordTrace tailWord_415065 prefixEnd_415065 63148991958081122956639 := by
  unfold tailWord_415065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138664241297867303470649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10092442827531911535647099 15138664241297867303470649)
  ·
    refine ⟨11353998180973400477602987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15138664241297867303470649 11353998180973400477602987)
    ·
      refine ⟨17030997271460100716404481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11353998180973400477602987 17030997271460100716404481)
      ·
        refine ⟨12773247953595075537303361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17030997271460100716404481 12773247953595075537303361)
        ·
          refine ⟨9579935965196306652977521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12773247953595075537303361 9579935965196306652977521)
          ·
            refine ⟨7184951973897229989733141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9579935965196306652977521 7184951973897229989733141)
            ·
              refine ⟨336794623776432655768741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7184951973897229989733141 336794623776432655768741)
              ·
                refine ⟨63148991958081122956639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336794623776432655768741 63148991958081122956639)
                ·
                  rfl

theorem cell20_415065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_415065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415065 prefixEnd_415065 := by exact prefixLift 415065
  have htrace : WordTrace (prefixWord ++ tailWord_415065) baseStart_415065 baseEnd_415065 := by
    simpa [prefixWord, tailWord_415065, baseEnd_415065] using wordTrace_append hprefix tailTrace_415065
  have hstable : (prefixWord ++ tailWord_415065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415065).length < 2 ^ (prefixWord ++ tailWord_415065).sum := by decide
  have hdescent : baseEnd_415065 < baseStart_415065 := by decide
  rcases family_descends (prefixWord ++ tailWord_415065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415072 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_415072 : Nat := 118140960795 + 415072 * 2 ^ 59
def prefixEnd_415072 : Nat := 4983230072969 + 3 ^ 40 * 415072 * 2
def baseEnd_415072 : Nat := 189450170864982455636555

theorem tailTrace_415072 : CollatzResearch.WordTrace tailWord_415072 prefixEnd_415072 189450170864982455636555 := by
  unfold tailWord_415072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569459776136253749487735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10092613034848338332650313 7569459776136253749487735)
  ·
    refine ⟨11354189664204380624231603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569459776136253749487735 11354189664204380624231603)
    ·
      refine ⟨17031284496306570936347405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354189664204380624231603 17031284496306570936347405)
      ·
        refine ⟨6386731686114964101130277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17031284496306570936347405 6386731686114964101130277)
        ·
          refine ⟨1197512191146555768961927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6386731686114964101130277 1197512191146555768961927)
          ·
            refine ⟨1796268286719833653442891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197512191146555768961927 1796268286719833653442891)
            ·
              refine ⟨2694402430079750480164337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796268286719833653442891 2694402430079750480164337)
              ·
                refine ⟨2020801822559812860123253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694402430079750480164337 2020801822559812860123253)
                ·
                  refine ⟨189450170864982455636555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020801822559812860123253 189450170864982455636555)
                  ·
                    rfl

theorem cell20_415072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_415072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415072 prefixEnd_415072 := by exact prefixLift 415072
  have htrace : WordTrace (prefixWord ++ tailWord_415072) baseStart_415072 baseEnd_415072 := by
    simpa [prefixWord, tailWord_415072, baseEnd_415072] using wordTrace_append hprefix tailTrace_415072
  have hstable : (prefixWord ++ tailWord_415072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415072).length < 2 ^ (prefixWord ++ tailWord_415072).sum := by decide
  have hdescent : baseEnd_415072 < baseStart_415072 := by decide
  rcases family_descends (prefixWord ++ tailWord_415072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415075 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 2]
def baseStart_415075 : Nat := 118140960795 + 415075 * 2 ^ 59
def prefixEnd_415075 : Nat := 4983230072969 + 3 ^ 40 * 415075 * 2
def baseEnd_415075 : Nat := 189451540146727778536543

theorem tailTrace_415075 : CollatzResearch.WordTrace tailWord_415075 prefixEnd_415075 189451540146727778536543 := by
  unfold tailWord_415075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15139028971261639011334679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10092685980841092674223119 15139028971261639011334679)
  ·
    refine ⟨22708543456892458517002019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15139028971261639011334679 22708543456892458517002019)
    ·
      refine ⟨34062815185338687775503029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22708543456892458517002019 34062815185338687775503029)
      ·
        refine ⟨3193388923625501978953409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34062815185338687775503029 3193388923625501978953409)
        ·
          refine ⟨2395041692719126484215057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193388923625501978953409 2395041692719126484215057)
          ·
            refine ⟨1796281269539344863161293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395041692719126484215057 1796281269539344863161293)
            ·
              refine ⟨673605476077254323685485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1796281269539344863161293 673605476077254323685485)
              ·
                refine ⟨252602053528970371382057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673605476077254323685485 252602053528970371382057)
                ·
                  refine ⟨189451540146727778536543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252602053528970371382057 189451540146727778536543)
                  ·
                    rfl

theorem cell20_415075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 2].length) (baseStart_415075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415075 prefixEnd_415075 := by exact prefixLift 415075
  have htrace : WordTrace (prefixWord ++ tailWord_415075) baseStart_415075 baseEnd_415075 := by
    simpa [prefixWord, tailWord_415075, baseEnd_415075] using wordTrace_append hprefix tailTrace_415075
  have hstable : (prefixWord ++ tailWord_415075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415075).length < 2 ^ (prefixWord ++ tailWord_415075).sum := by decide
  have hdescent : baseEnd_415075 < baseStart_415075 := by decide
  rcases family_descends (prefixWord ++ tailWord_415075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415082 : List Nat := [3, 1, 3, 3, 2, 2, 6]
def baseStart_415082 : Nat := 118140960795 + 415082 * 2 ^ 59
def prefixEnd_415082 : Nat := 4983230072969 + 3 ^ 40 * 415082 * 2
def baseEnd_415082 : Nat := 21050526126385207255909

theorem tailTrace_415082 : CollatzResearch.WordTrace tailWord_415082 prefixEnd_415082 21050526126385207255909 := by
  unfold tailWord_415082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784821070559069801709875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10092856188157519471226333 3784821070559069801709875)
  ·
    refine ⟨5677231605838604702564813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784821070559069801709875 5677231605838604702564813)
    ·
      refine ⟨2128961852189476763461805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5677231605838604702564813 2128961852189476763461805)
      ·
        refine ⟨798360694571053786298177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2128961852189476763461805 798360694571053786298177)
        ·
          refine ⟨598770520928290339723633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798360694571053786298177 598770520928290339723633)
          ·
            refine ⟨449077890696217754792725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598770520928290339723633 449077890696217754792725)
            ·
              refine ⟨21050526126385207255909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449077890696217754792725 21050526126385207255909)
              ·
                rfl

theorem cell20_415082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_415082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415082 prefixEnd_415082 := by exact prefixLift 415082
  have htrace : WordTrace (prefixWord ++ tailWord_415082) baseStart_415082 baseEnd_415082 := by
    simpa [prefixWord, tailWord_415082, baseEnd_415082] using wordTrace_append hprefix tailTrace_415082
  have hstable : (prefixWord ++ tailWord_415082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415082).length < 2 ^ (prefixWord ++ tailWord_415082).sum := by decide
  have hdescent : baseEnd_415082 < baseStart_415082 := by decide
  rcases family_descends (prefixWord ++ tailWord_415082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415148 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_415148 : Nat := 118140960795 + 415148 * 2 ^ 59
def prefixEnd_415148 : Nat := 4983230072969 + 3 ^ 40 * 415148 * 2
def baseEnd_415148 : Nat := 189484859335863969102911

theorem tailTrace_415148 : CollatzResearch.WordTrace tailWord_415148 prefixEnd_415148 189484859335863969102911 := by
  unfold tailWord_415148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570845749998586239371049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10094460999998114985828065 7570845749998586239371049)
  ·
    refine ⟨5678134312498939679528287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7570845749998586239371049 5678134312498939679528287)
    ·
      refine ⟨8517201468748409519292431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678134312498939679528287 8517201468748409519292431)
      ·
        refine ⟨12775802203122614278938647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8517201468748409519292431 12775802203122614278938647)
        ·
          refine ⟨19163703304683921418407971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775802203122614278938647 19163703304683921418407971)
          ·
            refine ⟨28745554957025882127611957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19163703304683921418407971 28745554957025882127611957)
            ·
              refine ⟨2694895777221176449463621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28745554957025882127611957 2694895777221176449463621)
              ·
                refine ⟨505292958228970584274429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2694895777221176449463621 505292958228970584274429)
                ·
                  refine ⟨189484859335863969102911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505292958228970584274429 189484859335863969102911)
                  ·
                    rfl

theorem cell20_415148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_415148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415148 prefixEnd_415148 := by exact prefixLift 415148
  have htrace : WordTrace (prefixWord ++ tailWord_415148) baseStart_415148 baseEnd_415148 := by
    simpa [prefixWord, tailWord_415148, baseEnd_415148] using wordTrace_append hprefix tailTrace_415148
  have hstable : (prefixWord ++ tailWord_415148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415148).length < 2 ^ (prefixWord ++ tailWord_415148).sum := by decide
  have hdescent : baseEnd_415148 < baseStart_415148 := by decide
  rcases family_descends (prefixWord ++ tailWord_415148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415172 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_415172 : Nat := 118140960795 + 415172 * 2 ^ 59
def prefixEnd_415172 : Nat := 4983230072969 + 3 ^ 40 * 415172 * 2
def baseEnd_415172 : Nat := 189495813589826552302813

theorem tailTrace_415172 : CollatzResearch.WordTrace tailWord_415172 prefixEnd_415172 189495813589826552302813 := by
  unfold tailWord_415172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571283425955112288807885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10095044567940149718410513 7571283425955112288807885)
  ·
    refine ⟨2839231284733167108302957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7571283425955112288807885 2839231284733167108302957)
    ·
      refine ⟨1064711731774937665613609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2839231284733167108302957 1064711731774937665613609)
      ·
        refine ⟨798533798831203249210207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064711731774937665613609 798533798831203249210207)
        ·
          refine ⟨1197800698246804873815311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798533798831203249210207 1197800698246804873815311)
          ·
            refine ⟨1796701047370207310722967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197800698246804873815311 1796701047370207310722967)
            ·
              refine ⟨2695051571055310966084451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796701047370207310722967 2695051571055310966084451)
              ·
                refine ⟨4042577356582966449126677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695051571055310966084451 4042577356582966449126677)
                ·
                  refine ⟨189495813589826552302813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4042577356582966449126677 189495813589826552302813)
                  ·
                    rfl

theorem cell20_415172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_415172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415172 prefixEnd_415172 := by exact prefixLift 415172
  have htrace : WordTrace (prefixWord ++ tailWord_415172) baseStart_415172 baseEnd_415172 := by
    simpa [prefixWord, tailWord_415172, baseEnd_415172] using wordTrace_append hprefix tailTrace_415172
  have hstable : (prefixWord ++ tailWord_415172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415172).length < 2 ^ (prefixWord ++ tailWord_415172).sum := by decide
  have hdescent : baseEnd_415172 < baseStart_415172 := by decide
  rcases family_descends (prefixWord ++ tailWord_415172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415189 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 2]
def baseStart_415189 : Nat := 118140960795 + 415189 * 2 ^ 59
def prefixEnd_415189 : Nat := 4983230072969 + 3 ^ 40 * 415189 * 2
def baseEnd_415189 : Nat := 189503572853050048736077

theorem tailTrace_415189 : CollatzResearch.WordTrace tailWord_415189 prefixEnd_415189 189503572853050048736077 := by
  unfold tailWord_415189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143186892848636480984621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10095457928565757653989747 15143186892848636480984621)
  ·
    refine ⟨5678695084818238680369233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15143186892848636480984621 5678695084818238680369233)
    ·
      refine ⟨4259021313613679010276925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5678695084818238680369233 4259021313613679010276925)
      ·
        refine ⟨1597132992605129628853847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4259021313613679010276925 1597132992605129628853847)
        ·
          refine ⟨2395699488907694443280771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597132992605129628853847 2395699488907694443280771)
          ·
            refine ⟨3593549233361541664921157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395699488907694443280771 3593549233361541664921157)
            ·
              refine ⟨673790481255289062172717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3593549233361541664921157 673790481255289062172717)
              ·
                refine ⟨252671430470733398314769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673790481255289062172717 252671430470733398314769)
                ·
                  refine ⟨189503572853050048736077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252671430470733398314769 189503572853050048736077)
                  ·
                    rfl

theorem cell20_415189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_415189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415189 prefixEnd_415189 := by exact prefixLift 415189
  have htrace : WordTrace (prefixWord ++ tailWord_415189) baseStart_415189 baseEnd_415189 := by
    simpa [prefixWord, tailWord_415189, baseEnd_415189] using wordTrace_append hprefix tailTrace_415189
  have hstable : (prefixWord ++ tailWord_415189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415189).length < 2 ^ (prefixWord ++ tailWord_415189).sum := by decide
  have hdescent : baseEnd_415189 < baseStart_415189 := by decide
  rcases family_descends (prefixWord ++ tailWord_415189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415203 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_415203 : Nat := 118140960795 + 415203 * 2 ^ 59
def prefixEnd_415203 : Nat := 4983230072969 + 3 ^ 40 * 415203 * 2
def baseEnd_415203 : Nat := 189509962834528222269353

theorem tailTrace_415203 : CollatzResearch.WordTrace tailWord_415203 prefixEnd_415203 189509962834528222269353 := by
  unfold tailWord_415203
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143697514797916871994263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10095798343198611247996175 15143697514797916871994263)
  ·
    refine ⟨22715546272196875307991395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15143697514797916871994263 22715546272196875307991395)
    ·
      refine ⟨34073319408295312961987093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22715546272196875307991395 34073319408295312961987093)
      ·
        refine ⟨1597186847263842795093145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34073319408295312961987093 1597186847263842795093145)
        ·
          refine ⟨1197890135447882096319859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597186847263842795093145 1197890135447882096319859)
          ·
            refine ⟨1796835203171823144479789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197890135447882096319859 1796835203171823144479789)
            ·
              refine ⟨673813201189433679179921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1796835203171823144479789 673813201189433679179921)
              ·
                refine ⟨505359900892075259384941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673813201189433679179921 505359900892075259384941)
                ·
                  refine ⟨189509962834528222269353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505359900892075259384941 189509962834528222269353)
                  ·
                    rfl

theorem cell20_415203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_415203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415203 prefixEnd_415203 := by exact prefixLift 415203
  have htrace : WordTrace (prefixWord ++ tailWord_415203) baseStart_415203 baseEnd_415203 := by
    simpa [prefixWord, tailWord_415203, baseEnd_415203] using wordTrace_append hprefix tailTrace_415203
  have hstable : (prefixWord ++ tailWord_415203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415203).length < 2 ^ (prefixWord ++ tailWord_415203).sum := by decide
  have hdescent : baseEnd_415203 < baseStart_415203 := by decide
  rcases family_descends (prefixWord ++ tailWord_415203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415230 : List Nat := [4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_415230 : Nat := 118140960795 + 415230 * 2 ^ 59
def prefixEnd_415230 : Nat := 4983230072969 + 3 ^ 40 * 415230 * 2
def baseEnd_415230 : Nat := 63174095456745376123081

theorem tailTrace_415230 : CollatzResearch.WordTrace tailWord_415230 prefixEnd_415230 63174095456745376123081 := by
  unfold tailWord_415230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893085285712512560403393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10096454857133400322151429 1893085285712512560403393)
  ·
    refine ⟨1419813964284384420302545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1893085285712512560403393 1419813964284384420302545)
    ·
      refine ⟨1064860473213288315226909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1419813964284384420302545 1064860473213288315226909)
      ·
        refine ⟨399322677454983118210091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1064860473213288315226909 399322677454983118210091)
        ·
          refine ⟨598984016182474677315137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399322677454983118210091 598984016182474677315137)
          ·
            refine ⟨449238012136856007986353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598984016182474677315137 449238012136856007986353)
            ·
              refine ⟨336928509102642005989765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449238012136856007986353 336928509102642005989765)
              ·
                refine ⟨63174095456745376123081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336928509102642005989765 63174095456745376123081)
                ·
                  rfl

theorem cell20_415230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_415230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415230 prefixEnd_415230 := by exact prefixLift 415230
  have htrace : WordTrace (prefixWord ++ tailWord_415230) baseStart_415230 baseEnd_415230 := by
    simpa [prefixWord, tailWord_415230, baseEnd_415230] using wordTrace_append hprefix tailTrace_415230
  have hstable : (prefixWord ++ tailWord_415230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415230).length < 2 ^ (prefixWord ++ tailWord_415230).sum := by decide
  have hdescent : baseEnd_415230 < baseStart_415230 := by decide
  rcases family_descends (prefixWord ++ tailWord_415230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415234 : List Nat := [3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_415234 : Nat := 118140960795 + 415234 * 2 ^ 59
def prefixEnd_415234 : Nat := 4983230072969 + 3 ^ 40 * 415234 * 2
def baseEnd_415234 : Nat := 63174704026409964078631

theorem tailTrace_415234 : CollatzResearch.WordTrace tailWord_415234 prefixEnd_415234 63174704026409964078631 := by
  unfold tailWord_415234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786207044421402291593189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10096552118457072777581837 3786207044421402291593189)
  ·
    refine ⟨709913820829012929673723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3786207044421402291593189 709913820829012929673723)
    ·
      refine ⟨1064870731243519394510585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709913820829012929673723 1064870731243519394510585)
      ·
        refine ⟨798653048432639545882939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064870731243519394510585 798653048432639545882939)
        ·
          refine ⟨1197979572648959318824409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798653048432639545882939 1197979572648959318824409)
          ·
            refine ⟨898484679486719489118307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197979572648959318824409 898484679486719489118307)
            ·
              refine ⟨1347727019230079233677461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898484679486719489118307 1347727019230079233677461)
              ·
                refine ⟨63174704026409964078631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1347727019230079233677461 63174704026409964078631)
                ·
                  rfl

theorem cell20_415234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_415234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415234 prefixEnd_415234 := by exact prefixLift 415234
  have htrace : WordTrace (prefixWord ++ tailWord_415234) baseStart_415234 baseEnd_415234 := by
    simpa [prefixWord, tailWord_415234, baseEnd_415234] using wordTrace_append hprefix tailTrace_415234
  have hstable : (prefixWord ++ tailWord_415234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415234).length < 2 ^ (prefixWord ++ tailWord_415234).sum := by decide
  have hdescent : baseEnd_415234 < baseStart_415234 := by decide
  rcases family_descends (prefixWord ++ tailWord_415234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415244 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_415244 : Nat := 118140960795 + 415244 * 2 ^ 59
def prefixEnd_415244 : Nat := 4983230072969 + 3 ^ 40 * 415244 * 2
def baseEnd_415244 : Nat := 189528676351714301902519

theorem tailTrace_415244 : CollatzResearch.WordTrace tailWord_415244 prefixEnd_415244 189528676351714301902519 := by
  unfold tailWord_415244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572596453824690437118393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10096795271766253916157857 7572596453824690437118393)
  ·
    refine ⟨5679447340368517827838795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7572596453824690437118393 5679447340368517827838795)
    ·
      refine ⟨8519171010552776741758193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679447340368517827838795 8519171010552776741758193)
      ·
        refine ⟨6389378257914582556318645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519171010552776741758193 6389378257914582556318645)
        ·
          refine ⟨599004211679492114654873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6389378257914582556318645 599004211679492114654873)
          ·
            refine ⟨449253158759619085991155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599004211679492114654873 449253158759619085991155)
            ·
              refine ⟨673879738139428628986733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449253158759619085991155 673879738139428628986733)
              ·
                refine ⟨252704901802285735870025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673879738139428628986733 252704901802285735870025)
                ·
                  refine ⟨189528676351714301902519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252704901802285735870025 189528676351714301902519)
                  ·
                    rfl

theorem cell20_415244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_415244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415244 prefixEnd_415244 := by exact prefixLift 415244
  have htrace : WordTrace (prefixWord ++ tailWord_415244) baseStart_415244 baseEnd_415244 := by
    simpa [prefixWord, tailWord_415244, baseEnd_415244] using wordTrace_append hprefix tailTrace_415244
  have hstable : (prefixWord ++ tailWord_415244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415244).length < 2 ^ (prefixWord ++ tailWord_415244).sum := by decide
  have hdescent : baseEnd_415244 < baseStart_415244 := by decide
  rcases family_descends (prefixWord ++ tailWord_415244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415272 : List Nat := [2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_415272 : Nat := 118140960795 + 415272 * 2 ^ 59
def prefixEnd_415272 : Nat := 4983230072969 + 3 ^ 40 * 415272 * 2
def baseEnd_415272 : Nat := 63180485438223549656357

theorem tailTrace_415272 : CollatzResearch.WordTrace tailWord_415272 prefixEnd_415272 63180485438223549656357 := by
  unfold tailWord_415272
  simp only [CollatzResearch.WordTrace]
  refine ⟨7573107075773970828128035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10097476101031961104170713 7573107075773970828128035)
  ·
    refine ⟨11359660613660956242192053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7573107075773970828128035 11359660613660956242192053)
    ·
      refine ⟨1064968182530714647705505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11359660613660956242192053 1064968182530714647705505)
      ·
        refine ⟨798726136898035985779129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064968182530714647705505 798726136898035985779129)
        ·
          refine ⟨599044602673526989334347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798726136898035985779129 599044602673526989334347)
          ·
            refine ⟨898566904010290484001521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599044602673526989334347 898566904010290484001521)
            ·
              refine ⟨673925178007717863001141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898566904010290484001521 673925178007717863001141)
              ·
                refine ⟨63180485438223549656357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 673925178007717863001141 63180485438223549656357)
                ·
                  rfl

theorem cell20_415272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_415272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415272 prefixEnd_415272 := by exact prefixLift 415272
  have htrace : WordTrace (prefixWord ++ tailWord_415272) baseStart_415272 baseEnd_415272 := by
    simpa [prefixWord, tailWord_415272, baseEnd_415272] using wordTrace_append hprefix tailTrace_415272
  have hstable : (prefixWord ++ tailWord_415272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415272).length < 2 ^ (prefixWord ++ tailWord_415272).sum := by decide
  have hdescent : baseEnd_415272 < baseStart_415272 := by decide
  rcases family_descends (prefixWord ++ tailWord_415272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415314 : List Nat := [3, 2, 2, 1, 2, 10]
def baseStart_415314 : Nat := 118140960795 + 415314 * 2 ^ 59
def prefixEnd_415314 : Nat := 4983230072969 + 3 ^ 40 * 415314 * 2
def baseEnd_415314 : Nat := 7020763935522413687737

theorem tailTrace_415314 : CollatzResearch.WordTrace tailWord_415314 prefixEnd_415314 7020763935522413687737 := by
  unfold tailWord_415314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786936504348945707321249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10098497344930521886189997 3786936504348945707321249)
  ·
    refine ⟨2840202378261709280490937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3786936504348945707321249 2840202378261709280490937)
    ·
      refine ⟨2130151783696281960368203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2840202378261709280490937 2130151783696281960368203)
      ·
        refine ⟨3195227675544422940552305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130151783696281960368203 3195227675544422940552305)
        ·
          refine ⟨2396420756658317205414229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195227675544422940552305 2396420756658317205414229)
          ·
            refine ⟨7020763935522413687737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2396420756658317205414229 7020763935522413687737)
            ·
              rfl

theorem cell20_415314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 10].length) (baseStart_415314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415314 prefixEnd_415314 := by exact prefixLift 415314
  have htrace : WordTrace (prefixWord ++ tailWord_415314) baseStart_415314 baseEnd_415314 := by
    simpa [prefixWord, tailWord_415314, baseEnd_415314] using wordTrace_append hprefix tailTrace_415314
  have hstable : (prefixWord ++ tailWord_415314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415314).length < 2 ^ (prefixWord ++ tailWord_415314).sum := by decide
  have hdescent : baseEnd_415314 < baseStart_415314 := by decide
  rcases family_descends (prefixWord ++ tailWord_415314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415321 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_415321 : Nat := 118140960795 + 415321 * 2 ^ 59
def prefixEnd_415321 : Nat := 4983230072969 + 3 ^ 40 * 415321 * 2
def baseEnd_415321 : Nat := 189563821249844256335537

theorem tailTrace_415321 : CollatzResearch.WordTrace tailWord_415321 prefixEnd_415321 189563821249844256335537 := by
  unfold tailWord_415321
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148001328370423024789817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10098667552246948683193211 15148001328370423024789817)
  ·
    refine ⟨11361000996277817268592363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15148001328370423024789817 11361000996277817268592363)
    ·
      refine ⟨17041501494416725902888545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361000996277817268592363 17041501494416725902888545)
      ·
        refine ⟨12781126120812544427166409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17041501494416725902888545 12781126120812544427166409)
        ·
          refine ⟨9585844590609408320374807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12781126120812544427166409 9585844590609408320374807)
          ·
            refine ⟨14378766885914112480562211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9585844590609408320374807 14378766885914112480562211)
            ·
              refine ⟨21568150328871168720843317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378766885914112480562211 21568150328871168720843317)
              ·
                refine ⟨2022014093331672067579061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21568150328871168720843317 2022014093331672067579061)
                ·
                  refine ⟨189563821249844256335537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2022014093331672067579061 189563821249844256335537)
                  ·
                    rfl

theorem cell20_415321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_415321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415321 prefixEnd_415321 := by exact prefixLift 415321
  have htrace : WordTrace (prefixWord ++ tailWord_415321) baseStart_415321 baseEnd_415321 := by
    simpa [prefixWord, tailWord_415321, baseEnd_415321] using wordTrace_append hprefix tailTrace_415321
  have hstable : (prefixWord ++ tailWord_415321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415321).length < 2 ^ (prefixWord ++ tailWord_415321).sum := by decide
  have hdescent : baseEnd_415321 < baseStart_415321 := by decide
  rcases family_descends (prefixWord ++ tailWord_415321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415331 : List Nat := [1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_415331 : Nat := 118140960795 + 415331 * 2 ^ 59
def prefixEnd_415331 : Nat := 4983230072969 + 3 ^ 40 * 415331 * 2
def baseEnd_415331 : Nat := 63189461840776222000721

theorem tailTrace_415331 : CollatzResearch.WordTrace tailWord_415331 prefixEnd_415331 63189461840776222000721 := by
  unfold tailWord_415331
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148366058334194732653847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10098910705556129821769231 15148366058334194732653847)
  ·
    refine ⟨22722549087501292098980771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15148366058334194732653847 22722549087501292098980771)
    ·
      refine ⟨34083823631251938148471157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22722549087501292098980771 34083823631251938148471157)
      ·
        refine ⟨3195358465429869201419171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34083823631251938148471157 3195358465429869201419171)
        ·
          refine ⟨4793037698144803802128757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195358465429869201419171 4793037698144803802128757)
          ·
            refine ⟨449347284201075356449571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4793037698144803802128757 449347284201075356449571)
            ·
              refine ⟨674020926301613034674357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449347284201075356449571 674020926301613034674357)
              ·
                refine ⟨63189461840776222000721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674020926301613034674357 63189461840776222000721)
                ·
                  rfl

theorem cell20_415331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_415331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415331 prefixEnd_415331 := by exact prefixLift 415331
  have htrace : WordTrace (prefixWord ++ tailWord_415331) baseStart_415331 baseEnd_415331 := by
    simpa [prefixWord, tailWord_415331, baseEnd_415331] using wordTrace_append hprefix tailTrace_415331
  have hstable : (prefixWord ++ tailWord_415331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415331).length < 2 ^ (prefixWord ++ tailWord_415331).sum := by decide
  have hdescent : baseEnd_415331 < baseStart_415331 := by decide
  rcases family_descends (prefixWord ++ tailWord_415331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415383 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_415383 : Nat := 118140960795 + 415383 * 2 ^ 59
def prefixEnd_415383 : Nat := 4983230072969 + 3 ^ 40 * 415383 * 2
def baseEnd_415383 : Nat := 189592119739247596268617

theorem tailTrace_415383 : CollatzResearch.WordTrace tailWord_415383 prefixEnd_415383 189592119739247596268617 := by
  unfold tailWord_415383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150262654145807613546803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10100175102763871742364535 15150262654145807613546803)
  ·
    refine ⟨22725393981218711420320205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15150262654145807613546803 22725393981218711420320205)
    ·
      refine ⟨8522022742957016782620077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22725393981218711420320205 8522022742957016782620077)
      ·
        refine ⟨3195758528608881293482529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8522022742957016782620077 3195758528608881293482529)
        ·
          refine ⟨2396818896456660970111897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195758528608881293482529 2396818896456660970111897)
          ·
            refine ⟨1797614172342495727583923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396818896456660970111897 1797614172342495727583923)
            ·
              refine ⟨2696421258513743591375885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797614172342495727583923 2696421258513743591375885)
              ·
                refine ⟨1011157971942653846765957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696421258513743591375885 1011157971942653846765957)
                ·
                  refine ⟨189592119739247596268617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011157971942653846765957 189592119739247596268617)
                  ·
                    rfl

theorem cell20_415383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_415383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415383 prefixEnd_415383 := by exact prefixLift 415383
  have htrace : WordTrace (prefixWord ++ tailWord_415383) baseStart_415383 baseEnd_415383 := by
    simpa [prefixWord, tailWord_415383, baseEnd_415383] using wordTrace_append hprefix tailTrace_415383
  have hstable : (prefixWord ++ tailWord_415383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415383).length < 2 ^ (prefixWord ++ tailWord_415383).sum := by decide
  have hdescent : baseEnd_415383 < baseStart_415383 := by decide
  rcases family_descends (prefixWord ++ tailWord_415383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415413 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 2]
def baseStart_415413 : Nat := 118140960795 + 415413 * 2 ^ 59
def prefixEnd_415413 : Nat := 4983230072969 + 3 ^ 40 * 415413 * 2
def baseEnd_415413 : Nat := 189605812556700825268495

theorem tailTrace_415413 : CollatzResearch.WordTrace tailWord_415413 prefixEnd_415413 189605812556700825268495 := by
  unfold tailWord_415413
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151356844037122737138893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10100904562691415158092595 15151356844037122737138893)
  ·
    refine ⟨5681758816513921026427085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15151356844037122737138893 5681758816513921026427085)
    ·
      refine ⟨2130659556192720384910157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5681758816513921026427085 2130659556192720384910157)
      ·
        refine ⟨798997333572270144341309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2130659556192720384910157 798997333572270144341309)
        ·
          refine ⟨299624000089601304127991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 798997333572270144341309 299624000089601304127991)
          ·
            refine ⟨449436000134401956191987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299624000089601304127991 449436000134401956191987)
            ·
              refine ⟨674154000201602934287981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449436000134401956191987 674154000201602934287981)
              ·
                refine ⟨252807750075601100357993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674154000201602934287981 252807750075601100357993)
                ·
                  refine ⟨189605812556700825268495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252807750075601100357993 189605812556700825268495)
                  ·
                    rfl

theorem cell20_415413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_415413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415413 prefixEnd_415413 := by exact prefixLift 415413
  have htrace : WordTrace (prefixWord ++ tailWord_415413) baseStart_415413 baseEnd_415413 := by
    simpa [prefixWord, tailWord_415413, baseEnd_415413] using wordTrace_append hprefix tailTrace_415413
  have hstable : (prefixWord ++ tailWord_415413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415413).length < 2 ^ (prefixWord ++ tailWord_415413).sum := by decide
  have hdescent : baseEnd_415413 < baseStart_415413 := by decide
  rcases family_descends (prefixWord ++ tailWord_415413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415430 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_415430 : Nat := 118140960795 + 415430 * 2 ^ 59
def prefixEnd_415430 : Nat := 4983230072969 + 3 ^ 40 * 415430 * 2
def baseEnd_415430 : Nat := 189613571819924321701759

theorem tailTrace_415430 : CollatzResearch.WordTrace tailWord_415430 prefixEnd_415430 189613571819924321701759 := by
  unfold tailWord_415430
  simp only [CollatzResearch.WordTrace]
  refine ⟨473499277655485457515867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10101317923317023093671829 473499277655485457515867)
  ·
    refine ⟨710248916483228186273801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473499277655485457515867 710248916483228186273801)
    ·
      refine ⟨532686687362421139705351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710248916483228186273801 532686687362421139705351)
      ·
        refine ⟨799030031043631709558027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532686687362421139705351 799030031043631709558027)
        ·
          refine ⟨1198545046565447564337041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799030031043631709558027 1198545046565447564337041)
          ·
            refine ⟨898908784924085673252781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198545046565447564337041 898908784924085673252781)
            ·
              refine ⟨337090794346532127469793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898908784924085673252781 337090794346532127469793)
              ·
                refine ⟨252818095759899095602345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337090794346532127469793 252818095759899095602345)
                ·
                  refine ⟨189613571819924321701759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252818095759899095602345 189613571819924321701759)
                  ·
                    rfl

theorem cell20_415430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_415430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415430 prefixEnd_415430 := by exact prefixLift 415430
  have htrace : WordTrace (prefixWord ++ tailWord_415430) baseStart_415430 baseEnd_415430 := by
    simpa [prefixWord, tailWord_415430, baseEnd_415430] using wordTrace_append hprefix tailTrace_415430
  have hstable : (prefixWord ++ tailWord_415430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415430).length < 2 ^ (prefixWord ++ tailWord_415430).sum := by decide
  have hdescent : baseEnd_415430 < baseStart_415430 := by decide
  rcases family_descends (prefixWord ++ tailWord_415430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415434 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_415434 : Nat := 118140960795 + 415434 * 2 ^ 59
def prefixEnd_415434 : Nat := 4983230072969 + 3 ^ 40 * 415434 * 2
def baseEnd_415434 : Nat := 189615397528918085568409

theorem tailTrace_415434 : CollatzResearch.WordTrace tailWord_415434 prefixEnd_415434 189615397528918085568409 := by
  unfold tailWord_415434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788030694240260830913339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10101415184640695549102237 3788030694240260830913339)
  ·
    refine ⟨5682046041360391246370009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788030694240260830913339 5682046041360391246370009)
    ·
      refine ⟨4261534531020293434777507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5682046041360391246370009 4261534531020293434777507)
      ·
        refine ⟨6392301796530440152166261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261534531020293434777507 6392301796530440152166261)
        ·
          refine ⟨599278293424728764265587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6392301796530440152166261 599278293424728764265587)
          ·
            refine ⟨898917440137093146398381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599278293424728764265587 898917440137093146398381)
            ·
              refine ⟨337094040051409929899393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898917440137093146398381 337094040051409929899393)
              ·
                refine ⟨252820530038557447424545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337094040051409929899393 252820530038557447424545)
                ·
                  refine ⟨189615397528918085568409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252820530038557447424545 189615397528918085568409)
                  ·
                    rfl

theorem cell20_415434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_415434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415434 prefixEnd_415434 := by exact prefixLift 415434
  have htrace : WordTrace (prefixWord ++ tailWord_415434) baseStart_415434 baseEnd_415434 := by
    simpa [prefixWord, tailWord_415434, baseEnd_415434] using wordTrace_append hprefix tailTrace_415434
  have hstable : (prefixWord ++ tailWord_415434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415434).length < 2 ^ (prefixWord ++ tailWord_415434).sum := by decide
  have hdescent : baseEnd_415434 < baseStart_415434 := by decide
  rcases family_descends (prefixWord ++ tailWord_415434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415466 : List Nat := [3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_415466 : Nat := 118140960795 + 415466 * 2 ^ 59
def prefixEnd_415466 : Nat := 4983230072969 + 3 ^ 40 * 415466 * 2
def baseEnd_415466 : Nat := 63210001066956065500537

theorem tailTrace_415466 : CollatzResearch.WordTrace tailWord_415466 prefixEnd_415466 63210001066956065500537 := by
  unfold tailWord_415466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788322478211278197204563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10102193275230075192545501 3788322478211278197204563)
  ·
    refine ⟨5682483717316917295806845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788322478211278197204563 5682483717316917295806845)
    ·
      refine ⟨2130931393993843985927567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5682483717316917295806845 2130931393993843985927567)
      ·
        refine ⟨3196397090990765978891351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130931393993843985927567 3196397090990765978891351)
        ·
          refine ⟨4794595636486148968337027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196397090990765978891351 4794595636486148968337027)
          ·
            refine ⟨7191893454729223452505541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794595636486148968337027 7191893454729223452505541)
            ·
              refine ⟨1348480022761729397344789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7191893454729223452505541 1348480022761729397344789)
              ·
                refine ⟨63210001066956065500537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1348480022761729397344789 63210001066956065500537)
                ·
                  rfl

theorem cell20_415466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_415466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415466 prefixEnd_415466 := by exact prefixLift 415466
  have htrace : WordTrace (prefixWord ++ tailWord_415466) baseStart_415466 baseEnd_415466 := by
    simpa [prefixWord, tailWord_415466, baseEnd_415466] using wordTrace_append hprefix tailTrace_415466
  have hstable : (prefixWord ++ tailWord_415466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415466).length < 2 ^ (prefixWord ++ tailWord_415466).sum := by decide
  have hdescent : baseEnd_415466 < baseStart_415466 := by decide
  rcases family_descends (prefixWord ++ tailWord_415466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415480 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_415480 : Nat := 118140960795 + 415480 * 2 ^ 59
def prefixEnd_415480 : Nat := 4983230072969 + 3 ^ 40 * 415480 * 2
def baseEnd_415480 : Nat := 189636393182346370034887

theorem tailTrace_415480 : CollatzResearch.WordTrace tailWord_415480 prefixEnd_415480 189636393182346370034887 := by
  unfold tailWord_415480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576900267397196589913947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10102533689862928786551929 7576900267397196589913947)
  ·
    refine ⟨11365350401095794884870921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7576900267397196589913947 11365350401095794884870921)
    ·
      refine ⟨8524012800821846163653191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365350401095794884870921 8524012800821846163653191)
      ·
        refine ⟨12786019201232769245479787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524012800821846163653191 12786019201232769245479787)
        ·
          refine ⟨19179028801849153868219681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786019201232769245479787 19179028801849153868219681)
          ·
            refine ⟨14384271601386865401164761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19179028801849153868219681 14384271601386865401164761)
            ·
              refine ⟨10788203701040149050873571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384271601386865401164761 10788203701040149050873571)
              ·
                refine ⟨16182305551560223576310357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788203701040149050873571 16182305551560223576310357)
                ·
                  refine ⟨189636393182346370034887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16182305551560223576310357 189636393182346370034887)
                  ·
                    rfl

theorem cell20_415480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_415480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415480 prefixEnd_415480 := by exact prefixLift 415480
  have htrace : WordTrace (prefixWord ++ tailWord_415480) baseStart_415480 baseEnd_415480 := by
    simpa [prefixWord, tailWord_415480, baseEnd_415480] using wordTrace_append hprefix tailTrace_415480
  have hstable : (prefixWord ++ tailWord_415480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415480).length < 2 ^ (prefixWord ++ tailWord_415480).sum := by decide
  have hdescent : baseEnd_415480 < baseStart_415480 := by decide
  rcases family_descends (prefixWord ++ tailWord_415480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415486 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_415486 : Nat := 118140960795 + 415486 * 2 ^ 59
def prefixEnd_415486 : Nat := 4983230072969 + 3 ^ 40 * 415486 * 2
def baseEnd_415486 : Nat := 189639131745837015834863

theorem tailTrace_415486 : CollatzResearch.WordTrace tailWord_415486 prefixEnd_415486 189639131745837015834863 := by
  unfold tailWord_415486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894252421596582025568289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10102679581848437469697541 1894252421596582025568289)
  ·
    refine ⟨1420689316197436519176217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1894252421596582025568289 1420689316197436519176217)
    ·
      refine ⟨1065516987148077389382163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1420689316197436519176217 1065516987148077389382163)
      ·
        refine ⟨1598275480722116084073245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065516987148077389382163 1598275480722116084073245)
        ·
          refine ⟨599353305270793531527467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1598275480722116084073245 599353305270793531527467)
          ·
            refine ⟨899029957906190297291201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599353305270793531527467 899029957906190297291201)
            ·
              refine ⟨674272468429642722968401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899029957906190297291201 674272468429642722968401)
              ·
                refine ⟨505704351322232042226301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674272468429642722968401 505704351322232042226301)
                ·
                  refine ⟨189639131745837015834863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505704351322232042226301 189639131745837015834863)
                  ·
                    rfl

theorem cell20_415486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_415486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415486 prefixEnd_415486 := by exact prefixLift 415486
  have htrace : WordTrace (prefixWord ++ tailWord_415486) baseStart_415486 baseEnd_415486 := by
    simpa [prefixWord, tailWord_415486, baseEnd_415486] using wordTrace_append hprefix tailTrace_415486
  have hstable : (prefixWord ++ tailWord_415486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415486).length < 2 ^ (prefixWord ++ tailWord_415486).sum := by decide
  have hdescent : baseEnd_415486 < baseStart_415486 := by decide
  rcases family_descends (prefixWord ++ tailWord_415486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415521 : List Nat := [1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_415521 : Nat := 118140960795 + 415521 * 2 ^ 59
def prefixEnd_415521 : Nat := 4983230072969 + 3 ^ 40 * 415521 * 2
def baseEnd_415521 : Nat := 63218368899844149889351

theorem tailTrace_415521 : CollatzResearch.WordTrace tailWord_415521 prefixEnd_415521 63218368899844149889351 := by
  unfold tailWord_415521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155295927645857182070417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10103530618430571454713611 15155295927645857182070417)
  ·
    refine ⟨11366471945734392886552813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15155295927645857182070417 11366471945734392886552813)
    ·
      refine ⟨4262426979650397332457305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11366471945734392886552813 4262426979650397332457305)
      ·
        refine ⟨3196820234737797999342979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262426979650397332457305 3196820234737797999342979)
        ·
          refine ⟨4795230352106696999014469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196820234737797999342979 4795230352106696999014469)
          ·
            refine ⟨899105691020005687315213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4795230352106696999014469 899105691020005687315213)
            ·
              refine ⟨337164634132502132743205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899105691020005687315213 337164634132502132743205)
              ·
                refine ⟨63218368899844149889351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337164634132502132743205 63218368899844149889351)
                ·
                  rfl

theorem cell20_415521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_415521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415521 prefixEnd_415521 := by exact prefixLift 415521
  have htrace : WordTrace (prefixWord ++ tailWord_415521) baseStart_415521 baseEnd_415521 := by
    simpa [prefixWord, tailWord_415521, baseEnd_415521] using wordTrace_append hprefix tailTrace_415521
  have hstable : (prefixWord ++ tailWord_415521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415521).length < 2 ^ (prefixWord ++ tailWord_415521).sum := by decide
  have hdescent : baseEnd_415521 < baseStart_415521 := by decide
  rcases family_descends (prefixWord ++ tailWord_415521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415545 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_415545 : Nat := 118140960795 + 415545 * 2 ^ 59
def prefixEnd_415545 : Nat := 4983230072969 + 3 ^ 40 * 415545 * 2
def baseEnd_415545 : Nat := 189666060953495032867955

theorem tailTrace_415545 : CollatzResearch.WordTrace tailWord_415545 prefixEnd_415545 189666060953495032867955 := by
  unfold tailWord_415545
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156171279558909280944089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10104114186372606187296059 15156171279558909280944089)
  ·
    refine ⟨11367128459669181960708067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15156171279558909280944089 11367128459669181960708067)
    ·
      refine ⟨17050692689503772941062101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367128459669181960708067 17050692689503772941062101)
      ·
        refine ⟨399625609910244678306143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17050692689503772941062101 399625609910244678306143)
        ·
          refine ⟨599438414865367017459215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399625609910244678306143 599438414865367017459215)
          ·
            refine ⟨899157622298050526188823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599438414865367017459215 899157622298050526188823)
            ·
              refine ⟨1348736433447075789283235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899157622298050526188823 1348736433447075789283235)
              ·
                refine ⟨2023104650170613683924853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348736433447075789283235 2023104650170613683924853)
                ·
                  refine ⟨189666060953495032867955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2023104650170613683924853 189666060953495032867955)
                  ·
                    rfl

theorem cell20_415545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_415545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415545 prefixEnd_415545 := by exact prefixLift 415545
  have htrace : WordTrace (prefixWord ++ tailWord_415545) baseStart_415545 baseEnd_415545 := by
    simpa [prefixWord, tailWord_415545, baseEnd_415545] using wordTrace_append hprefix tailTrace_415545
  have hstable : (prefixWord ++ tailWord_415545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415545).length < 2 ^ (prefixWord ++ tailWord_415545).sum := by decide
  have hdescent : baseEnd_415545 < baseStart_415545 := by decide
  rcases family_descends (prefixWord ++ tailWord_415545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415573 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_415573 : Nat := 118140960795 + 415573 * 2 ^ 59
def prefixEnd_415573 : Nat := 4983230072969 + 3 ^ 40 * 415573 * 2
def baseEnd_415573 : Nat := 189678840916451379934507

theorem tailTrace_415573 : CollatzResearch.WordTrace tailWord_415573 prefixEnd_415573 189678840916451379934507 := by
  unfold tailWord_415573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15157192523457470062963373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10104795015638313375308915 15157192523457470062963373)
  ·
    refine ⟨5683947196296551273611265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15157192523457470062963373 5683947196296551273611265)
    ·
      refine ⟨4262960397222413455208449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5683947196296551273611265 4262960397222413455208449)
      ·
        refine ⟨3197220297916810091406337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262960397222413455208449 3197220297916810091406337)
        ·
          refine ⟨2397915223437607568554753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197220297916810091406337 2397915223437607568554753)
          ·
            refine ⟨1798436417578205676416065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397915223437607568554753 1798436417578205676416065)
            ·
              refine ⟨1348827313183654257312049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798436417578205676416065 1348827313183654257312049)
              ·
                refine ⟨1011620484887740692984037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348827313183654257312049 1011620484887740692984037)
                ·
                  refine ⟨189678840916451379934507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011620484887740692984037 189678840916451379934507)
                  ·
                    rfl

theorem cell20_415573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_415573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415573 prefixEnd_415573 := by exact prefixLift 415573
  have htrace : WordTrace (prefixWord ++ tailWord_415573) baseStart_415573 baseEnd_415573 := by
    simpa [prefixWord, tailWord_415573, baseEnd_415573] using wordTrace_append hprefix tailTrace_415573
  have hstable : (prefixWord ++ tailWord_415573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415573).length < 2 ^ (prefixWord ++ tailWord_415573).sum := by decide
  have hdescent : baseEnd_415573 < baseStart_415573 := by decide
  rcases family_descends (prefixWord ++ tailWord_415573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415586 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_415586 : Nat := 118140960795 + 415586 * 2 ^ 59
def prefixEnd_415586 : Nat := 4983230072969 + 3 ^ 40 * 415586 * 2
def baseEnd_415586 : Nat := 189684774470681112501121

theorem tailTrace_415586 : CollatzResearch.WordTrace tailWord_415586 prefixEnd_415586 189684774470681112501121 := by
  unfold tailWord_415586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789416668102593320796653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10105111114940248855457741 3789416668102593320796653)
  ·
    refine ⟨1421031250538472495298745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3789416668102593320796653 1421031250538472495298745)
    ·
      refine ⟨1065773437903854371474059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421031250538472495298745 1065773437903854371474059)
      ·
        refine ⟨1598660156855781557211089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065773437903854371474059 1598660156855781557211089)
        ·
          refine ⟨1198995117641836167908317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598660156855781557211089 1198995117641836167908317)
          ·
            refine ⟨449623169115688562965619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1198995117641836167908317 449623169115688562965619)
            ·
              refine ⟨674434753673532844448429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449623169115688562965619 674434753673532844448429)
              ·
                refine ⟨252913032627574816668161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674434753673532844448429 252913032627574816668161)
                ·
                  refine ⟨189684774470681112501121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252913032627574816668161 189684774470681112501121)
                  ·
                    rfl

theorem cell20_415586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_415586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415586 prefixEnd_415586 := by exact prefixLift 415586
  have htrace : WordTrace (prefixWord ++ tailWord_415586) baseStart_415586 baseEnd_415586 := by
    simpa [prefixWord, tailWord_415586, baseEnd_415586] using wordTrace_append hprefix tailTrace_415586
  have hstable : (prefixWord ++ tailWord_415586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415586).length < 2 ^ (prefixWord ++ tailWord_415586).sum := by decide
  have hdescent : baseEnd_415586 < baseStart_415586 := by decide
  rcases family_descends (prefixWord ++ tailWord_415586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415614 : List Nat := [4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_415614 : Nat := 118140960795 + 415614 * 2 ^ 59
def prefixEnd_415614 : Nat := 4983230072969 + 3 ^ 40 * 415614 * 2
def baseEnd_415614 : Nat := 63232518144545819855891

theorem tailTrace_415614 : CollatzResearch.WordTrace tailWord_415614 prefixEnd_415614 63232518144545819855891 := by
  unfold tailWord_415614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894835989538616758150737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10105791944205956043470597 1894835989538616758150737)
  ·
    refine ⟨1421126992153962568613053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1894835989538616758150737 1421126992153962568613053)
    ·
      refine ⟨532922622057735963229895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1421126992153962568613053 532922622057735963229895)
      ·
        refine ⟨799383933086603944844843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532922622057735963229895 799383933086603944844843)
        ·
          refine ⟨1199075899629905917267265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799383933086603944844843 1199075899629905917267265)
          ·
            refine ⟨899306924722429437950449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199075899629905917267265 899306924722429437950449)
            ·
              refine ⟨674480193541822078462837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899306924722429437950449 674480193541822078462837)
              ·
                refine ⟨63232518144545819855891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674480193541822078462837 63232518144545819855891)
                ·
                  rfl

theorem cell20_415614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_415614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415614 prefixEnd_415614 := by exact prefixLift 415614
  have htrace : WordTrace (prefixWord ++ tailWord_415614) baseStart_415614 baseEnd_415614 := by
    simpa [prefixWord, tailWord_415614, baseEnd_415614] using wordTrace_append hprefix tailTrace_415614
  have hstable : (prefixWord ++ tailWord_415614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415614).length < 2 ^ (prefixWord ++ tailWord_415614).sum := by decide
  have hdescent : baseEnd_415614 < baseStart_415614 := by decide
  rcases family_descends (prefixWord ++ tailWord_415614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415617 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_415617 : Nat := 118140960795 + 415617 * 2 ^ 59
def prefixEnd_415617 : Nat := 4983230072969 + 3 ^ 40 * 415617 * 2
def baseEnd_415617 : Nat := 189698923715382782467661

theorem tailTrace_415617 : CollatzResearch.WordTrace tailWord_415617 prefixEnd_415617 189698923715382782467661 := by
  unfold tailWord_415617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158797335298065577565105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10105864890198710385043403 15158797335298065577565105)
  ·
    refine ⟨11369098001473549183173829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15158797335298065577565105 11369098001473549183173829)
    ·
      refine ⟨2131705875276290471845093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11369098001473549183173829 2131705875276290471845093)
      ·
        refine ⟨399694851614304463470955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2131705875276290471845093 399694851614304463470955)
        ·
          refine ⟨599542277421456695206433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399694851614304463470955 599542277421456695206433)
          ·
            refine ⟨449656708066092521404825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599542277421456695206433 449656708066092521404825)
            ·
              refine ⟨337242531049569391053619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449656708066092521404825 337242531049569391053619)
              ·
                refine ⟨505863796574354086580429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337242531049569391053619 505863796574354086580429)
                ·
                  refine ⟨189698923715382782467661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505863796574354086580429 189698923715382782467661)
                  ·
                    rfl

theorem cell20_415617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_415617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415617 prefixEnd_415617 := by exact prefixLift 415617
  have htrace : WordTrace (prefixWord ++ tailWord_415617) baseStart_415617 baseEnd_415617 := by
    simpa [prefixWord, tailWord_415617, baseEnd_415617] using wordTrace_append hprefix tailTrace_415617
  have hstable : (prefixWord ++ tailWord_415617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415617).length < 2 ^ (prefixWord ++ tailWord_415617).sum := by decide
  have hdescent : baseEnd_415617 < baseStart_415617 := by decide
  rcases family_descends (prefixWord ++ tailWord_415617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415704 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_415704 : Nat := 118140960795 + 415704 * 2 ^ 59
def prefixEnd_415704 : Nat := 4983230072969 + 3 ^ 40 * 415704 * 2
def baseEnd_415704 : Nat := 189738632885997146567305

theorem tailTrace_415704 : CollatzResearch.WordTrace tailWord_415704 prefixEnd_415704 189738632885997146567305 := by
  unfold tailWord_415704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580985242991439717991083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10107980323988586290654777 7580985242991439717991083)
  ·
    refine ⟨11371477864487159576986625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580985242991439717991083 11371477864487159576986625)
    ·
      refine ⟨8528608398365369682739969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11371477864487159576986625 8528608398365369682739969)
      ·
        refine ⟨6396456298774027262054977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8528608398365369682739969 6396456298774027262054977)
        ·
          refine ⟨4797342224080520446541233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6396456298774027262054977 4797342224080520446541233)
          ·
            refine ⟨3598006668060390334905925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4797342224080520446541233 3598006668060390334905925)
            ·
              refine ⟨674626250261323187794861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3598006668060390334905925 674626250261323187794861)
              ·
                refine ⟨252984843847996195423073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674626250261323187794861 252984843847996195423073)
                ·
                  refine ⟨189738632885997146567305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252984843847996195423073 189738632885997146567305)
                  ·
                    rfl

theorem cell20_415704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_415704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415704 prefixEnd_415704 := by exact prefixLift 415704
  have htrace : WordTrace (prefixWord ++ tailWord_415704) baseStart_415704 baseEnd_415704 := by
    simpa [prefixWord, tailWord_415704, baseEnd_415704] using wordTrace_append hprefix tailTrace_415704
  have hstable : (prefixWord ++ tailWord_415704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415704).length < 2 ^ (prefixWord ++ tailWord_415704).sum := by decide
  have hdescent : baseEnd_415704 < baseStart_415704 := by decide
  rcases family_descends (prefixWord ++ tailWord_415704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415739 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_415739 : Nat := 118140960795 + 415739 * 2 ^ 59
def prefixEnd_415739 : Nat := 4983230072969 + 3 ^ 40 * 415739 * 2
def baseEnd_415739 : Nat := 189754607839692580400495

theorem tailTrace_415739 : CollatzResearch.WordTrace tailWord_415739 prefixEnd_415739 189754607839692580400495 := by
  unfold tailWord_415739
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163247040856080413506271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10108831360570720275670847 15163247040856080413506271)
  ·
    refine ⟨22744870561284120620259407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15163247040856080413506271 22744870561284120620259407)
    ·
      refine ⟨34117305841926180930389111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22744870561284120620259407 34117305841926180930389111)
      ·
        refine ⟨51175958762889271395583667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34117305841926180930389111 51175958762889271395583667)
        ·
          refine ⟨76763938144333907093375501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51175958762889271395583667 76763938144333907093375501)
          ·
            refine ⟨28786476804125215160015813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76763938144333907093375501 28786476804125215160015813)
            ·
              refine ⟨5397464400773477842502965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28786476804125215160015813 5397464400773477842502965)
              ·
                refine ⟨506012287572513547734653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5397464400773477842502965 506012287572513547734653)
                ·
                  refine ⟨189754607839692580400495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506012287572513547734653 189754607839692580400495)
                  ·
                    rfl

theorem cell20_415739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_415739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415739 prefixEnd_415739 := by exact prefixLift 415739
  have htrace : WordTrace (prefixWord ++ tailWord_415739) baseStart_415739 baseEnd_415739 := by
    simpa [prefixWord, tailWord_415739, baseEnd_415739] using wordTrace_append hprefix tailTrace_415739
  have hstable : (prefixWord ++ tailWord_415739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415739).length < 2 ^ (prefixWord ++ tailWord_415739).sum := by decide
  have hdescent : baseEnd_415739 < baseStart_415739 := by decide
  rcases family_descends (prefixWord ++ tailWord_415739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415742 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_415742 : Nat := 118140960795 + 415742 * 2 ^ 59
def prefixEnd_415742 : Nat := 4983230072969 + 3 ^ 40 * 415742 * 2
def baseEnd_415742 : Nat := 189755977121437903300483

theorem tailTrace_415742 : CollatzResearch.WordTrace tailWord_415742 prefixEnd_415742 189755977121437903300483 := by
  unfold tailWord_415742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895419557480651490733185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10108904306563474617243653 1895419557480651490733185)
  ·
    refine ⟨1421564668110488618049889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1895419557480651490733185 1421564668110488618049889)
    ·
      refine ⟨1066173501082866463537417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421564668110488618049889 1066173501082866463537417)
      ·
        refine ⟨799630125812149847653063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066173501082866463537417 799630125812149847653063)
        ·
          refine ⟨1199445188718224771479595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799630125812149847653063 1199445188718224771479595)
          ·
            refine ⟨1799167783077337157219393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199445188718224771479595 1799167783077337157219393)
            ·
              refine ⟨1349375837308002867914545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799167783077337157219393 1349375837308002867914545)
              ·
                refine ⟨1012031877981002150935909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349375837308002867914545 1012031877981002150935909)
                ·
                  refine ⟨189755977121437903300483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012031877981002150935909 189755977121437903300483)
                  ·
                    rfl

theorem cell20_415742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_415742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415742 prefixEnd_415742 := by exact prefixLift 415742
  have htrace : WordTrace (prefixWord ++ tailWord_415742) baseStart_415742 baseEnd_415742 := by
    simpa [prefixWord, tailWord_415742, baseEnd_415742] using wordTrace_append hprefix tailTrace_415742
  have hstable : (prefixWord ++ tailWord_415742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415742).length < 2 ^ (prefixWord ++ tailWord_415742).sum := by decide
  have hdescent : baseEnd_415742 < baseStart_415742 := by decide
  rcases family_descends (prefixWord ++ tailWord_415742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415749 : List Nat := [1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_415749 : Nat := 118140960795 + 415749 * 2 ^ 59
def prefixEnd_415749 : Nat := 4983230072969 + 3 ^ 40 * 415749 * 2
def baseEnd_415749 : Nat := 63253057370725663355707

theorem tailTrace_415749 : CollatzResearch.WordTrace tailWord_415749 prefixEnd_415749 63253057370725663355707 := by
  unfold tailWord_415749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163611770819852121370301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109074513879901414246867 15163611770819852121370301)
  ·
    refine ⟨5686354414057444545513863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15163611770819852121370301 5686354414057444545513863)
    ·
      refine ⟨8529531621086166818270795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686354414057444545513863 8529531621086166818270795)
      ·
        refine ⟨12794297431629250227406193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529531621086166818270795 12794297431629250227406193)
        ·
          refine ⟨9595723073721937670554645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12794297431629250227406193 9595723073721937670554645)
          ·
            refine ⟨449799519080715828307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9595723073721937670554645 449799519080715828307249)
            ·
              refine ⟨337349639310536871230437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449799519080715828307249 337349639310536871230437)
              ·
                refine ⟨63253057370725663355707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337349639310536871230437 63253057370725663355707)
                ·
                  rfl

theorem cell20_415749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_415749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415749 prefixEnd_415749 := by exact prefixLift 415749
  have htrace : WordTrace (prefixWord ++ tailWord_415749) baseStart_415749 baseEnd_415749 := by
    simpa [prefixWord, tailWord_415749, baseEnd_415749] using wordTrace_append hprefix tailTrace_415749
  have hstable : (prefixWord ++ tailWord_415749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415749).length < 2 ^ (prefixWord ++ tailWord_415749).sum := by decide
  have hdescent : baseEnd_415749 < baseStart_415749 := by decide
  rcases family_descends (prefixWord ++ tailWord_415749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415770 : List Nat := [3, 1, 1, 3, 1, 5, 6]
def baseStart_415770 : Nat := 118140960795 + 415770 * 2 ^ 59
def prefixEnd_415770 : Nat := 4983230072969 + 3 ^ 40 * 415770 * 2
def baseEnd_415770 : Nat := 21085417453821583374115

theorem tailTrace_415770 : CollatzResearch.WordTrace tailWord_415770 prefixEnd_415770 21085417453821583374115 := by
  unfold tailWord_415770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791094425935943176971191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10109585135829181805256509 3791094425935943176971191)
  ·
    refine ⟨5686641638903914765456787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791094425935943176971191 5686641638903914765456787)
    ·
      refine ⟨8529962458355872148185181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686641638903914765456787 8529962458355872148185181)
      ·
        refine ⟨3198735921883452055569443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8529962458355872148185181 3198735921883452055569443)
        ·
          refine ⟨4798103882825178083354165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198735921883452055569443 4798103882825178083354165)
          ·
            refine ⟨449822239014860445314453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4798103882825178083354165 449822239014860445314453)
            ·
              refine ⟨21085417453821583374115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449822239014860445314453 21085417453821583374115)
              ·
                rfl

theorem cell20_415770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_415770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415770 prefixEnd_415770 := by exact prefixLift 415770
  have htrace : WordTrace (prefixWord ++ tailWord_415770) baseStart_415770 baseEnd_415770 := by
    simpa [prefixWord, tailWord_415770, baseEnd_415770] using wordTrace_append hprefix tailTrace_415770
  have hstable : (prefixWord ++ tailWord_415770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415770).length < 2 ^ (prefixWord ++ tailWord_415770).sum := by decide
  have hdescent : baseEnd_415770 < baseStart_415770 := by decide
  rcases family_descends (prefixWord ++ tailWord_415770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415790 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_415790 : Nat := 118140960795 + 415790 * 2 ^ 59
def prefixEnd_415790 : Nat := 4983230072969 + 3 ^ 40 * 415790 * 2
def baseEnd_415790 : Nat := 189777885629363069700287

theorem tailTrace_415790 : CollatzResearch.WordTrace tailWord_415790 prefixEnd_415790 189777885629363069700287 := by
  unfold tailWord_415790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895638395458914515451603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10110071442447544082408549 1895638395458914515451603)
  ·
    refine ⟨2843457593188371773177405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895638395458914515451603 2843457593188371773177405)
    ·
      refine ⟨1066296597445639414941527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2843457593188371773177405 1066296597445639414941527)
      ·
        refine ⟨1599444896168459122412291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066296597445639414941527 1599444896168459122412291)
        ·
          refine ⟨2399167344252688683618437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599444896168459122412291 2399167344252688683618437)
          ·
            refine ⟨449843877047379128178457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2399167344252688683618437 449843877047379128178457)
            ·
              refine ⟨337382907785534346133843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449843877047379128178457 337382907785534346133843)
              ·
                refine ⟨506074361678301519200765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337382907785534346133843 506074361678301519200765)
                ·
                  refine ⟨189777885629363069700287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506074361678301519200765 189777885629363069700287)
                  ·
                    rfl

theorem cell20_415790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_415790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415790 prefixEnd_415790 := by exact prefixLift 415790
  have htrace : WordTrace (prefixWord ++ tailWord_415790) baseStart_415790 baseEnd_415790 := by
    simpa [prefixWord, tailWord_415790, baseEnd_415790] using wordTrace_append hprefix tailTrace_415790
  have hstable : (prefixWord ++ tailWord_415790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415790).length < 2 ^ (prefixWord ++ tailWord_415790).sum := by decide
  have hdescent : baseEnd_415790 < baseStart_415790 := by decide
  rcases family_descends (prefixWord ++ tailWord_415790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415794 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_415794 : Nat := 118140960795 + 415794 * 2 ^ 59
def prefixEnd_415794 : Nat := 4983230072969 + 3 ^ 40 * 415794 * 2
def baseEnd_415794 : Nat := 189779711338356833566937

theorem tailTrace_415794 : CollatzResearch.WordTrace tailWord_415794 prefixEnd_415794 189779711338356833566937 := by
  unfold tailWord_415794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791313263914206201689609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10110168703771216537838957 3791313263914206201689609)
  ·
    refine ⟨2843484947935654651267207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791313263914206201689609 2843484947935654651267207)
    ·
      refine ⟨4265227421903481976900811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843484947935654651267207 4265227421903481976900811)
      ·
        refine ⟨6397841132855222965351217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265227421903481976900811 6397841132855222965351217)
        ·
          refine ⟨4798380849641417224013413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6397841132855222965351217 4798380849641417224013413)
          ·
            refine ⟨899696409307765729502515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4798380849641417224013413 899696409307765729502515)
            ·
              refine ⟨1349544613961648594253773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899696409307765729502515 1349544613961648594253773)
              ·
                refine ⟨506079230235618222845165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1349544613961648594253773 506079230235618222845165)
                ·
                  refine ⟨189779711338356833566937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506079230235618222845165 189779711338356833566937)
                  ·
                    rfl

theorem cell20_415794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_415794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415794 prefixEnd_415794 := by exact prefixLift 415794
  have htrace : WordTrace (prefixWord ++ tailWord_415794) baseStart_415794 baseEnd_415794 := by
    simpa [prefixWord, tailWord_415794, baseEnd_415794] using wordTrace_append hprefix tailTrace_415794
  have hstable : (prefixWord ++ tailWord_415794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415794).length < 2 ^ (prefixWord ++ tailWord_415794).sum := by decide
  have hdescent : baseEnd_415794 < baseStart_415794 := by decide
  rcases family_descends (prefixWord ++ tailWord_415794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415829 : List Nat := [1, 3, 2, 2, 1, 11]
def baseStart_415829 : Nat := 118140960795 + 415829 * 2 ^ 59
def prefixEnd_415829 : Nat := 4983230072969 + 3 ^ 40 * 415829 * 2
def baseEnd_415829 : Nat := 7029469862668602496301

theorem tailTrace_415829 : CollatzResearch.WordTrace tailWord_415829 prefixEnd_415829 7029469862668602496301 := by
  unfold tailWord_415829
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166529610530025784282541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10111019740353350522855027 15166529610530025784282541)
  ·
    refine ⟨5687448603948759669105953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15166529610530025784282541 5687448603948759669105953)
    ·
      refine ⟨4265586452961569751829465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5687448603948759669105953 4265586452961569751829465)
      ·
        refine ⟨3199189839721177313872099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265586452961569751829465 3199189839721177313872099)
        ·
          refine ⟨4798784759581765970808149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199189839721177313872099 4798784759581765970808149)
          ·
            refine ⟨7029469862668602496301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4798784759581765970808149 7029469862668602496301)
            ·
              rfl

theorem cell20_415829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_415829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415829 prefixEnd_415829 := by exact prefixLift 415829
  have htrace : WordTrace (prefixWord ++ tailWord_415829) baseStart_415829 baseEnd_415829 := by
    simpa [prefixWord, tailWord_415829, baseEnd_415829] using wordTrace_append hprefix tailTrace_415829
  have hstable : (prefixWord ++ tailWord_415829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415829).length < 2 ^ (prefixWord ++ tailWord_415829).sum := by decide
  have hdescent : baseEnd_415829 < baseStart_415829 := by decide
  rcases family_descends (prefixWord ++ tailWord_415829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415832 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_415832 : Nat := 118140960795 + 415832 * 2 ^ 59
def prefixEnd_415832 : Nat := 4983230072969 + 3 ^ 40 * 415832 * 2
def baseEnd_415832 : Nat := 189797055573797590300115

theorem tailTrace_415832 : CollatzResearch.WordTrace tailWord_415832 prefixEnd_415832 189797055573797590300115 := by
  unfold tailWord_415832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583319514759578648320875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10111092686346104864427833 7583319514759578648320875)
  ·
    refine ⟨11374979272139367972481313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7583319514759578648320875 11374979272139367972481313)
    ·
      refine ⟨8531234454104525979360985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11374979272139367972481313 8531234454104525979360985)
      ·
        refine ⟨6398425840578394484520739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8531234454104525979360985 6398425840578394484520739)
        ·
          refine ⟨9597638760867591726781109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398425840578394484520739 9597638760867591726781109)
          ·
            refine ⟨899778633831336724385729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9597638760867591726781109 899778633831336724385729)
            ·
              refine ⟨674833975373502543289297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899778633831336724385729 674833975373502543289297)
              ·
                refine ⟨506125481530126907466973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674833975373502543289297 506125481530126907466973)
                ·
                  refine ⟨189797055573797590300115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506125481530126907466973 189797055573797590300115)
                  ·
                    rfl

theorem cell20_415832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_415832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415832 prefixEnd_415832 := by exact prefixLift 415832
  have htrace : WordTrace (prefixWord ++ tailWord_415832) baseStart_415832 baseEnd_415832 := by
    simpa [prefixWord, tailWord_415832, baseEnd_415832] using wordTrace_append hprefix tailTrace_415832
  have hstable : (prefixWord ++ tailWord_415832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415832).length < 2 ^ (prefixWord ++ tailWord_415832).sum := by decide
  have hdescent : baseEnd_415832 < baseStart_415832 := by decide
  rcases family_descends (prefixWord ++ tailWord_415832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415838 : List Nat := [4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_415838 : Nat := 118140960795 + 415838 * 2 ^ 59
def prefixEnd_415838 : Nat := 4983230072969 + 3 ^ 40 * 415838 * 2
def baseEnd_415838 : Nat := 63266598045762745366697

theorem tailTrace_415838 : CollatzResearch.WordTrace tailWord_415838 prefixEnd_415838 63266598045762745366697 := by
  unfold tailWord_415838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895857233437177540170021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10111238578331613547573445 1895857233437177540170021)
  ·
    refine ⟨355473231269470788781879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1895857233437177540170021 355473231269470788781879)
    ·
      refine ⟨533209846904206183172819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355473231269470788781879 533209846904206183172819)
      ·
        refine ⟨799814770356309274759229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533209846904206183172819 799814770356309274759229)
        ·
          refine ⟨299930538883615978034711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 799814770356309274759229 299930538883615978034711)
          ·
            refine ⟨449895808325423967052067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299930538883615978034711 449895808325423967052067)
            ·
              refine ⟨674843712488135950578101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449895808325423967052067 674843712488135950578101)
              ·
                refine ⟨63266598045762745366697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674843712488135950578101 63266598045762745366697)
                ·
                  rfl

theorem cell20_415838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_415838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415838 prefixEnd_415838 := by exact prefixLift 415838
  have htrace : WordTrace (prefixWord ++ tailWord_415838) baseStart_415838 baseEnd_415838 := by
    simpa [prefixWord, tailWord_415838, baseEnd_415838] using wordTrace_append hprefix tailTrace_415838
  have hstable : (prefixWord ++ tailWord_415838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415838).length < 2 ^ (prefixWord ++ tailWord_415838).sum := by decide
  have hdescent : baseEnd_415838 < baseStart_415838 := by decide
  rcases family_descends (prefixWord ++ tailWord_415838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415842 : List Nat := [3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_415842 : Nat := 118140960795 + 415842 * 2 ^ 59
def prefixEnd_415842 : Nat := 4983230072969 + 3 ^ 40 * 415842 * 2
def baseEnd_415842 : Nat := 63267206615427333322247

theorem tailTrace_415842 : CollatzResearch.WordTrace tailWord_415842 prefixEnd_415842 63267206615427333322247 := by
  unfold tailWord_415842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791750939870732251126445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10111335839655286003003853 3791750939870732251126445)
  ·
    refine ⟨1421906602451524594172417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3791750939870732251126445 1421906602451524594172417)
    ·
      refine ⟨1066429951838643445629313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421906602451524594172417 1066429951838643445629313)
      ·
        refine ⟨799822463878982584221985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066429951838643445629313 799822463878982584221985)
        ·
          refine ⟨599866847909236938166489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799822463878982584221985 599866847909236938166489)
          ·
            refine ⟨449900135931927703624867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599866847909236938166489 449900135931927703624867)
            ·
              refine ⟨674850203897891555437301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449900135931927703624867 674850203897891555437301)
              ·
                refine ⟨63267206615427333322247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674850203897891555437301 63267206615427333322247)
                ·
                  rfl

theorem cell20_415842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_415842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415842 prefixEnd_415842 := by exact prefixLift 415842
  have htrace : WordTrace (prefixWord ++ tailWord_415842) baseStart_415842 baseEnd_415842 := by
    simpa [prefixWord, tailWord_415842, baseEnd_415842] using wordTrace_append hprefix tailTrace_415842
  have hstable : (prefixWord ++ tailWord_415842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415842).length < 2 ^ (prefixWord ++ tailWord_415842).sum := by decide
  have hdescent : baseEnd_415842 < baseStart_415842 := by decide
  rcases family_descends (prefixWord ++ tailWord_415842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415873 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 2]
def baseStart_415873 : Nat := 118140960795 + 415873 * 2 ^ 59
def prefixEnd_415873 : Nat := 4983230072969 + 3 ^ 40 * 415873 * 2
def baseEnd_415873 : Nat := 189815769090983669933281

theorem tailTrace_415873 : CollatzResearch.WordTrace tailWord_415873 prefixEnd_415873 189815769090983669933281 := by
  unfold tailWord_415873
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168134422370621298884273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10112089614913747532589515 15168134422370621298884273)
  ·
    refine ⟨11376100816777965974163205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15168134422370621298884273 11376100816777965974163205)
    ·
      refine ⟨2133018903145868620155601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11376100816777965974163205 2133018903145868620155601)
      ·
        refine ⟨1599764177359401465116701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2133018903145868620155601 1599764177359401465116701)
        ·
          refine ⟨599911566509775549418763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1599764177359401465116701 599911566509775549418763)
          ·
            refine ⟨899867349764663324128145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599911566509775549418763 899867349764663324128145)
            ·
              refine ⟨674900512323497493096109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899867349764663324128145 674900512323497493096109)
              ·
                refine ⟨253087692121311559911041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674900512323497493096109 253087692121311559911041)
                ·
                  refine ⟨189815769090983669933281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253087692121311559911041 189815769090983669933281)
                  ·
                    rfl

theorem cell20_415873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_415873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415873 prefixEnd_415873 := by exact prefixLift 415873
  have htrace : WordTrace (prefixWord ++ tailWord_415873) baseStart_415873 baseEnd_415873 := by
    simpa [prefixWord, tailWord_415873, baseEnd_415873] using wordTrace_append hprefix tailTrace_415873
  have hstable : (prefixWord ++ tailWord_415873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415873).length < 2 ^ (prefixWord ++ tailWord_415873).sum := by decide
  have hdescent : baseEnd_415873 < baseStart_415873 := by decide
  rcases family_descends (prefixWord ++ tailWord_415873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415918 : List Nat := [4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_415918 : Nat := 118140960795 + 415918 * 2 ^ 59
def prefixEnd_415918 : Nat := 4983230072969 + 3 ^ 40 * 415918 * 2
def baseEnd_415918 : Nat := 63278769439054504477699

theorem tailTrace_415918 : CollatzResearch.WordTrace tailWord_415918 prefixEnd_415918 63278769439054504477699 := by
  unfold tailWord_415918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896221963400949248034051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10113183804805062656181605 1896221963400949248034051)
  ·
    refine ⟨2844332945101423872051077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896221963400949248034051 2844332945101423872051077)
    ·
      refine ⟨533312427206516976009577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2844332945101423872051077 533312427206516976009577)
      ·
        refine ⟨399984320404887732007183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533312427206516976009577 399984320404887732007183)
        ·
          refine ⟨599976480607331598010775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399984320404887732007183 599976480607331598010775)
          ·
            refine ⟨899964720910997397016163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599976480607331598010775 899964720910997397016163)
            ·
              refine ⟨1349947081366496095524245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899964720910997397016163 1349947081366496095524245)
              ·
                refine ⟨63278769439054504477699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1349947081366496095524245 63278769439054504477699)
                ·
                  rfl

theorem cell20_415918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_415918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415918 prefixEnd_415918 := by exact prefixLift 415918
  have htrace : WordTrace (prefixWord ++ tailWord_415918) baseStart_415918 baseEnd_415918 := by
    simpa [prefixWord, tailWord_415918, baseEnd_415918] using wordTrace_append hprefix tailTrace_415918
  have hstable : (prefixWord ++ tailWord_415918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415918).length < 2 ^ (prefixWord ++ tailWord_415918).sum := by decide
  have hdescent : baseEnd_415918 < baseStart_415918 := by decide
  rcases family_descends (prefixWord ++ tailWord_415918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415924 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_415924 : Nat := 118140960795 + 415924 * 2 ^ 59
def prefixEnd_415924 : Nat := 4983230072969 + 3 ^ 40 * 415924 * 2
def baseEnd_415924 : Nat := 189839046880654159233073

theorem tailTrace_415924 : CollatzResearch.WordTrace tailWord_415924 prefixEnd_415924 189839046880654159233073 := by
  unfold tailWord_415924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584997272592928504495413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10113329696790571339327217 7584997272592928504495413)
  ·
    refine ⟨711093494305587047296445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7584997272592928504495413 711093494305587047296445)
    ·
      refine ⟨266660060364595142736167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 711093494305587047296445 266660060364595142736167)
      ·
        refine ⟨399990090546892714104251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266660060364595142736167 399990090546892714104251)
        ·
          refine ⟨599985135820339071156377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399990090546892714104251 599985135820339071156377)
          ·
            refine ⟨449988851865254303367283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599985135820339071156377 449988851865254303367283)
            ·
              refine ⟨674983277797881455050925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449988851865254303367283 674983277797881455050925)
              ·
                refine ⟨253118729174205545644097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674983277797881455050925 253118729174205545644097)
                ·
                  refine ⟨189839046880654159233073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253118729174205545644097 189839046880654159233073)
                  ·
                    rfl

theorem cell20_415924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_415924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415924 prefixEnd_415924 := by exact prefixLift 415924
  have htrace : WordTrace (prefixWord ++ tailWord_415924) baseStart_415924 baseEnd_415924 := by
    simpa [prefixWord, tailWord_415924, baseEnd_415924] using wordTrace_append hprefix tailTrace_415924
  have hstable : (prefixWord ++ tailWord_415924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415924).length < 2 ^ (prefixWord ++ tailWord_415924).sum := by decide
  have hdescent : baseEnd_415924 < baseStart_415924 := by decide
  rcases family_descends (prefixWord ++ tailWord_415924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415953 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 2]
def baseStart_415953 : Nat := 118140960795 + 415953 * 2 ^ 59
def prefixEnd_415953 : Nat := 4983230072969 + 3 ^ 40 * 415953 * 2
def baseEnd_415953 : Nat := 189852283270858947266287

theorem tailTrace_415953 : CollatzResearch.WordTrace tailWord_415953 prefixEnd_415953 189852283270858947266287 := by
  unfold tailWord_415953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171052262080794961796513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10114034841387196641197675 15171052262080794961796513)
  ·
    refine ⟨11378289196560596221347385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15171052262080794961796513 11378289196560596221347385)
    ·
      refine ⟨8533716897420447166010539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11378289196560596221347385 8533716897420447166010539)
      ·
        refine ⟨12800575346130670749015809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8533716897420447166010539 12800575346130670749015809)
        ·
          refine ⟨9600431509598003061761857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800575346130670749015809 9600431509598003061761857)
          ·
            refine ⟨7200323632198502296321393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9600431509598003061761857 7200323632198502296321393)
            ·
              refine ⟨5400242724148876722241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200323632198502296321393 5400242724148876722241045)
              ·
                refine ⟨253136377694478596355049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5400242724148876722241045 253136377694478596355049)
                ·
                  refine ⟨189852283270858947266287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253136377694478596355049 189852283270858947266287)
                  ·
                    rfl

theorem cell20_415953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_415953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415953 prefixEnd_415953 := by exact prefixLift 415953
  have htrace : WordTrace (prefixWord ++ tailWord_415953) baseStart_415953 baseEnd_415953 := by
    simpa [prefixWord, tailWord_415953, baseEnd_415953] using wordTrace_append hprefix tailTrace_415953
  have hstable : (prefixWord ++ tailWord_415953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415953).length < 2 ^ (prefixWord ++ tailWord_415953).sum := by decide
  have hdescent : baseEnd_415953 < baseStart_415953 := by decide
  rcases family_descends (prefixWord ++ tailWord_415953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415960 : List Nat := [2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_415960 : Nat := 118140960795 + 415960 * 2 ^ 59
def prefixEnd_415960 : Nat := 4983230072969 + 3 ^ 40 * 415960 * 2
def baseEnd_415960 : Nat := 63285159420532678010975

theorem tailTrace_415960 : CollatzResearch.WordTrace tailWord_415960 prefixEnd_415960 63285159420532678010975 := by
  unfold tailWord_415960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585653786527717578650667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10114205048703623438200889 7585653786527717578650667)
  ·
    refine ⟨11378480679791576367976001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585653786527717578650667 11378480679791576367976001)
    ·
      refine ⟨8533860509843682275982001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11378480679791576367976001 8533860509843682275982001)
      ·
        refine ⟨6400395382382761706986501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8533860509843682275982001 6400395382382761706986501)
        ·
          refine ⟨1200074134196767820059969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6400395382382761706986501 1200074134196767820059969)
          ·
            refine ⟨900055600647575865044977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200074134196767820059969 900055600647575865044977)
            ·
              refine ⟨675041700485681898783733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900055600647575865044977 675041700485681898783733)
              ·
                refine ⟨63285159420532678010975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675041700485681898783733 63285159420532678010975)
                ·
                  rfl

theorem cell20_415960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_415960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_415960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_415960 prefixEnd_415960 := by exact prefixLift 415960
  have htrace : WordTrace (prefixWord ++ tailWord_415960) baseStart_415960 baseEnd_415960 := by
    simpa [prefixWord, tailWord_415960, baseEnd_415960] using wordTrace_append hprefix tailTrace_415960
  have hstable : (prefixWord ++ tailWord_415960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415960).length < 2 ^ (prefixWord ++ tailWord_415960).sum := by decide
  have hdescent : baseEnd_415960 < baseStart_415960 := by decide
  rcases family_descends (prefixWord ++ tailWord_415960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416004 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_416004 : Nat := 118140960795 + 416004 * 2 ^ 59
def prefixEnd_416004 : Nat := 4983230072969 + 3 ^ 40 * 416004 * 2
def baseEnd_416004 : Nat := 189875561060529436566079

theorem tailTrace_416004 : CollatzResearch.WordTrace tailWord_416004 prefixEnd_416004 189875561060529436566079 := by
  unfold tailWord_416004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586456192448015335951533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10115274923264020447935377 7586456192448015335951533)
  ·
    refine ⟨2844921072168005750981825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7586456192448015335951533 2844921072168005750981825)
    ·
      refine ⟨2133690804126004313236369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2844921072168005750981825 2133690804126004313236369)
      ·
        refine ⟨1600268103094503234927277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2133690804126004313236369 1600268103094503234927277)
        ·
          refine ⟨600100538660438713097729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1600268103094503234927277 600100538660438713097729)
          ·
            refine ⟨450075403995329034823297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600100538660438713097729 450075403995329034823297)
            ·
              refine ⟨337556552996496776117473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450075403995329034823297 337556552996496776117473)
              ·
                refine ⟨253167414747372582088105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337556552996496776117473 253167414747372582088105)
                ·
                  refine ⟨189875561060529436566079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253167414747372582088105 189875561060529436566079)
                  ·
                    rfl

theorem cell20_416004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_416004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416004 prefixEnd_416004 := by exact prefixLift 416004
  have htrace : WordTrace (prefixWord ++ tailWord_416004) baseStart_416004 baseEnd_416004 := by
    simpa [prefixWord, tailWord_416004, baseEnd_416004] using wordTrace_append hprefix tailTrace_416004
  have hstable : (prefixWord ++ tailWord_416004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416004).length < 2 ^ (prefixWord ++ tailWord_416004).sum := by decide
  have hdescent : baseEnd_416004 < baseStart_416004 := by decide
  rcases family_descends (prefixWord ++ tailWord_416004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416008 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_416008 : Nat := 118140960795 + 416008 * 2 ^ 59
def prefixEnd_416008 : Nat := 4983230072969 + 3 ^ 40 * 416008 * 2
def baseEnd_416008 : Nat := 189877386769523200432729

theorem tailTrace_416008 : CollatzResearch.WordTrace tailWord_416008 prefixEnd_416008 189877386769523200432729 := by
  unfold tailWord_416008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586529138440769677524339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10115372184587692903365785 7586529138440769677524339)
  ·
    refine ⟨11379793707661154516286509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586529138440769677524339 11379793707661154516286509)
    ·
      refine ⟨4267422640372932943607441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11379793707661154516286509 4267422640372932943607441)
      ·
        refine ⟨3200566980279699707705581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4267422640372932943607441 3200566980279699707705581)
        ·
          refine ⟨1200212617604887390389593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3200566980279699707705581 1200212617604887390389593)
          ·
            refine ⟨900159463203665542792195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200212617604887390389593 900159463203665542792195)
            ·
              refine ⟨1350239194805498314188293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900159463203665542792195 1350239194805498314188293)
              ·
                refine ⟨253169849026030933910305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1350239194805498314188293 253169849026030933910305)
                ·
                  refine ⟨189877386769523200432729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253169849026030933910305 189877386769523200432729)
                  ·
                    rfl

theorem cell20_416008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_416008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416008 prefixEnd_416008 := by exact prefixLift 416008
  have htrace : WordTrace (prefixWord ++ tailWord_416008) baseStart_416008 baseEnd_416008 := by
    simpa [prefixWord, tailWord_416008, baseEnd_416008] using wordTrace_append hprefix tailTrace_416008
  have hstable : (prefixWord ++ tailWord_416008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416008).length < 2 ^ (prefixWord ++ tailWord_416008).sum := by decide
  have hdescent : baseEnd_416008 < baseStart_416008 := by decide
  rcases family_descends (prefixWord ++ tailWord_416008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416012 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_416012 : Nat := 118140960795 + 416012 * 2 ^ 59
def prefixEnd_416012 : Nat := 4983230072969 + 3 ^ 40 * 416012 * 2
def baseEnd_416012 : Nat := 189879212478516964299379

theorem tailTrace_416012 : CollatzResearch.WordTrace tailWord_416012 prefixEnd_416012 189879212478516964299379 := by
  unfold tailWord_416012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586602084433524019097145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10115469445911365358796193 7586602084433524019097145)
  ·
    refine ⟨5689951563325143014322859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7586602084433524019097145 5689951563325143014322859)
    ·
      refine ⟨8534927344987714521484289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689951563325143014322859 8534927344987714521484289)
      ·
        refine ⟨6401195508740785891113217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8534927344987714521484289 6401195508740785891113217)
        ·
          refine ⟨4800896631555589418334913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401195508740785891113217 4800896631555589418334913)
          ·
            refine ⟨3600672473666692063751185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800896631555589418334913 3600672473666692063751185)
            ·
              refine ⟨2700504355250019047813389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600672473666692063751185 2700504355250019047813389)
              ·
                refine ⟨1012689133218757142930021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700504355250019047813389 1012689133218757142930021)
                ·
                  refine ⟨189879212478516964299379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012689133218757142930021 189879212478516964299379)
                  ·
                    rfl

theorem cell20_416012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_416012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416012 prefixEnd_416012 := by exact prefixLift 416012
  have htrace : WordTrace (prefixWord ++ tailWord_416012) baseStart_416012 baseEnd_416012 := by
    simpa [prefixWord, tailWord_416012, baseEnd_416012] using wordTrace_append hprefix tailTrace_416012
  have hstable : (prefixWord ++ tailWord_416012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416012).length < 2 ^ (prefixWord ++ tailWord_416012).sum := by decide
  have hdescent : baseEnd_416012 < baseStart_416012 := by decide
  rcases family_descends (prefixWord ++ tailWord_416012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416067 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 2]
def baseStart_416067 : Nat := 118140960795 + 416067 * 2 ^ 59
def prefixEnd_416067 : Nat := 4983230072969 + 3 ^ 40 * 416067 * 2
def baseEnd_416067 : Nat := 189904315977181217465821

theorem tailTrace_416067 : CollatzResearch.WordTrace tailWord_416067 prefixEnd_416067 189904315977181217465821 := by
  unfold tailWord_416067
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175210183667792431446455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10116806789111861620964303 15175210183667792431446455)
  ·
    refine ⟨22762815275501688647169683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175210183667792431446455 22762815275501688647169683)
    ·
      refine ⟨34144222913252532970754525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762815275501688647169683 34144222913252532970754525)
      ·
        refine ⟨12804083592469699864032947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34144222913252532970754525 12804083592469699864032947)
        ·
          refine ⟨19206125388704549796049421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804083592469699864032947 19206125388704549796049421)
          ·
            refine ⟨7202297020764206173518533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19206125388704549796049421 7202297020764206173518533)
            ·
              refine ⟨1350430691393288657534725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7202297020764206173518533 1350430691393288657534725)
              ·
                refine ⟨253205754636241623287761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1350430691393288657534725 253205754636241623287761)
                ·
                  refine ⟨189904315977181217465821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253205754636241623287761 189904315977181217465821)
                  ·
                    rfl

theorem cell20_416067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2].length) (baseStart_416067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416067 prefixEnd_416067 := by exact prefixLift 416067
  have htrace : WordTrace (prefixWord ++ tailWord_416067) baseStart_416067 baseEnd_416067 := by
    simpa [prefixWord, tailWord_416067, baseEnd_416067] using wordTrace_append hprefix tailTrace_416067
  have hstable : (prefixWord ++ tailWord_416067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416067).length < 2 ^ (prefixWord ++ tailWord_416067).sum := by decide
  have hdescent : baseEnd_416067 < baseStart_416067 := by decide
  rcases family_descends (prefixWord ++ tailWord_416067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416118 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_416118 : Nat := 118140960795 + 416118 * 2 ^ 59
def prefixEnd_416118 : Nat := 4983230072969 + 3 ^ 40 * 416118 * 2
def baseEnd_416118 : Nat := 189927593766851706765613

theorem tailTrace_416118 : CollatzResearch.WordTrace tailWord_416118 prefixEnd_416118 189927593766851706765613 := by
  unfold tailWord_416118
  simp only [CollatzResearch.WordTrace]
  refine ⟨948566894155189258847063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10118046870988685427702005 948566894155189258847063)
  ·
    refine ⟨1422850341232783888270595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948566894155189258847063 1422850341232783888270595)
    ·
      refine ⟨2134275511849175832405893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422850341232783888270595 2134275511849175832405893)
      ·
        refine ⟨400176658471720468576105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2134275511849175832405893 400176658471720468576105)
        ·
          refine ⟨300132493853790351432079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400176658471720468576105 300132493853790351432079)
          ·
            refine ⟨450198740780685527148119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300132493853790351432079 450198740780685527148119)
            ·
              refine ⟨675298111171028290722179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450198740780685527148119 675298111171028290722179)
              ·
                refine ⟨1012947166756542436083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675298111171028290722179 1012947166756542436083269)
                ·
                  refine ⟨189927593766851706765613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012947166756542436083269 189927593766851706765613)
                  ·
                    rfl

theorem cell20_416118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_416118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416118 prefixEnd_416118 := by exact prefixLift 416118
  have htrace : WordTrace (prefixWord ++ tailWord_416118) baseStart_416118 baseEnd_416118 := by
    simpa [prefixWord, tailWord_416118, baseEnd_416118] using wordTrace_append hprefix tailTrace_416118
  have hstable : (prefixWord ++ tailWord_416118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416118).length < 2 ^ (prefixWord ++ tailWord_416118).sum := by decide
  have hdescent : baseEnd_416118 < baseStart_416118 := by decide
  rcases family_descends (prefixWord ++ tailWord_416118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416173 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 2]
def baseStart_416173 : Nat := 118140960795 + 416173 * 2 ^ 59
def prefixEnd_416173 : Nat := 4983230072969 + 3 ^ 40 * 416173 * 2
def baseEnd_416173 : Nat := 189952697265515959932055

theorem tailTrace_416173 : CollatzResearch.WordTrace tailWord_416173 prefixEnd_416173 189952697265515959932055 := by
  unfold tailWord_416173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179076321283772534805173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10119384214189181689870115 15179076321283772534805173)
  ·
    refine ⟨1423038405120353675137985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15179076321283772534805173 1423038405120353675137985)
    ·
      refine ⟨1067278803840265256353489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423038405120353675137985 1067278803840265256353489)
      ·
        refine ⟨800459102880198942265117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067278803840265256353489 800459102880198942265117)
        ·
          refine ⟨300172163580074603349419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800459102880198942265117 300172163580074603349419)
          ·
            refine ⟨450258245370111905024129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300172163580074603349419 450258245370111905024129)
            ·
              refine ⟨337693684027583928768097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450258245370111905024129 337693684027583928768097)
              ·
                refine ⟨253270263020687946576073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337693684027583928768097 253270263020687946576073)
                ·
                  refine ⟨189952697265515959932055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253270263020687946576073 189952697265515959932055)
                  ·
                    rfl

theorem cell20_416173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_416173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416173 prefixEnd_416173 := by exact prefixLift 416173
  have htrace : WordTrace (prefixWord ++ tailWord_416173) baseStart_416173 baseEnd_416173 := by
    simpa [prefixWord, tailWord_416173, baseEnd_416173] using wordTrace_append hprefix tailTrace_416173
  have hstable : (prefixWord ++ tailWord_416173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416173).length < 2 ^ (prefixWord ++ tailWord_416173).sum := by decide
  have hdescent : baseEnd_416173 < baseStart_416173 := by decide
  rcases family_descends (prefixWord ++ tailWord_416173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416177 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 2]
def baseStart_416177 : Nat := 118140960795 + 416177 * 2 ^ 59
def prefixEnd_416177 : Nat := 4983230072969 + 3 ^ 40 * 416177 * 2
def baseEnd_416177 : Nat := 189954522974509723798705

theorem tailTrace_416177 : CollatzResearch.WordTrace tailWord_416177 prefixEnd_416177 189954522974509723798705 := by
  unfold tailWord_416177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179222213269281217950785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10119481475512854145300523 15179222213269281217950785)
  ·
    refine ⟨11384416659951960913463089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179222213269281217950785 11384416659951960913463089)
    ·
      refine ⟨8538312494963970685097317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11384416659951960913463089 8538312494963970685097317)
      ·
        refine ⟨1600933592805744503455747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8538312494963970685097317 1600933592805744503455747)
        ·
          refine ⟨2401400389208616755183621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600933592805744503455747 2401400389208616755183621)
          ·
            refine ⟨450262572976615641596929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2401400389208616755183621 450262572976615641596929)
            ·
              refine ⟨337696929732461731197697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450262572976615641596929 337696929732461731197697)
              ·
                refine ⟨253272697299346298398273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337696929732461731197697 253272697299346298398273)
                ·
                  refine ⟨189954522974509723798705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253272697299346298398273 189954522974509723798705)
                  ·
                    rfl

theorem cell20_416177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_416177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416177 prefixEnd_416177 := by exact prefixLift 416177
  have htrace : WordTrace (prefixWord ++ tailWord_416177) baseStart_416177 baseEnd_416177 := by
    simpa [prefixWord, tailWord_416177, baseEnd_416177] using wordTrace_append hprefix tailTrace_416177
  have hstable : (prefixWord ++ tailWord_416177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416177).length < 2 ^ (prefixWord ++ tailWord_416177).sum := by decide
  have hdescent : baseEnd_416177 < baseStart_416177 := by decide
  rcases family_descends (prefixWord ++ tailWord_416177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416188 : List Nat := [2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_416188 : Nat := 118140960795 + 416188 * 2 ^ 59
def prefixEnd_416188 : Nat := 4983230072969 + 3 ^ 40 * 416188 * 2
def baseEnd_416188 : Nat := 63319847891414191477331

theorem tailTrace_416188 : CollatzResearch.WordTrace tailWord_416188 prefixEnd_416188 63319847891414191477331 := by
  unfold tailWord_416188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589811708114715048300609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10119748944152953397734145 7589811708114715048300609)
  ·
    refine ⟨5692358781086036286225457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7589811708114715048300609 5692358781086036286225457)
    ·
      refine ⟨4269269085814527214669093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692358781086036286225457 4269269085814527214669093)
      ·
        refine ⟨800487953590223852750455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4269269085814527214669093 800487953590223852750455)
        ·
          refine ⟨1200731930385335779125683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800487953590223852750455 1200731930385335779125683)
          ·
            refine ⟨1801097895578003668688525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200731930385335779125683 1801097895578003668688525)
            ·
              refine ⟨675411710841751375758197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1801097895578003668688525 675411710841751375758197)
              ·
                refine ⟨63319847891414191477331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675411710841751375758197 63319847891414191477331)
                ·
                  rfl

theorem cell20_416188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_416188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416188 prefixEnd_416188 := by exact prefixLift 416188
  have htrace : WordTrace (prefixWord ++ tailWord_416188) baseStart_416188 baseEnd_416188 := by
    simpa [prefixWord, tailWord_416188, baseEnd_416188] using wordTrace_append hprefix tailTrace_416188
  have hstable : (prefixWord ++ tailWord_416188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416188).length < 2 ^ (prefixWord ++ tailWord_416188).sum := by decide
  have hdescent : baseEnd_416188 < baseStart_416188 := by decide
  rcases family_descends (prefixWord ++ tailWord_416188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416202 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_416202 : Nat := 118140960795 + 416202 * 2 ^ 59
def prefixEnd_416202 : Nat := 4983230072969 + 3 ^ 40 * 416202 * 2
def baseEnd_416202 : Nat := 189965933655720747965269

theorem tailTrace_416202 : CollatzResearch.WordTrace tailWord_416202 prefixEnd_416202 189965933655720747965269 := by
  unfold tailWord_416202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795033509544677621902715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10120089358785806991740573 3795033509544677621902715)
  ·
    refine ⟨5692550264317016432854073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3795033509544677621902715 5692550264317016432854073)
    ·
      refine ⟨4269412698237762324640555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692550264317016432854073 4269412698237762324640555)
      ·
        refine ⟨6404119047356643486960833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269412698237762324640555 6404119047356643486960833)
        ·
          refine ⟨4803089285517482615220625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6404119047356643486960833 4803089285517482615220625)
          ·
            refine ⟨3602316964138111961415469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4803089285517482615220625 3602316964138111961415469)
            ·
              refine ⟨1350868861551791985530801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602316964138111961415469 1350868861551791985530801)
              ·
                refine ⟨1013151646163843989148101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350868861551791985530801 1013151646163843989148101)
                ·
                  refine ⟨189965933655720747965269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013151646163843989148101 189965933655720747965269)
                  ·
                    rfl

theorem cell20_416202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_416202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416202 prefixEnd_416202 := by exact prefixLift 416202
  have htrace : WordTrace (prefixWord ++ tailWord_416202) baseStart_416202 baseEnd_416202 := by
    simpa [prefixWord, tailWord_416202, baseEnd_416202] using wordTrace_append hprefix tailTrace_416202
  have hstable : (prefixWord ++ tailWord_416202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416202).length < 2 ^ (prefixWord ++ tailWord_416202).sum := by decide
  have hdescent : baseEnd_416202 < baseStart_416202 := by decide
  rcases family_descends (prefixWord ++ tailWord_416202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416216 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_416216 : Nat := 118140960795 + 416216 * 2 ^ 59
def prefixEnd_416216 : Nat := 4983230072969 + 3 ^ 40 * 416216 * 2
def baseEnd_416216 : Nat := 189972323637198921498545

theorem tailTrace_416216 : CollatzResearch.WordTrace tailWord_416216 prefixEnd_416216 189972323637198921498545 := by
  unfold tailWord_416216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7590322330063995439310251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10120429773418660585747001 7590322330063995439310251)
  ·
    refine ⟨11385483495095993158965377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7590322330063995439310251 11385483495095993158965377)
    ·
      refine ⟨8539112621321994869224033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11385483495095993158965377 8539112621321994869224033)
      ·
        refine ⟨6404334465991496151918025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539112621321994869224033 6404334465991496151918025)
        ·
          refine ⟨4803250849493622113938519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6404334465991496151918025 4803250849493622113938519)
          ·
            refine ⟨7204876274240433170907779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803250849493622113938519 7204876274240433170907779)
            ·
              refine ⟨10807314411360649756361669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204876274240433170907779 10807314411360649756361669)
              ·
                refine ⟨2026371452130121829317813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10807314411360649756361669 2026371452130121829317813)
                ·
                  refine ⟨189972323637198921498545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026371452130121829317813 189972323637198921498545)
                  ·
                    rfl

theorem cell20_416216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_416216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416216 prefixEnd_416216 := by exact prefixLift 416216
  have htrace : WordTrace (prefixWord ++ tailWord_416216) baseStart_416216 baseEnd_416216 := by
    simpa [prefixWord, tailWord_416216, baseEnd_416216] using wordTrace_append hprefix tailTrace_416216
  have hstable : (prefixWord ++ tailWord_416216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416216).length < 2 ^ (prefixWord ++ tailWord_416216).sum := by decide
  have hdescent : baseEnd_416216 < baseStart_416216 := by decide
  rcases family_descends (prefixWord ++ tailWord_416216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416229 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_416229 : Nat := 118140960795 + 416229 * 2 ^ 59
def prefixEnd_416229 : Nat := 4983230072969 + 3 ^ 40 * 416229 * 2
def baseEnd_416229 : Nat := 189978257191428654065159

theorem tailTrace_416229 : CollatzResearch.WordTrace tailWord_416229 prefixEnd_416229 189978257191428654065159 := by
  unfold tailWord_416229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181118809080894098843741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10120745872720596065895827 15181118809080894098843741)
  ·
    refine ⟨5692919553405335287066403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15181118809080894098843741 5692919553405335287066403)
    ·
      refine ⟨8539379330108002930599605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692919553405335287066403 8539379330108002930599605)
      ·
        refine ⟨800566812197625274743713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8539379330108002930599605 800566812197625274743713)
        ·
          refine ⟨600425109148218956057785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800566812197625274743713 600425109148218956057785)
          ·
            refine ⟨450318831861164217043339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600425109148218956057785 450318831861164217043339)
            ·
              refine ⟨675478247791746325565009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450318831861164217043339 675478247791746325565009)
              ·
                refine ⟨506608685843809744173757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675478247791746325565009 506608685843809744173757)
                ·
                  refine ⟨189978257191428654065159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506608685843809744173757 189978257191428654065159)
                  ·
                    rfl

theorem cell20_416229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_416229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416229 prefixEnd_416229 := by exact prefixLift 416229
  have htrace : WordTrace (prefixWord ++ tailWord_416229) baseStart_416229 baseEnd_416229 := by
    simpa [prefixWord, tailWord_416229, baseEnd_416229] using wordTrace_append hprefix tailTrace_416229
  have hstable : (prefixWord ++ tailWord_416229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416229).length < 2 ^ (prefixWord ++ tailWord_416229).sum := by decide
  have hdescent : baseEnd_416229 < baseStart_416229 := by decide
  rcases family_descends (prefixWord ++ tailWord_416229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416240 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_416240 : Nat := 118140960795 + 416240 * 2 ^ 59
def prefixEnd_416240 : Nat := 4983230072969 + 3 ^ 40 * 416240 * 2
def baseEnd_416240 : Nat := 189983277891161504698447

theorem tailTrace_416240 : CollatzResearch.WordTrace tailWord_416240 prefixEnd_416240 189983277891161504698447 := by
  unfold tailWord_416240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7590760006020521488747087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10121013341360695318329449 7590760006020521488747087)
  ·
    refine ⟨11386140009030782233120631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7590760006020521488747087 11386140009030782233120631)
    ·
      refine ⟨17079210013546173349680947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11386140009030782233120631 17079210013546173349680947)
      ·
        refine ⟨25618815020319260024521421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17079210013546173349680947 25618815020319260024521421)
        ·
          refine ⟨9607055632619722509195533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25618815020319260024521421 9607055632619722509195533)
          ·
            refine ⟨3602645862232395940948325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9607055632619722509195533 3602645862232395940948325)
            ·
              refine ⟨675496099168574238927811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3602645862232395940948325 675496099168574238927811)
              ·
                refine ⟨1013244148752861358391717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675496099168574238927811 1013244148752861358391717)
                ·
                  refine ⟨189983277891161504698447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013244148752861358391717 189983277891161504698447)
                  ·
                    rfl

theorem cell20_416240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_416240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416240 prefixEnd_416240 := by exact prefixLift 416240
  have htrace : WordTrace (prefixWord ++ tailWord_416240) baseStart_416240 baseEnd_416240 := by
    simpa [prefixWord, tailWord_416240, baseEnd_416240] using wordTrace_append hprefix tailTrace_416240
  have hstable : (prefixWord ++ tailWord_416240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416240).length < 2 ^ (prefixWord ++ tailWord_416240).sum := by decide
  have hdescent : baseEnd_416240 < baseStart_416240 := by decide
  rcases family_descends (prefixWord ++ tailWord_416240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416285 : List Nat := [1, 4, 2, 2, 1, 2, 8]
def baseStart_416285 : Nat := 118140960795 + 416285 * 2 ^ 59
def prefixEnd_416285 : Nat := 4983230072969 + 3 ^ 40 * 416285 * 2
def baseEnd_416285 : Nat := 21111535235260149799807

theorem tailTrace_416285 : CollatzResearch.WordTrace tailWord_416285 prefixEnd_416285 21111535235260149799807 := by
  unfold tailWord_416285
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183161296878015662882309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10122107531252010441921539 15183161296878015662882309)
  ·
    refine ⟨2846842743164627936790433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15183161296878015662882309 2846842743164627936790433)
    ·
      refine ⟨2135132057373470952592825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2846842743164627936790433 2135132057373470952592825)
      ·
        refine ⟨1601349043030103214444619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135132057373470952592825 1601349043030103214444619)
        ·
          refine ⟨2402023564545154821666929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601349043030103214444619 2402023564545154821666929)
          ·
            refine ⟨1801517673408866116250197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402023564545154821666929 1801517673408866116250197)
            ·
              refine ⟨21111535235260149799807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1801517673408866116250197 21111535235260149799807)
              ·
                rfl

theorem cell20_416285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_416285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416285 prefixEnd_416285 := by exact prefixLift 416285
  have htrace : WordTrace (prefixWord ++ tailWord_416285) baseStart_416285 baseEnd_416285 := by
    simpa [prefixWord, tailWord_416285, baseEnd_416285] using wordTrace_append hprefix tailTrace_416285
  have hstable : (prefixWord ++ tailWord_416285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416285).length < 2 ^ (prefixWord ++ tailWord_416285).sum := by decide
  have hdescent : baseEnd_416285 < baseStart_416285 := by decide
  rcases family_descends (prefixWord ++ tailWord_416285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416309 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_416309 : Nat := 118140960795 + 416309 * 2 ^ 59
def prefixEnd_416309 : Nat := 4983230072969 + 3 ^ 40 * 416309 * 2
def baseEnd_416309 : Nat := 190014771371303931398165

theorem tailTrace_416309 : CollatzResearch.WordTrace tailWord_416309 prefixEnd_416309 190014771371303931398165 := by
  unfold tailWord_416309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15184036648791067761755981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10122691099194045174503987 15184036648791067761755981)
  ·
    refine ⟨5694013743296650410658493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15184036648791067761755981 5694013743296650410658493)
    ·
      refine ⟨2135255153736243903996935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5694013743296650410658493 2135255153736243903996935)
      ·
        refine ⟨3202882730604365855995403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135255153736243903996935 3202882730604365855995403)
        ·
          refine ⟨4804324095906548783993105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202882730604365855995403 4804324095906548783993105)
          ·
            refine ⟨3603243071929911587994829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804324095906548783993105 3603243071929911587994829)
            ·
              refine ⟨1351216151973716845498061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3603243071929911587994829 1351216151973716845498061)
              ·
                refine ⟨506706056990143817061773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1351216151973716845498061 506706056990143817061773)
                ·
                  refine ⟨190014771371303931398165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506706056990143817061773 190014771371303931398165)
                  ·
                    rfl

theorem cell20_416309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_416309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416309 prefixEnd_416309 := by exact prefixLift 416309
  have htrace : WordTrace (prefixWord ++ tailWord_416309) baseStart_416309 baseEnd_416309 := by
    simpa [prefixWord, tailWord_416309, baseEnd_416309] using wordTrace_append hprefix tailTrace_416309
  have hstable : (prefixWord ++ tailWord_416309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416309).length < 2 ^ (prefixWord ++ tailWord_416309).sum := by decide
  have hdescent : baseEnd_416309 < baseStart_416309 := by decide
  rcases family_descends (prefixWord ++ tailWord_416309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416357 : List Nat := [1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_416357 : Nat := 118140960795 + 416357 * 2 ^ 59
def prefixEnd_416357 : Nat := 4983230072969 + 3 ^ 40 * 416357 * 2
def baseEnd_416357 : Nat := 63345559959743032599323

theorem tailTrace_416357 : CollatzResearch.WordTrace tailWord_416357 prefixEnd_416357 63345559959743032599323 := by
  unfold tailWord_416357
  simp only [CollatzResearch.WordTrace]
  refine ⟨15185787352617171959503325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10123858235078114639668883 15185787352617171959503325)
  ·
    refine ⟨5694670257231439484813747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15185787352617171959503325 5694670257231439484813747)
    ·
      refine ⟨8542005385847159227220621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694670257231439484813747 8542005385847159227220621)
      ·
        refine ⟨3203252019692684710207733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8542005385847159227220621 3203252019692684710207733)
        ·
          refine ⟨300304876846189191581975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3203252019692684710207733 300304876846189191581975)
          ·
            refine ⟨450457315269283787372963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300304876846189191581975 450457315269283787372963)
            ·
              refine ⟨675685972903925681059445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450457315269283787372963 675685972903925681059445)
              ·
                refine ⟨63345559959743032599323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675685972903925681059445 63345559959743032599323)
                ·
                  rfl

theorem cell20_416357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_416357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416357 prefixEnd_416357 := by exact prefixLift 416357
  have htrace : WordTrace (prefixWord ++ tailWord_416357) baseStart_416357 baseEnd_416357 := by
    simpa [prefixWord, tailWord_416357, baseEnd_416357] using wordTrace_append hprefix tailTrace_416357
  have hstable : (prefixWord ++ tailWord_416357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416357).length < 2 ^ (prefixWord ++ tailWord_416357).sum := by decide
  have hdescent : baseEnd_416357 < baseStart_416357 := by decide
  rcases family_descends (prefixWord ++ tailWord_416357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416375 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_416375 : Nat := 118140960795 + 416375 * 2 ^ 59
def prefixEnd_416375 : Nat := 4983230072969 + 3 ^ 40 * 416375 * 2
def baseEnd_416375 : Nat := 190044895569701035197895

theorem tailTrace_416375 : CollatzResearch.WordTrace tailWord_416375 prefixEnd_416375 190044895569701035197895 := by
  unfold tailWord_416375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186443866551961033658579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10124295911034640689105719 15186443866551961033658579)
  ·
    refine ⟨22779665799827941550487869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186443866551961033658579 22779665799827941550487869)
    ·
      refine ⟨8542374674935478081432951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22779665799827941550487869 8542374674935478081432951)
      ·
        refine ⟨12813562012403217122149427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542374674935478081432951 12813562012403217122149427)
        ·
          refine ⟨19220343018604825683224141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12813562012403217122149427 19220343018604825683224141)
          ·
            refine ⟨7207628631976809631209053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19220343018604825683224141 7207628631976809631209053)
            ·
              refine ⟨2702860736991303611703395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7207628631976809631209053 2702860736991303611703395)
              ·
                refine ⟨4054291105486955417555093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702860736991303611703395 4054291105486955417555093)
                ·
                  refine ⟨190044895569701035197895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4054291105486955417555093 190044895569701035197895)
                  ·
                    rfl

theorem cell20_416375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_416375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416375 prefixEnd_416375 := by exact prefixLift 416375
  have htrace : WordTrace (prefixWord ++ tailWord_416375) baseStart_416375 baseEnd_416375 := by
    simpa [prefixWord, tailWord_416375, baseEnd_416375] using wordTrace_append hprefix tailTrace_416375
  have hstable : (prefixWord ++ tailWord_416375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416375).length < 2 ^ (prefixWord ++ tailWord_416375).sum := by decide
  have hdescent : baseEnd_416375 < baseStart_416375 := by decide
  rcases family_descends (prefixWord ++ tailWord_416375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416388 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_416388 : Nat := 118140960795 + 416388 * 2 ^ 59
def prefixEnd_416388 : Nat := 4983230072969 + 3 ^ 40 * 416388 * 2
def baseEnd_416388 : Nat := 190050829123930767764509

theorem tailTrace_416388 : CollatzResearch.WordTrace tailWord_416388 prefixEnd_416388 190050829123930767764509 := by
  unfold tailWord_416388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593459007752432126940909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10124612010336576169254545 7593459007752432126940909)
  ·
    refine ⟨2847547127907162047602841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7593459007752432126940909 2847547127907162047602841)
    ·
      refine ⟨2135660345930371535702131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2847547127907162047602841 2135660345930371535702131)
      ·
        refine ⟨3203490518895557303553197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135660345930371535702131 3203490518895557303553197)
        ·
          refine ⟨1201308944585833988832449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3203490518895557303553197 1201308944585833988832449)
          ·
            refine ⟨900981708439375491624337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201308944585833988832449 900981708439375491624337)
            ·
              refine ⟨675736281329531618718253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900981708439375491624337 675736281329531618718253)
              ·
                refine ⟨253401105498574357019345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675736281329531618718253 253401105498574357019345)
                ·
                  refine ⟨190050829123930767764509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253401105498574357019345 190050829123930767764509)
                  ·
                    rfl

theorem cell20_416388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_416388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416388 prefixEnd_416388 := by exact prefixLift 416388
  have htrace : WordTrace (prefixWord ++ tailWord_416388) baseStart_416388 baseEnd_416388 := by
    simpa [prefixWord, tailWord_416388, baseEnd_416388] using wordTrace_append hprefix tailTrace_416388
  have hstable : (prefixWord ++ tailWord_416388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416388).length < 2 ^ (prefixWord ++ tailWord_416388).sum := by decide
  have hdescent : baseEnd_416388 < baseStart_416388 := by decide
  rcases family_descends (prefixWord ++ tailWord_416388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416402 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_416402 : Nat := 118140960795 + 416402 * 2 ^ 59
def prefixEnd_416402 : Nat := 4983230072969 + 3 ^ 40 * 416402 * 2
def baseEnd_416402 : Nat := 190057219105408941297785

theorem tailTrace_416402 : CollatzResearch.WordTrace tailWord_416402 prefixEnd_416402 190057219105408941297785 := by
  unfold tailWord_416402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796857159363536161222865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10124952424969429763260973 3796857159363536161222865)
  ·
    refine ⟨2847642869522652120917149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3796857159363536161222865 2847642869522652120917149)
    ·
      refine ⟨1067866076070994545343931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2847642869522652120917149 1067866076070994545343931)
      ·
        refine ⟨1601799114106491818015897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067866076070994545343931 1601799114106491818015897)
        ·
          refine ⟨1201349335579868863511923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1601799114106491818015897 1201349335579868863511923)
          ·
            refine ⟨1802024003369803295267885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201349335579868863511923 1802024003369803295267885)
            ·
              refine ⟨675759001263676235725457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1802024003369803295267885 675759001263676235725457)
              ·
                refine ⟨506819250947757176794093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675759001263676235725457 506819250947757176794093)
                ·
                  refine ⟨190057219105408941297785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506819250947757176794093 190057219105408941297785)
                  ·
                    rfl

theorem cell20_416402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_416402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416402 prefixEnd_416402 := by exact prefixLift 416402
  have htrace : WordTrace (prefixWord ++ tailWord_416402) baseStart_416402 baseEnd_416402 := by
    simpa [prefixWord, tailWord_416402, baseEnd_416402] using wordTrace_append hprefix tailTrace_416402
  have hstable : (prefixWord ++ tailWord_416402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416402).length < 2 ^ (prefixWord ++ tailWord_416402).sum := by decide
  have hdescent : baseEnd_416402 < baseStart_416402 := by decide
  rcases family_descends (prefixWord ++ tailWord_416402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416444 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_416444 : Nat := 118140960795 + 416444 * 2 ^ 59
def prefixEnd_416444 : Nat := 4983230072969 + 3 ^ 40 * 416444 * 2
def baseEnd_416444 : Nat := 190076389049843461897613

theorem tailTrace_416444 : CollatzResearch.WordTrace tailWord_416444 prefixEnd_416444 190076389049843461897613 := by
  unfold tailWord_416444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594480251650992908960193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10125973668867990545280257 7594480251650992908960193)
  ·
    refine ⟨5695860188738244681720145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7594480251650992908960193 5695860188738244681720145)
    ·
      refine ⟨4271895141553683511290109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695860188738244681720145 4271895141553683511290109)
      ·
        refine ⟨1601960678082631316733791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4271895141553683511290109 1601960678082631316733791)
        ·
          refine ⟨2402941017123946975100687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601960678082631316733791 2402941017123946975100687)
          ·
            refine ⟨3604411525685920462651031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402941017123946975100687 3604411525685920462651031)
            ·
              refine ⟨5406617288528880693976547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604411525685920462651031 5406617288528880693976547)
              ·
                refine ⟨8109925932793321040964821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406617288528880693976547 8109925932793321040964821)
                ·
                  refine ⟨190076389049843461897613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8109925932793321040964821 190076389049843461897613)
                  ·
                    rfl

theorem cell20_416444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_416444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416444 prefixEnd_416444 := by exact prefixLift 416444
  have htrace : WordTrace (prefixWord ++ tailWord_416444) baseStart_416444 baseEnd_416444 := by
    simpa [prefixWord, tailWord_416444, baseEnd_416444] using wordTrace_append hprefix tailTrace_416444
  have hstable : (prefixWord ++ tailWord_416444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416444).length < 2 ^ (prefixWord ++ tailWord_416444).sum := by decide
  have hdescent : baseEnd_416444 < baseStart_416444 := by decide
  rcases family_descends (prefixWord ++ tailWord_416444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416447 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 2]
def baseStart_416447 : Nat := 118140960795 + 416447 * 2 ^ 59
def prefixEnd_416447 : Nat := 4983230072969 + 3 ^ 40 * 416447 * 2
def baseEnd_416447 : Nat := 190077758331588784797601

theorem tailTrace_416447 : CollatzResearch.WordTrace tailWord_416447 prefixEnd_416447 190077758331588784797601 := by
  unfold tailWord_416447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15189069922291117330279595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10126046614860744886853063 15189069922291117330279595)
  ·
    refine ⟨22783604883436675995419393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15189069922291117330279595 22783604883436675995419393)
    ·
      refine ⟨17087703662577506996564545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22783604883436675995419393 17087703662577506996564545)
      ·
        refine ⟨12815777746933130247423409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17087703662577506996564545 12815777746933130247423409)
        ·
          refine ⟨9611833310199847685567557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815777746933130247423409 9611833310199847685567557)
          ·
            refine ⟨1802218745662471441043917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9611833310199847685567557 1802218745662471441043917)
            ·
              refine ⟨675832029623426790391469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1802218745662471441043917 675832029623426790391469)
              ·
                refine ⟨253437011108785046396801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675832029623426790391469 253437011108785046396801)
                ·
                  refine ⟨190077758331588784797601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253437011108785046396801 190077758331588784797601)
                  ·
                    rfl

theorem cell20_416447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 2].length) (baseStart_416447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416447 prefixEnd_416447 := by exact prefixLift 416447
  have htrace : WordTrace (prefixWord ++ tailWord_416447) baseStart_416447 baseEnd_416447 := by
    simpa [prefixWord, tailWord_416447, baseEnd_416447] using wordTrace_append hprefix tailTrace_416447
  have hstable : (prefixWord ++ tailWord_416447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416447).length < 2 ^ (prefixWord ++ tailWord_416447).sum := by decide
  have hdescent : baseEnd_416447 < baseStart_416447 := by decide
  rcases family_descends (prefixWord ++ tailWord_416447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416489 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_416489 : Nat := 118140960795 + 416489 * 2 ^ 59
def prefixEnd_416489 : Nat := 4983230072969 + 3 ^ 40 * 416489 * 2
def baseEnd_416489 : Nat := 190096928276023305397429

theorem tailTrace_416489 : CollatzResearch.WordTrace tailWord_416489 prefixEnd_416489 190096928276023305397429 := by
  unfold tailWord_416489
  simp only [CollatzResearch.WordTrace]
  refine ⟨15190601788138958503308521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10127067858759305668872347 15190601788138958503308521)
  ·
    refine ⟨11392951341104218877481391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15190601788138958503308521 11392951341104218877481391)
    ·
      refine ⟨17089427011656328316222087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392951341104218877481391 17089427011656328316222087)
      ·
        refine ⟨25634140517484492474333131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089427011656328316222087 25634140517484492474333131)
        ·
          refine ⟨38451210776226738711499697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25634140517484492474333131 38451210776226738711499697)
          ·
            refine ⟨28838408082170054033624773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38451210776226738711499697 28838408082170054033624773)
            ·
              refine ⟨5407201515406885131304645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28838408082170054033624773 5407201515406885131304645)
              ·
                refine ⟨1013850284138790962119621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5407201515406885131304645 1013850284138790962119621)
                ·
                  refine ⟨190096928276023305397429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013850284138790962119621 190096928276023305397429)
                  ·
                    rfl

theorem cell20_416489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_416489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416489 prefixEnd_416489 := by exact prefixLift 416489
  have htrace : WordTrace (prefixWord ++ tailWord_416489) baseStart_416489 baseEnd_416489 := by
    simpa [prefixWord, tailWord_416489, baseEnd_416489] using wordTrace_append hprefix tailTrace_416489
  have hstable : (prefixWord ++ tailWord_416489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416489).length < 2 ^ (prefixWord ++ tailWord_416489).sum := by decide
  have hdescent : baseEnd_416489 < baseStart_416489 := by decide
  rcases family_descends (prefixWord ++ tailWord_416489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416496 : List Nat := [2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_416496 : Nat := 118140960795 + 416496 * 2 ^ 59
def prefixEnd_416496 : Nat := 4983230072969 + 3 ^ 40 * 416496 * 2
def baseEnd_416496 : Nat := 63366707755587464054689

theorem tailTrace_416496 : CollatzResearch.WordTrace tailWord_416496 prefixEnd_416496 63366707755587464054689 := by
  unfold tailWord_416496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595428549556799349406671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10127238066075732465875561 7595428549556799349406671)
  ·
    refine ⟨11393142824335199024110007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7595428549556799349406671 11393142824335199024110007)
    ·
      refine ⟨17089714236502798536165011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393142824335199024110007 17089714236502798536165011)
      ·
        refine ⟨25634571354754197804247517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089714236502798536165011 25634571354754197804247517)
        ·
          refine ⟨9612964258032824176592819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25634571354754197804247517 9612964258032824176592819)
          ·
            refine ⟨14419446387049236264889229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612964258032824176592819 14419446387049236264889229)
            ·
              refine ⟨5407292395143463599333461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14419446387049236264889229 5407292395143463599333461)
              ·
                refine ⟨63366707755587464054689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5407292395143463599333461 63366707755587464054689)
                ·
                  rfl

theorem cell20_416496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_416496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416496 prefixEnd_416496 := by exact prefixLift 416496
  have htrace : WordTrace (prefixWord ++ tailWord_416496) baseStart_416496 baseEnd_416496 := by
    simpa [prefixWord, tailWord_416496, baseEnd_416496] using wordTrace_append hprefix tailTrace_416496
  have hstable : (prefixWord ++ tailWord_416496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416496).length < 2 ^ (prefixWord ++ tailWord_416496).sum := by decide
  have hdescent : baseEnd_416496 < baseStart_416496 := by decide
  rcases family_descends (prefixWord ++ tailWord_416496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416519 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 2]
def baseStart_416519 : Nat := 118140960795 + 416519 * 2 ^ 59
def prefixEnd_416519 : Nat := 4983230072969 + 3 ^ 40 * 416519 * 2
def baseEnd_416519 : Nat := 190110621093476534397307

theorem tailTrace_416519 : CollatzResearch.WordTrace tailWord_416519 prefixEnd_416519 190110621093476534397307 := by
  unfold tailWord_416519
  simp only [CollatzResearch.WordTrace]
  refine ⟨15191695978030273626900611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10127797318686849084600407 15191695978030273626900611)
  ·
    refine ⟨22787543967045410440350917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15191695978030273626900611 22787543967045410440350917)
    ·
      refine ⟨4272664493821014457565797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22787543967045410440350917 4272664493821014457565797)
      ·
        refine ⟨801124592591440210793587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4272664493821014457565797 801124592591440210793587)
        ·
          refine ⟨1201686888887160316190381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801124592591440210793587 1201686888887160316190381)
          ·
            refine ⟨450632583332685118571393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201686888887160316190381 450632583332685118571393)
            ·
              refine ⟨337974437499513838928545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450632583332685118571393 337974437499513838928545)
              ·
                refine ⟨253480828124635379196409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337974437499513838928545 253480828124635379196409)
                ·
                  refine ⟨190110621093476534397307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253480828124635379196409 190110621093476534397307)
                  ·
                    rfl

theorem cell20_416519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2].length) (baseStart_416519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416519 prefixEnd_416519 := by exact prefixLift 416519
  have htrace : WordTrace (prefixWord ++ tailWord_416519) baseStart_416519 baseEnd_416519 := by
    simpa [prefixWord, tailWord_416519, baseEnd_416519] using wordTrace_append hprefix tailTrace_416519
  have hstable : (prefixWord ++ tailWord_416519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416519).length < 2 ^ (prefixWord ++ tailWord_416519).sum := by decide
  have hdescent : baseEnd_416519 < baseStart_416519 := by decide
  rcases family_descends (prefixWord ++ tailWord_416519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416527 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_416527 : Nat := 118140960795 + 416527 * 2 ^ 59
def prefixEnd_416527 : Nat := 4983230072969 + 3 ^ 40 * 416527 * 2
def baseEnd_416527 : Nat := 190114272511464062130607

theorem tailTrace_416527 : CollatzResearch.WordTrace tailWord_416527 prefixEnd_416527 190114272511464062130607 := by
  unfold tailWord_416527
  simp only [CollatzResearch.WordTrace]
  refine ⟨15191987762001290993191835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10127991841334193995461223 15191987762001290993191835)
  ·
    refine ⟨22787981643001936489787753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15191987762001290993191835 22787981643001936489787753)
    ·
      refine ⟨17090986232251452367340815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22787981643001936489787753 17090986232251452367340815)
      ·
        refine ⟨25636479348377178551011223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090986232251452367340815 25636479348377178551011223)
        ·
          refine ⟨38454719022565767826516835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25636479348377178551011223 38454719022565767826516835)
          ·
            refine ⟨57682078533848651739775253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38454719022565767826516835 57682078533848651739775253)
            ·
              refine ⟨2703847431274155550301965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57682078533848651739775253 2703847431274155550301965)
              ·
                refine ⟨1013942786727808331363237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703847431274155550301965 1013942786727808331363237)
                ·
                  refine ⟨190114272511464062130607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013942786727808331363237 190114272511464062130607)
                  ·
                    rfl

theorem cell20_416527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_416527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416527 prefixEnd_416527 := by exact prefixLift 416527
  have htrace : WordTrace (prefixWord ++ tailWord_416527) baseStart_416527 baseEnd_416527 := by
    simpa [prefixWord, tailWord_416527, baseEnd_416527] using wordTrace_append hprefix tailTrace_416527
  have hstable : (prefixWord ++ tailWord_416527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416527).length < 2 ^ (prefixWord ++ tailWord_416527).sum := by decide
  have hdescent : baseEnd_416527 < baseStart_416527 := by decide
  rcases family_descends (prefixWord ++ tailWord_416527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416544 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_416544 : Nat := 118140960795 + 416544 * 2 ^ 59
def prefixEnd_416544 : Nat := 4983230072969 + 3 ^ 40 * 416544 * 2
def baseEnd_416544 : Nat := 190122031774687558563871

theorem tailTrace_416544 : CollatzResearch.WordTrace tailWord_416544 prefixEnd_416544 190122031774687558563871 := by
  unfold tailWord_416544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596303901469851448280343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10128405201959801931040457 7596303901469851448280343)
  ·
    refine ⟨11394455852204777172420515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596303901469851448280343 11394455852204777172420515)
    ·
      refine ⟨17091683778307165758630773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11394455852204777172420515 17091683778307165758630773)
      ·
        refine ⟨1602345354216296789871635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17091683778307165758630773 1602345354216296789871635)
        ·
          refine ⟨2403518031324445184807453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602345354216296789871635 2403518031324445184807453)
          ·
            refine ⟨901319261746666944302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2403518031324445184807453 901319261746666944302795)
            ·
              refine ⟨1351978892620000416454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901319261746666944302795 1351978892620000416454193)
              ·
                refine ⟨1013984169465000312340645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351978892620000416454193 1013984169465000312340645)
                ·
                  refine ⟨190122031774687558563871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013984169465000312340645 190122031774687558563871)
                  ·
                    rfl

theorem cell20_416544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_416544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416544 prefixEnd_416544 := by exact prefixLift 416544
  have htrace : WordTrace (prefixWord ++ tailWord_416544) baseStart_416544 baseEnd_416544 := by
    simpa [prefixWord, tailWord_416544, baseEnd_416544] using wordTrace_append hprefix tailTrace_416544
  have hstable : (prefixWord ++ tailWord_416544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416544).length < 2 ^ (prefixWord ++ tailWord_416544).sum := by decide
  have hdescent : baseEnd_416544 < baseStart_416544 := by decide
  rcases family_descends (prefixWord ++ tailWord_416544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416561 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 2]
def baseStart_416561 : Nat := 118140960795 + 416561 * 2 ^ 59
def prefixEnd_416561 : Nat := 4983230072969 + 3 ^ 40 * 416561 * 2
def baseEnd_416561 : Nat := 190129791037911054997135

theorem tailTrace_416561 : CollatzResearch.WordTrace tailWord_416561 prefixEnd_416561 190129791037911054997135 := by
  unfold tailWord_416561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193227843878114799929537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10128818562585409866619691 15193227843878114799929537)
  ·
    refine ⟨11394920882908586099947153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15193227843878114799929537 11394920882908586099947153)
    ·
      refine ⟨8546190662181439574960365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11394920882908586099947153 8546190662181439574960365)
      ·
        refine ⟨3204821498318039840610137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8546190662181439574960365 3204821498318039840610137)
        ·
          refine ⟨2403616123738529880457603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204821498318039840610137 2403616123738529880457603)
          ·
            refine ⟨3605424185607794820686405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403616123738529880457603 3605424185607794820686405)
            ·
              refine ⟨676017034801461528878701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3605424185607794820686405 676017034801461528878701)
              ·
                refine ⟨253506388050548073329513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676017034801461528878701 253506388050548073329513)
                ·
                  refine ⟨190129791037911054997135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253506388050548073329513 190129791037911054997135)
                  ·
                    rfl

theorem cell20_416561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_416561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416561 prefixEnd_416561 := by exact prefixLift 416561
  have htrace : WordTrace (prefixWord ++ tailWord_416561) baseStart_416561 baseEnd_416561 := by
    simpa [prefixWord, tailWord_416561, baseEnd_416561] using wordTrace_append hprefix tailTrace_416561
  have hstable : (prefixWord ++ tailWord_416561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416561).length < 2 ^ (prefixWord ++ tailWord_416561).sum := by decide
  have hdescent : baseEnd_416561 < baseStart_416561 := by decide
  rcases family_descends (prefixWord ++ tailWord_416561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416575 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_416575 : Nat := 118140960795 + 416575 * 2 ^ 59
def prefixEnd_416575 : Nat := 4983230072969 + 3 ^ 40 * 416575 * 2
def baseEnd_416575 : Nat := 190136181019389228530411

theorem tailTrace_416575 : CollatzResearch.WordTrace tailWord_416575 prefixEnd_416575 190136181019389228530411 := by
  unfold tailWord_416575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193738465827395190939179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10129158977218263460626119 15193738465827395190939179)
  ·
    refine ⟨22790607698741092786408769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193738465827395190939179 22790607698741092786408769)
    ·
      refine ⟨17092955774055819589806577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22790607698741092786408769 17092955774055819589806577)
      ·
        refine ⟨12819716830541864692354933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17092955774055819589806577 12819716830541864692354933)
        ·
          refine ⟨1201848452863299814908275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12819716830541864692354933 1201848452863299814908275)
          ·
            refine ⟨1802772679294949722362413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201848452863299814908275 1802772679294949722362413)
            ·
              refine ⟨676039754735606145885905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1802772679294949722362413 676039754735606145885905)
              ·
                refine ⟨507029816051704609414429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676039754735606145885905 507029816051704609414429)
                ·
                  refine ⟨190136181019389228530411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507029816051704609414429 190136181019389228530411)
                  ·
                    rfl

theorem cell20_416575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_416575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416575 prefixEnd_416575 := by exact prefixLift 416575
  have htrace : WordTrace (prefixWord ++ tailWord_416575) baseStart_416575 baseEnd_416575 := by
    simpa [prefixWord, tailWord_416575, baseEnd_416575] using wordTrace_append hprefix tailTrace_416575
  have hstable : (prefixWord ++ tailWord_416575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416575).length < 2 ^ (prefixWord ++ tailWord_416575).sum := by decide
  have hdescent : baseEnd_416575 < baseStart_416575 := by decide
  rcases family_descends (prefixWord ++ tailWord_416575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416616 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_416616 : Nat := 118140960795 + 416616 * 2 ^ 59
def prefixEnd_416616 : Nat := 4983230072969 + 3 ^ 40 * 416616 * 2
def baseEnd_416616 : Nat := 190154894536575308163577

theorem tailTrace_416616 : CollatzResearch.WordTrace tailWord_416616 prefixEnd_416616 190154894536575308163577 := by
  unfold tailWord_416616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597616929339429596590851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10130155905785906128787801 7597616929339429596590851)
  ·
    refine ⟨11396425394009144394886277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597616929339429596590851 11396425394009144394886277)
    ·
      refine ⟨2136829761376714574041177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11396425394009144394886277 2136829761376714574041177)
      ·
        refine ⟨1602622321032535930530883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2136829761376714574041177 1602622321032535930530883)
        ·
          refine ⟨2403933481548803895796325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602622321032535930530883 2403933481548803895796325)
          ·
            refine ⟨450737527790400730461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2403933481548803895796325 450737527790400730461811)
            ·
              refine ⟨676106291685601095692717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450737527790400730461811 676106291685601095692717)
              ·
                refine ⟨253539859382100410884769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676106291685601095692717 253539859382100410884769)
                ·
                  refine ⟨190154894536575308163577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253539859382100410884769 190154894536575308163577)
                  ·
                    rfl

theorem cell20_416616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_416616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416616 prefixEnd_416616 := by exact prefixLift 416616
  have htrace : WordTrace (prefixWord ++ tailWord_416616) baseStart_416616 baseEnd_416616 := by
    simpa [prefixWord, tailWord_416616, baseEnd_416616] using wordTrace_append hprefix tailTrace_416616
  have hstable : (prefixWord ++ tailWord_416616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416616).length < 2 ^ (prefixWord ++ tailWord_416616).sum := by decide
  have hdescent : baseEnd_416616 < baseStart_416616 := by decide
  rcases family_descends (prefixWord ++ tailWord_416616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416634 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_416634 : Nat := 118140960795 + 416634 * 2 ^ 59
def prefixEnd_416634 : Nat := 4983230072969 + 3 ^ 40 * 416634 * 2
def baseEnd_416634 : Nat := 190163110227047245563503

theorem tailTrace_416634 : CollatzResearch.WordTrace tailWord_416634 prefixEnd_416634 190163110227047245563503 := by
  unfold tailWord_416634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798972593153412066834239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10130593581742432178224637 3798972593153412066834239)
  ·
    refine ⟨5698458889730118100251359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798972593153412066834239 5698458889730118100251359)
    ·
      refine ⟨8547688334595177150377039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698458889730118100251359 8547688334595177150377039)
      ·
        refine ⟨12821532501892765725565559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547688334595177150377039 12821532501892765725565559)
        ·
          refine ⟨19232298752839148588348339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821532501892765725565559 19232298752839148588348339)
          ·
            refine ⟨28848448129258722882522509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19232298752839148588348339 28848448129258722882522509)
            ·
              refine ⟨10818168048472021080945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28848448129258722882522509 10818168048472021080945941)
              ·
                refine ⟨507101627272125988169341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10818168048472021080945941 507101627272125988169341)
                ·
                  refine ⟨190163110227047245563503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507101627272125988169341 190163110227047245563503)
                  ·
                    rfl

theorem cell20_416634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_416634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416634 prefixEnd_416634 := by exact prefixLift 416634
  have htrace : WordTrace (prefixWord ++ tailWord_416634) baseStart_416634 baseEnd_416634 := by
    simpa [prefixWord, tailWord_416634, baseEnd_416634] using wordTrace_append hprefix tailTrace_416634
  have hstable : (prefixWord ++ tailWord_416634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416634).length < 2 ^ (prefixWord ++ tailWord_416634).sum := by decide
  have hdescent : baseEnd_416634 < baseStart_416634 := by decide
  rcases family_descends (prefixWord ++ tailWord_416634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416651 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_416651 : Nat := 118140960795 + 416651 * 2 ^ 59
def prefixEnd_416651 : Nat := 4983230072969 + 3 ^ 40 * 416651 * 2
def baseEnd_416651 : Nat := 190170869490270741996767

theorem tailTrace_416651 : CollatzResearch.WordTrace tailWord_416651 prefixEnd_416651 190170869490270741996767 := by
  unfold tailWord_416651
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196510413552060170705807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10131006942368040113803871 15196510413552060170705807)
  ·
    refine ⟨22794765620328090256058711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15196510413552060170705807 22794765620328090256058711)
    ·
      refine ⟨34192148430492135384088067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22794765620328090256058711 34192148430492135384088067)
      ·
        refine ⟨51288222645738203076132101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34192148430492135384088067 51288222645738203076132101)
        ·
          refine ⟨9616541746075913076774769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51288222645738203076132101 9616541746075913076774769)
          ·
            refine ⟨7212406309556934807581077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9616541746075913076774769 7212406309556934807581077)
            ·
              refine ⟨338081545760481319105363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7212406309556934807581077 338081545760481319105363)
              ·
                refine ⟨507122318640721978658045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338081545760481319105363 507122318640721978658045)
                ·
                  refine ⟨190170869490270741996767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507122318640721978658045 190170869490270741996767)
                  ·
                    rfl

theorem cell20_416651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_416651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416651 prefixEnd_416651 := by exact prefixLift 416651
  have htrace : WordTrace (prefixWord ++ tailWord_416651) baseStart_416651 baseEnd_416651 := by
    simpa [prefixWord, tailWord_416651, baseEnd_416651] using wordTrace_append hprefix tailTrace_416651
  have hstable : (prefixWord ++ tailWord_416651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416651).length < 2 ^ (prefixWord ++ tailWord_416651).sum := by decide
  have hdescent : baseEnd_416651 < baseStart_416651 := by decide
  rcases family_descends (prefixWord ++ tailWord_416651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416685 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_416685 : Nat := 118140960795 + 416685 * 2 ^ 59
def prefixEnd_416685 : Nat := 4983230072969 + 3 ^ 40 * 416685 * 2
def baseEnd_416685 : Nat := 190186388016717734863295

theorem tailTrace_416685 : CollatzResearch.WordTrace tailWord_416685 prefixEnd_416685 190186388016717734863295 := by
  unfold tailWord_416685
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197750495428883977443509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10131833663619255984962339 15197750495428883977443509)
  ·
    refine ⟨1424789108946457872885329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15197750495428883977443509 1424789108946457872885329)
    ·
      refine ⟨1068591831709843404663997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1424789108946457872885329 1068591831709843404663997)
      ·
        refine ⟨400721936891191276748999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1068591831709843404663997 400721936891191276748999)
        ·
          refine ⟨601082905336786915123499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400721936891191276748999 601082905336786915123499)
          ·
            refine ⟨901624358005180372685249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601082905336786915123499 901624358005180372685249)
            ·
              refine ⟨676218268503885279513937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901624358005180372685249 676218268503885279513937)
              ·
                refine ⟨507163701377913959635453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676218268503885279513937 507163701377913959635453)
                ·
                  refine ⟨190186388016717734863295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507163701377913959635453 190186388016717734863295)
                  ·
                    rfl

theorem cell20_416685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_416685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416685 prefixEnd_416685 := by exact prefixLift 416685
  have htrace : WordTrace (prefixWord ++ tailWord_416685) baseStart_416685 baseEnd_416685 := by
    simpa [prefixWord, tailWord_416685, baseEnd_416685] using wordTrace_append hprefix tailTrace_416685
  have hstable : (prefixWord ++ tailWord_416685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416685).length < 2 ^ (prefixWord ++ tailWord_416685).sum := by decide
  have hdescent : baseEnd_416685 < baseStart_416685 := by decide
  rcases family_descends (prefixWord ++ tailWord_416685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416779 : List Nat := [1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_416779 : Nat := 118140960795 + 416779 * 2 ^ 59
def prefixEnd_416779 : Nat := 4983230072969 + 3 ^ 40 * 416779 * 2
def baseEnd_416779 : Nat := 63409764059357061909859

theorem tailTrace_416779 : CollatzResearch.WordTrace tailWord_416779 prefixEnd_416779 63409764059357061909859 := by
  unfold tailWord_416779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201178957088338031365391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134119304725558687576927 15201178957088338031365391)
  ·
    refine ⟨22801768435632507047048087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15201178957088338031365391 22801768435632507047048087)
    ·
      refine ⟨34202652653448760570572131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22801768435632507047048087 34202652653448760570572131)
      ·
        refine ⟨51303978980173140855858197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34202652653448760570572131 51303978980173140855858197)
        ·
          refine ⟨2404874014695615977618353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51303978980173140855858197 2404874014695615977618353)
          ·
            refine ⟨1803655511021711983213765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2404874014695615977618353 1803655511021711983213765)
            ·
              refine ⟨338185408316570996852581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1803655511021711983213765 338185408316570996852581)
              ·
                refine ⟨63409764059357061909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338185408316570996852581 63409764059357061909859)
                ·
                  rfl

theorem cell20_416779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_416779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416779 prefixEnd_416779 := by exact prefixLift 416779
  have htrace : WordTrace (prefixWord ++ tailWord_416779) baseStart_416779 baseEnd_416779 := by
    simpa [prefixWord, tailWord_416779, baseEnd_416779] using wordTrace_append hprefix tailTrace_416779
  have hstable : (prefixWord ++ tailWord_416779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416779).length < 2 ^ (prefixWord ++ tailWord_416779).sum := by decide
  have hdescent : baseEnd_416779 < baseStart_416779 := by decide
  rcases family_descends (prefixWord ++ tailWord_416779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416789 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 2]
def baseStart_416789 : Nat := 118140960795 + 416789 * 2 ^ 59
def prefixEnd_416789 : Nat := 4983230072969 + 3 ^ 40 * 416789 * 2
def baseEnd_416789 : Nat := 190233856450555595396203

theorem tailTrace_416789 : CollatzResearch.WordTrace tailWord_416789 prefixEnd_416789 190233856450555595396203 := by
  unfold tailWord_416789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201543687052109739229421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134362458034739826152947 15201543687052109739229421)
  ·
    refine ⟨5700578882644541152211033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15201543687052109739229421 5700578882644541152211033)
    ·
      refine ⟨4275434161983405864158275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700578882644541152211033 4275434161983405864158275)
      ·
        refine ⟨6413151242975108796237413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275434161983405864158275 6413151242975108796237413)
        ·
          refine ⟨1202465858057832899294515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6413151242975108796237413 1202465858057832899294515)
          ·
            refine ⟨1803698787086749348941773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202465858057832899294515 1803698787086749348941773)
            ·
              refine ⟨676387045157531005853165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1803698787086749348941773 676387045157531005853165)
              ·
                refine ⟨253645141934074127194937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676387045157531005853165 253645141934074127194937)
                ·
                  refine ⟨190233856450555595396203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253645141934074127194937 190233856450555595396203)
                  ·
                    rfl

theorem cell20_416789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_416789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416789 prefixEnd_416789 := by exact prefixLift 416789
  have htrace : WordTrace (prefixWord ++ tailWord_416789) baseStart_416789 baseEnd_416789 := by
    simpa [prefixWord, tailWord_416789, baseEnd_416789] using wordTrace_append hprefix tailTrace_416789
  have hstable : (prefixWord ++ tailWord_416789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416789).length < 2 ^ (prefixWord ++ tailWord_416789).sum := by decide
  have hdescent : baseEnd_416789 < baseStart_416789 := by decide
  rcases family_descends (prefixWord ++ tailWord_416789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416796 : List Nat := [2, 2, 3, 1, 5, 1, 6]
def baseStart_416796 : Nat := 118140960795 + 416796 * 2 ^ 59
def prefixEnd_416796 : Nat := 4983230072969 + 3 ^ 40 * 416796 * 2
def baseEnd_416796 : Nat := 21137450160143853573649

theorem tailTrace_416796 : CollatzResearch.WordTrace tailWord_416796 prefixEnd_416796 21137450160143853573649 := by
  unfold tailWord_416796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600899499013374967367121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10134532665351166623156161 7600899499013374967367121)
  ·
    refine ⟨5700674624260031225525341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7600899499013374967367121 5700674624260031225525341)
    ·
      refine ⟨2137752984097511709572003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5700674624260031225525341 2137752984097511709572003)
      ·
        refine ⟨3206629476146267564358005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137752984097511709572003 3206629476146267564358005)
        ·
          refine ⟨300621513388712584158563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3206629476146267564358005 300621513388712584158563)
          ·
            refine ⟨450932270083068876237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300621513388712584158563 450932270083068876237845)
            ·
              refine ⟨21137450160143853573649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450932270083068876237845 21137450160143853573649)
              ·
                rfl

theorem cell20_416796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_416796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416796 prefixEnd_416796 := by exact prefixLift 416796
  have htrace : WordTrace (prefixWord ++ tailWord_416796) baseStart_416796 baseEnd_416796 := by
    simpa [prefixWord, tailWord_416796, baseEnd_416796] using wordTrace_append hprefix tailTrace_416796
  have hstable : (prefixWord ++ tailWord_416796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416796).length < 2 ^ (prefixWord ++ tailWord_416796).sum := by decide
  have hdescent : baseEnd_416796 < baseStart_416796 := by decide
  rcases family_descends (prefixWord ++ tailWord_416796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416820 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_416820 : Nat := 118140960795 + 416820 * 2 ^ 59
def prefixEnd_416820 : Nat := 4983230072969 + 3 ^ 40 * 416820 * 2
def baseEnd_416820 : Nat := 190248005695257265362743

theorem tailTrace_416820 : CollatzResearch.WordTrace tailWord_416820 prefixEnd_416820 190248005695257265362743 := by
  unfold tailWord_416820
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601337174969901016803957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10135116233293201355738609 7601337174969901016803957)
  ·
    refine ⟨712625360153428220325371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7601337174969901016803957 712625360153428220325371)
    ·
      refine ⟨1068938040230142330488057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712625360153428220325371 1068938040230142330488057)
      ·
        refine ⟨801703530172606747866043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1068938040230142330488057 801703530172606747866043)
        ·
          refine ⟨1202555295258910121799065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801703530172606747866043 1202555295258910121799065)
          ·
            refine ⟨901916471444182591349299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202555295258910121799065 901916471444182591349299)
            ·
              refine ⟨1352874707166273887023949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901916471444182591349299 1352874707166273887023949)
              ·
                refine ⟨507328015187352707633981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352874707166273887023949 507328015187352707633981)
                ·
                  refine ⟨190248005695257265362743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507328015187352707633981 190248005695257265362743)
                  ·
                    rfl

theorem cell20_416820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_416820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416820 prefixEnd_416820 := by exact prefixLift 416820
  have htrace : WordTrace (prefixWord ++ tailWord_416820) baseStart_416820 baseEnd_416820 := by
    simpa [prefixWord, tailWord_416820, baseEnd_416820] using wordTrace_append hprefix tailTrace_416820
  have hstable : (prefixWord ++ tailWord_416820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416820).length < 2 ^ (prefixWord ++ tailWord_416820).sum := by decide
  have hdescent : baseEnd_416820 < baseStart_416820 := by decide
  rcases family_descends (prefixWord ++ tailWord_416820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416865 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 2]
def baseStart_416865 : Nat := 118140960795 + 416865 * 2 ^ 59
def prefixEnd_416865 : Nat := 4983230072969 + 3 ^ 40 * 416865 * 2
def baseEnd_416865 : Nat := 190268544921437108862559

theorem tailTrace_416865 : CollatzResearch.WordTrace tailWord_416865 prefixEnd_416865 190268544921437108862559 := by
  unfold tailWord_416865
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204315634776774718996049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10136210423184516479330699 15204315634776774718996049)
  ·
    refine ⟨11403236726082581039247037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15204315634776774718996049 11403236726082581039247037)
    ·
      refine ⟨4276213772280967889717639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11403236726082581039247037 4276213772280967889717639)
      ·
        refine ⟨6414320658421451834576459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276213772280967889717639 6414320658421451834576459)
        ·
          refine ⟨9621480987632177751864689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414320658421451834576459 9621480987632177751864689)
          ·
            refine ⟨7216110740724133313898517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9621480987632177751864689 7216110740724133313898517)
            ·
              refine ⟨338255190971443749088993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7216110740724133313898517 338255190971443749088993)
              ·
                refine ⟨253691393228582811816745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338255190971443749088993 253691393228582811816745)
                ·
                  refine ⟨190268544921437108862559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253691393228582811816745 190268544921437108862559)
                  ·
                    rfl

theorem cell20_416865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_416865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416865 prefixEnd_416865 := by exact prefixLift 416865
  have htrace : WordTrace (prefixWord ++ tailWord_416865) baseStart_416865 baseEnd_416865 := by
    simpa [prefixWord, tailWord_416865, baseEnd_416865] using wordTrace_append hprefix tailTrace_416865
  have hstable : (prefixWord ++ tailWord_416865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416865).length < 2 ^ (prefixWord ++ tailWord_416865).sum := by decide
  have hdescent : baseEnd_416865 < baseStart_416865 := by decide
  rcases family_descends (prefixWord ++ tailWord_416865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416869 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_416869 : Nat := 118140960795 + 416869 * 2 ^ 59
def prefixEnd_416869 : Nat := 4983230072969 + 3 ^ 40 * 416869 * 2
def baseEnd_416869 : Nat := 190270370630430872729209

theorem tailTrace_416869 : CollatzResearch.WordTrace tailWord_416869 prefixEnd_416869 190270370630430872729209 := by
  unfold tailWord_416869
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204461526762283402141661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10136307684508188934761107 15204461526762283402141661)
  ·
    refine ⟨5701673072535856275803123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15204461526762283402141661 5701673072535856275803123)
    ·
      refine ⟨8552509608803784413704685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5701673072535856275803123 8552509608803784413704685)
      ·
        refine ⟨3207191103301419155139257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8552509608803784413704685 3207191103301419155139257)
        ·
          refine ⟨2405393327476064366354443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207191103301419155139257 2405393327476064366354443)
          ·
            refine ⟨3608089991214096549531665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405393327476064366354443 3608089991214096549531665)
            ·
              refine ⟨2706067493410572412148749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608089991214096549531665 2706067493410572412148749)
              ·
                refine ⟨1014775310028964654555781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2706067493410572412148749 1014775310028964654555781)
                ·
                  refine ⟨190270370630430872729209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014775310028964654555781 190270370630430872729209)
                  ·
                    rfl

theorem cell20_416869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_416869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416869 prefixEnd_416869 := by exact prefixLift 416869
  have htrace : WordTrace (prefixWord ++ tailWord_416869) baseStart_416869 baseEnd_416869 := by
    simpa [prefixWord, tailWord_416869, baseEnd_416869] using wordTrace_append hprefix tailTrace_416869
  have hstable : (prefixWord ++ tailWord_416869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416869).length < 2 ^ (prefixWord ++ tailWord_416869).sum := by decide
  have hdescent : baseEnd_416869 < baseStart_416869 := by decide
  rcases family_descends (prefixWord ++ tailWord_416869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416886 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_416886 : Nat := 118140960795 + 416886 * 2 ^ 59
def prefixEnd_416886 : Nat := 4983230072969 + 3 ^ 40 * 416886 * 2
def baseEnd_416886 : Nat := 190278129893654369162473

theorem tailTrace_416886 : CollatzResearch.WordTrace tailWord_416886 prefixEnd_416886 190278129893654369162473 := by
  unfold tailWord_416886
  simp only [CollatzResearch.WordTrace]
  refine ⟨950317597981293456594407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10136721045133796870340341 950317597981293456594407)
  ·
    refine ⟨1425476396971940184891611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950317597981293456594407 1425476396971940184891611)
    ·
      refine ⟨2138214595457910277337417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425476396971940184891611 2138214595457910277337417)
      ·
        refine ⟨1603660946593432708003063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138214595457910277337417 1603660946593432708003063)
        ·
          refine ⟨2405491419890149062004595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603660946593432708003063 2405491419890149062004595)
          ·
            refine ⟨3608237129835223593006893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405491419890149062004595 3608237129835223593006893)
            ·
              refine ⟨1353088923688208847377585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3608237129835223593006893 1353088923688208847377585)
              ·
                refine ⟨1014816692766156635533189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353088923688208847377585 1014816692766156635533189)
                ·
                  refine ⟨190278129893654369162473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014816692766156635533189 190278129893654369162473)
                  ·
                    rfl

theorem cell20_416886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_416886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416886 prefixEnd_416886 := by exact prefixLift 416886
  have htrace : WordTrace (prefixWord ++ tailWord_416886) baseStart_416886 baseEnd_416886 := by
    simpa [prefixWord, tailWord_416886, baseEnd_416886] using wordTrace_append hprefix tailTrace_416886
  have hstable : (prefixWord ++ tailWord_416886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416886).length < 2 ^ (prefixWord ++ tailWord_416886).sum := by decide
  have hdescent : baseEnd_416886 < baseStart_416886 := by decide
  rcases family_descends (prefixWord ++ tailWord_416886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416893 : List Nat := [1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_416893 : Nat := 118140960795 + 416893 * 2 ^ 59
def prefixEnd_416893 : Nat := 4983230072969 + 3 ^ 40 * 416893 * 2
def baseEnd_416893 : Nat := 63427108294797818643037

theorem tailTrace_416893 : CollatzResearch.WordTrace tailWord_416893 prefixEnd_416893 63427108294797818643037 := by
  unfold tailWord_416893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205336878675335501015333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10136891252450223667343555 15205336878675335501015333)
  ·
    refine ⟨2851000664751625406440375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15205336878675335501015333 2851000664751625406440375)
    ·
      refine ⟨4276500997127438109660563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851000664751625406440375 4276500997127438109660563)
      ·
        refine ⟨6414751495691157164490845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276500997127438109660563 6414751495691157164490845)
        ·
          refine ⟨2405531810884183936684067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6414751495691157164490845 2405531810884183936684067)
          ·
            refine ⟨3608297716326275905026101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405531810884183936684067 3608297716326275905026101)
            ·
              refine ⟨338277910905588366096197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3608297716326275905026101 338277910905588366096197)
              ·
                refine ⟨63427108294797818643037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338277910905588366096197 63427108294797818643037)
                ·
                  rfl

theorem cell20_416893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_416893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416893 prefixEnd_416893 := by exact prefixLift 416893
  have htrace : WordTrace (prefixWord ++ tailWord_416893) baseStart_416893 baseEnd_416893 := by
    simpa [prefixWord, tailWord_416893, baseEnd_416893] using wordTrace_append hprefix tailTrace_416893
  have hstable : (prefixWord ++ tailWord_416893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416893).length < 2 ^ (prefixWord ++ tailWord_416893).sum := by decide
  have hdescent : baseEnd_416893 < baseStart_416893 := by decide
  rcases family_descends (prefixWord ++ tailWord_416893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416924 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_416924 : Nat := 118140960795 + 416924 * 2 ^ 59
def prefixEnd_416924 : Nat := 4983230072969 + 3 ^ 40 * 416924 * 2
def baseEnd_416924 : Nat := 190295474129095125895651

theorem tailTrace_416924 : CollatzResearch.WordTrace tailWord_416924 prefixEnd_416924 190295474129095125895651 := by
  unfold tailWord_416924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603233770781513897696913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10137645027708685196929217 7603233770781513897696913)
  ·
    refine ⟨5702425328086135423272685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7603233770781513897696913 5702425328086135423272685)
    ·
      refine ⟨2138409498032300783727257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5702425328086135423272685 2138409498032300783727257)
      ·
        refine ⟨1603807123524225587795443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138409498032300783727257 1603807123524225587795443)
        ·
          refine ⟨2405710685286338381693165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603807123524225587795443 2405710685286338381693165)
          ·
            refine ⟨902141506982376893134937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2405710685286338381693165 902141506982376893134937)
            ·
              refine ⟨676606130236782669851203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902141506982376893134937 676606130236782669851203)
              ·
                refine ⟨1014909195355174004776805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676606130236782669851203 1014909195355174004776805)
                ·
                  refine ⟨190295474129095125895651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014909195355174004776805 190295474129095125895651)
                  ·
                    rfl

theorem cell20_416924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_416924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416924 prefixEnd_416924 := by exact prefixLift 416924
  have htrace : WordTrace (prefixWord ++ tailWord_416924) baseStart_416924 baseEnd_416924 := by
    simpa [prefixWord, tailWord_416924, baseEnd_416924] using wordTrace_append hprefix tailTrace_416924
  have hstable : (prefixWord ++ tailWord_416924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416924).length < 2 ^ (prefixWord ++ tailWord_416924).sum := by decide
  have hdescent : baseEnd_416924 < baseStart_416924 := by decide
  rcases family_descends (prefixWord ++ tailWord_416924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416958 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_416958 : Nat := 118140960795 + 416958 * 2 ^ 59
def prefixEnd_416958 : Nat := 4983230072969 + 3 ^ 40 * 416958 * 2
def baseEnd_416958 : Nat := 190310992655542118762179

theorem tailTrace_416958 : CollatzResearch.WordTrace tailWord_416958 prefixEnd_416958 190310992655542118762179 := by
  unfold tailWord_416958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900963452929981450266441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10138471748959901068087685 1900963452929981450266441)
  ·
    refine ⟨1425722589697486087699831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1900963452929981450266441 1425722589697486087699831)
    ·
      refine ⟨2138583884546229131549747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425722589697486087699831 2138583884546229131549747)
      ·
        refine ⟨3207875826819343697324621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138583884546229131549747 3207875826819343697324621)
        ·
          refine ⟨1202953435057253886496733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3207875826819343697324621 1202953435057253886496733)
          ·
            refine ⟨451107538146470207436275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1202953435057253886496733 451107538146470207436275)
            ·
              refine ⟨676661307219705311154413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451107538146470207436275 676661307219705311154413)
              ·
                refine ⟨253747990207389491682905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676661307219705311154413 253747990207389491682905)
                ·
                  refine ⟨190310992655542118762179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253747990207389491682905 190310992655542118762179)
                  ·
                    rfl

theorem cell20_416958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_416958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416958 prefixEnd_416958 := by exact prefixLift 416958
  have htrace : WordTrace (prefixWord ++ tailWord_416958) baseStart_416958 baseEnd_416958 := by
    simpa [prefixWord, tailWord_416958, baseEnd_416958] using wordTrace_append hprefix tailTrace_416958
  have hstable : (prefixWord ++ tailWord_416958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416958).length < 2 ^ (prefixWord ++ tailWord_416958).sum := by decide
  have hdescent : baseEnd_416958 < baseStart_416958 := by decide
  rcases family_descends (prefixWord ++ tailWord_416958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416959 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_416959 : Nat := 118140960795 + 416959 * 2 ^ 59
def prefixEnd_416959 : Nat := 4983230072969 + 3 ^ 40 * 416959 * 2
def baseEnd_416959 : Nat := 190311449082790559728841

theorem tailTrace_416959 : CollatzResearch.WordTrace tailWord_416959 prefixEnd_416959 190311449082790559728841 := by
  unfold tailWord_416959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207744096436228772917931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10138496064290819181945287 15207744096436228772917931)
  ·
    refine ⟨22811616144654343159376897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15207744096436228772917931 22811616144654343159376897)
    ·
      refine ⟨17108712108490757369532673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22811616144654343159376897 17108712108490757369532673)
      ·
        refine ⟨12831534081368068027149505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17108712108490757369532673 12831534081368068027149505)
        ·
          refine ⟨9623650561026051020362129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12831534081368068027149505 9623650561026051020362129)
          ·
            refine ⟨7217737920769538265271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9623650561026051020362129 7217737920769538265271597)
            ·
              refine ⟨2706651720288576849476849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7217737920769538265271597 2706651720288576849476849)
              ·
                refine ⟨2029988790216432637107637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706651720288576849476849 2029988790216432637107637)
                ·
                  refine ⟨190311449082790559728841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029988790216432637107637 190311449082790559728841)
                  ·
                    rfl

theorem cell20_416959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_416959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416959 prefixEnd_416959 := by exact prefixLift 416959
  have htrace : WordTrace (prefixWord ++ tailWord_416959) baseStart_416959 baseEnd_416959 := by
    simpa [prefixWord, tailWord_416959, baseEnd_416959] using wordTrace_append hprefix tailTrace_416959
  have hstable : (prefixWord ++ tailWord_416959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416959).length < 2 ^ (prefixWord ++ tailWord_416959).sum := by decide
  have hdescent : baseEnd_416959 < baseStart_416959 := by decide
  rcases family_descends (prefixWord ++ tailWord_416959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416983 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_416983 : Nat := 118140960795 + 416983 * 2 ^ 59
def prefixEnd_416983 : Nat := 4983230072969 + 3 ^ 40 * 416983 * 2
def baseEnd_416983 : Nat := 190322403336753142928743

theorem tailTrace_416983 : CollatzResearch.WordTrace tailWord_416983 prefixEnd_416983 190322403336753142928743 := by
  unfold tailWord_416983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208619448349280871791603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139079632232853914527735 15208619448349280871791603)
  ·
    refine ⟨22812929172523921307687405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15208619448349280871791603 22812929172523921307687405)
    ·
      refine ⟨8554848439696470490382777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22812929172523921307687405 8554848439696470490382777)
      ·
        refine ⟨6416136329772352867787083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554848439696470490382777 6416136329772352867787083)
        ·
          refine ⟨9624204494658529301680625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416136329772352867787083 9624204494658529301680625)
          ·
            refine ⟨7218153370993896976260469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9624204494658529301680625 7218153370993896976260469)
            ·
              refine ⟨676701878530677841524419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7218153370993896976260469 676701878530677841524419)
              ·
                refine ⟨1015052817796016762286629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676701878530677841524419 1015052817796016762286629)
                ·
                  refine ⟨190322403336753142928743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015052817796016762286629 190322403336753142928743)
                  ·
                    rfl

theorem cell20_416983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_416983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416983 prefixEnd_416983 := by exact prefixLift 416983
  have htrace : WordTrace (prefixWord ++ tailWord_416983) baseStart_416983 baseEnd_416983 := by
    simpa [prefixWord, tailWord_416983, baseEnd_416983] using wordTrace_append hprefix tailTrace_416983
  have hstable : (prefixWord ++ tailWord_416983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416983).length < 2 ^ (prefixWord ++ tailWord_416983).sum := by decide
  have hdescent : baseEnd_416983 < baseStart_416983 := by decide
  rcases family_descends (prefixWord ++ tailWord_416983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416989 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_416989 : Nat := 118140960795 + 416989 * 2 ^ 59
def prefixEnd_416989 : Nat := 4983230072969 + 3 ^ 40 * 416989 * 2
def baseEnd_416989 : Nat := 190325141900243788728719

theorem tailTrace_416989 : CollatzResearch.WordTrace tailWord_416989 prefixEnd_416989 190325141900243788728719 := by
  unfold tailWord_416989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208838286327543896510021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139225524218362597673347 15208838286327543896510021)
  ·
    refine ⟨2851657178686414480595629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15208838286327543896510021 2851657178686414480595629)
    ·
      refine ⟨1069371442007405430223361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2851657178686414480595629 1069371442007405430223361)
      ·
        refine ⟨802028581505554072667521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069371442007405430223361 802028581505554072667521)
        ·
          refine ⟨601521436129165554500641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802028581505554072667521 601521436129165554500641)
          ·
            refine ⟨451141077096874165875481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601521436129165554500641 451141077096874165875481)
            ·
              refine ⟨338355807822655624406611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451141077096874165875481 338355807822655624406611)
              ·
                refine ⟨507533711733983436609917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338355807822655624406611 507533711733983436609917)
                ·
                  refine ⟨190325141900243788728719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507533711733983436609917 190325141900243788728719)
                  ·
                    rfl

theorem cell20_416989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_416989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416989 prefixEnd_416989 := by exact prefixLift 416989
  have htrace : WordTrace (prefixWord ++ tailWord_416989) baseStart_416989 baseEnd_416989 := by
    simpa [prefixWord, tailWord_416989, baseEnd_416989] using wordTrace_append hprefix tailTrace_416989
  have hstable : (prefixWord ++ tailWord_416989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416989).length < 2 ^ (prefixWord ++ tailWord_416989).sum := by decide
  have hdescent : baseEnd_416989 < baseStart_416989 := by decide
  rcases family_descends (prefixWord ++ tailWord_416989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416993 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_416993 : Nat := 118140960795 + 416993 * 2 ^ 59
def prefixEnd_416993 : Nat := 4983230072969 + 3 ^ 40 * 416993 * 2
def baseEnd_416993 : Nat := 190326967609237552595369

theorem tailTrace_416993 : CollatzResearch.WordTrace tailWord_416993 prefixEnd_416993 190326967609237552595369 := by
  unfold tailWord_416993
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208984178313052579655633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139322785542035053103755 15208984178313052579655633)
  ·
    refine ⟨11406738133734789434741725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15208984178313052579655633 11406738133734789434741725)
    ·
      refine ⟨4277526800150546038028147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11406738133734789434741725 4277526800150546038028147)
      ·
        refine ⟨6416290200225819057042221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277526800150546038028147 6416290200225819057042221)
        ·
          refine ⟨2406108825084682146390833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6416290200225819057042221 2406108825084682146390833)
          ·
            refine ⟨1804581618813511609793125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2406108825084682146390833 1804581618813511609793125)
            ·
              refine ⟨338359053527533426836211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1804581618813511609793125 338359053527533426836211)
              ·
                refine ⟨507538580291300140254317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338359053527533426836211 507538580291300140254317)
                ·
                  refine ⟨190326967609237552595369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507538580291300140254317 190326967609237552595369)
                  ·
                    rfl

theorem cell20_416993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_416993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_416993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_416993 prefixEnd_416993 := by exact prefixLift 416993
  have htrace : WordTrace (prefixWord ++ tailWord_416993) baseStart_416993 baseEnd_416993 := by
    simpa [prefixWord, tailWord_416993, baseEnd_416993] using wordTrace_append hprefix tailTrace_416993
  have hstable : (prefixWord ++ tailWord_416993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416993).length < 2 ^ (prefixWord ++ tailWord_416993).sum := by decide
  have hdescent : baseEnd_416993 < baseStart_416993 := by decide
  rcases family_descends (prefixWord ++ tailWord_416993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417028 : List Nat := [2, 3, 2, 2, 2, 9]
def baseStart_417028 : Nat := 118140960795 + 417028 * 2 ^ 59
def prefixEnd_417028 : Nat := 4983230072969 + 3 ^ 40 * 417028 * 2
def baseEnd_417028 : Nat := 7049738613441962460317

theorem tailTrace_417028 : CollatzResearch.WordTrace tailWord_417028 prefixEnd_417028 7049738613441962460317 := by
  unfold tailWord_417028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605130366593126778589869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10140173822124169038119825 7605130366593126778589869)
  ·
    refine ⟨2851923887472422541971201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7605130366593126778589869 2851923887472422541971201)
    ·
      refine ⟨2138942915604316906478401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2851923887472422541971201 2138942915604316906478401)
      ·
        refine ⟨1604207186703237679858801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138942915604316906478401 1604207186703237679858801)
        ·
          refine ⟨1203155390027428259894101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604207186703237679858801 1203155390027428259894101)
          ·
            refine ⟨7049738613441962460317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1203155390027428259894101 7049738613441962460317)
            ·
              rfl

theorem cell20_417028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 9].length) (baseStart_417028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417028 prefixEnd_417028 := by exact prefixLift 417028
  have htrace : WordTrace (prefixWord ++ tailWord_417028) baseStart_417028 baseEnd_417028 := by
    simpa [prefixWord, tailWord_417028, baseEnd_417028] using wordTrace_append hprefix tailTrace_417028
  have hstable : (prefixWord ++ tailWord_417028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417028).length < 2 ^ (prefixWord ++ tailWord_417028).sum := by decide
  have hdescent : baseEnd_417028 < baseStart_417028 := by decide
  rcases family_descends (prefixWord ++ tailWord_417028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417052 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_417052 : Nat := 118140960795 + 417052 * 2 ^ 59
def prefixEnd_417052 : Nat := 4983230072969 + 3 ^ 40 * 417052 * 2
def baseEnd_417052 : Nat := 190353896816895569628461

theorem tailTrace_417052 : CollatzResearch.WordTrace tailWord_417052 prefixEnd_417052 190353896816895569628461 := by
  unfold tailWord_417052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605568042549652828026705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10140757390066203770702273 7605568042549652828026705)
  ·
    refine ⟨5704176031912239621020029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7605568042549652828026705 5704176031912239621020029)
    ·
      refine ⟨2139066011967089857882511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5704176031912239621020029 2139066011967089857882511)
      ·
        refine ⟨3208599017950634786823767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139066011967089857882511 3208599017950634786823767)
        ·
          refine ⟨4812898526925952180235651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208599017950634786823767 4812898526925952180235651)
          ·
            refine ⟨7219347790388928270353477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812898526925952180235651 7219347790388928270353477)
            ·
              refine ⟨1353627710697924050691277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7219347790388928270353477 1353627710697924050691277)
              ·
                refine ⟨507610391511721519009229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353627710697924050691277 507610391511721519009229)
                ·
                  refine ⟨190353896816895569628461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507610391511721519009229 190353896816895569628461)
                  ·
                    rfl

theorem cell20_417052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_417052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417052 prefixEnd_417052 := by exact prefixLift 417052
  have htrace : WordTrace (prefixWord ++ tailWord_417052) baseStart_417052 baseEnd_417052 := by
    simpa [prefixWord, tailWord_417052, baseEnd_417052] using wordTrace_append hprefix tailTrace_417052
  have hstable : (prefixWord ++ tailWord_417052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417052).length < 2 ^ (prefixWord ++ tailWord_417052).sum := by decide
  have hdescent : baseEnd_417052 < baseStart_417052 := by decide
  rcases family_descends (prefixWord ++ tailWord_417052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417059 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_417059 : Nat := 118140960795 + 417059 * 2 ^ 59
def prefixEnd_417059 : Nat := 4983230072969 + 3 ^ 40 * 417059 * 2
def baseEnd_417059 : Nat := 190357091807634656395099

theorem tailTrace_417059 : CollatzResearch.WordTrace tailWord_417059 prefixEnd_417059 190357091807634656395099 := by
  unfold tailWord_417059
  simp only [CollatzResearch.WordTrace]
  refine ⟨15211391396073945851558231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10140927597382630567705487 15211391396073945851558231)
  ·
    refine ⟨22817087094110918777337347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15211391396073945851558231 22817087094110918777337347)
    ·
      refine ⟨34225630641166378166006021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22817087094110918777337347 34225630641166378166006021)
      ·
        refine ⟨6417305745218695906126129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34225630641166378166006021 6417305745218695906126129)
        ·
          refine ⟨4812979308914021929594597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6417305745218695906126129 4812979308914021929594597)
          ·
            refine ⟨902433620421379111798987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4812979308914021929594597 902433620421379111798987)
            ·
              refine ⟨1353650430632068667698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902433620421379111798987 1353650430632068667698481)
              ·
                refine ⟨1015237822974051500773861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353650430632068667698481 1015237822974051500773861)
                ·
                  refine ⟨190357091807634656395099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015237822974051500773861 190357091807634656395099)
                  ·
                    rfl

theorem cell20_417059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_417059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417059 prefixEnd_417059 := by exact prefixLift 417059
  have htrace : WordTrace (prefixWord ++ tailWord_417059) baseStart_417059 baseEnd_417059 := by
    simpa [prefixWord, tailWord_417059, baseEnd_417059] using wordTrace_append hprefix tailTrace_417059
  have hstable : (prefixWord ++ tailWord_417059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417059).length < 2 ^ (prefixWord ++ tailWord_417059).sum := by decide
  have hdescent : baseEnd_417059 < baseStart_417059 := by decide
  rcases family_descends (prefixWord ++ tailWord_417059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417080 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_417080 : Nat := 118140960795 + 417080 * 2 ^ 59
def prefixEnd_417080 : Nat := 4983230072969 + 3 ^ 40 * 417080 * 2
def baseEnd_417080 : Nat := 190366676779851916695013

theorem tailTrace_417080 : CollatzResearch.WordTrace tailWord_417080 prefixEnd_417080 190366676779851916695013 := by
  unfold tailWord_417080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7606078664498933219036347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10141438219331910958715129 7606078664498933219036347)
  ·
    refine ⟨11409117996748399828554521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7606078664498933219036347 11409117996748399828554521)
    ·
      refine ⟨8556838497561299871415891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11409117996748399828554521 8556838497561299871415891)
      ·
        refine ⟨12835257746341949807123837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556838497561299871415891 12835257746341949807123837)
        ·
          refine ⟨4813221654878231177671439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12835257746341949807123837 4813221654878231177671439)
          ·
            refine ⟨7219832482317346766507159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813221654878231177671439 7219832482317346766507159)
            ·
              refine ⟨10829748723476020149760739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219832482317346766507159 10829748723476020149760739)
              ·
                refine ⟨16244623085214030224641109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10829748723476020149760739 16244623085214030224641109)
                ·
                  refine ⟨190366676779851916695013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16244623085214030224641109 190366676779851916695013)
                  ·
                    rfl

theorem cell20_417080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_417080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417080 prefixEnd_417080 := by exact prefixLift 417080
  have htrace : WordTrace (prefixWord ++ tailWord_417080) baseStart_417080 baseEnd_417080 := by
    simpa [prefixWord, tailWord_417080, baseEnd_417080] using wordTrace_append hprefix tailTrace_417080
  have hstable : (prefixWord ++ tailWord_417080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417080).length < 2 ^ (prefixWord ++ tailWord_417080).sum := by decide
  have hdescent : baseEnd_417080 < baseStart_417080 := by decide
  rcases family_descends (prefixWord ++ tailWord_417080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417117 : List Nat := [1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_417117 : Nat := 118140960795 + 417117 * 2 ^ 59
def prefixEnd_417117 : Nat := 4983230072969 + 3 ^ 40 * 417117 * 2
def baseEnd_417117 : Nat := 63461188196014744153843

theorem tailTrace_417117 : CollatzResearch.WordTrace tailWord_417117 prefixEnd_417117 63461188196014744153843 := by
  unfold tailWord_417117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213506829863821757169605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10142337886575881171446403 15213506829863821757169605)
  ·
    refine ⟨2852532530599466579469301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15213506829863821757169605 2852532530599466579469301)
    ·
      refine ⟨267424924743699991825247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2852532530599466579469301 267424924743699991825247)
      ·
        refine ⟨401137387115549987737871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267424924743699991825247 401137387115549987737871)
        ·
          refine ⟨601706080673324981606807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401137387115549987737871 601706080673324981606807)
          ·
            refine ⟨902559121009987472410211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601706080673324981606807 902559121009987472410211)
            ·
              refine ⟨1353838681514981208615317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902559121009987472410211 1353838681514981208615317)
              ·
                refine ⟨63461188196014744153843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1353838681514981208615317 63461188196014744153843)
                ·
                  rfl

theorem cell20_417117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_417117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417117 prefixEnd_417117 := by exact prefixLift 417117
  have htrace : WordTrace (prefixWord ++ tailWord_417117) baseStart_417117 baseEnd_417117 := by
    simpa [prefixWord, tailWord_417117, baseEnd_417117] using wordTrace_append hprefix tailTrace_417117
  have hstable : (prefixWord ++ tailWord_417117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417117).length < 2 ^ (prefixWord ++ tailWord_417117).sum := by decide
  have hdescent : baseEnd_417117 < baseStart_417117 := by decide
  rcases family_descends (prefixWord ++ tailWord_417117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417149 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_417149 : Nat := 118140960795 + 417149 * 2 ^ 59
def prefixEnd_417149 : Nat := 4983230072969 + 3 ^ 40 * 417149 * 2
def baseEnd_417149 : Nat := 190398170259994343394731

theorem tailTrace_417149 : CollatzResearch.WordTrace tailWord_417149 prefixEnd_417149 190398170259994343394731 := by
  unfold tailWord_417149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214673965747891222334501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10143115977165260814889667 15214673965747891222334501)
  ·
    refine ⟨2852751368577729604187719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15214673965747891222334501 2852751368577729604187719)
    ·
      refine ⟨4279127052866594406281579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852751368577729604187719 4279127052866594406281579)
      ·
        refine ⟨6418690579299891609422369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279127052866594406281579 6418690579299891609422369)
        ·
          refine ⟨4814017934474918707066777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418690579299891609422369 4814017934474918707066777)
          ·
            refine ⟨3610513450856189030300083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4814017934474918707066777 3610513450856189030300083)
            ·
              refine ⟨5415770176284283545450125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610513450856189030300083 5415770176284283545450125)
              ·
                refine ⟨2030913816106606329543797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415770176284283545450125 2030913816106606329543797)
                ·
                  refine ⟨190398170259994343394731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030913816106606329543797 190398170259994343394731)
                  ·
                    rfl

theorem cell20_417149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_417149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417149 prefixEnd_417149 := by exact prefixLift 417149
  have htrace : WordTrace (prefixWord ++ tailWord_417149) baseStart_417149 baseEnd_417149 := by
    simpa [prefixWord, tailWord_417149, baseEnd_417149] using wordTrace_append hprefix tailTrace_417149
  have hstable : (prefixWord ++ tailWord_417149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417149).length < 2 ^ (prefixWord ++ tailWord_417149).sum := by decide
  have hdescent : baseEnd_417149 < baseStart_417149 := by decide
  rcases family_descends (prefixWord ++ tailWord_417149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417232 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_417232 : Nat := 118140960795 + 417232 * 2 ^ 59
def prefixEnd_417232 : Nat := 4983230072969 + 3 ^ 40 * 417232 * 2
def baseEnd_417232 : Nat := 190436053721614943627725

theorem tailTrace_417232 : CollatzResearch.WordTrace tailWord_417232 prefixEnd_417232 190436053721614943627725 := by
  unfold tailWord_417232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608850612223598198802975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10145134149631464265070633 7608850612223598198802975)
  ·
    refine ⟨11413275918335397298204463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7608850612223598198802975 11413275918335397298204463)
    ·
      refine ⟨17119913877503095947306695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413275918335397298204463 17119913877503095947306695)
      ·
        refine ⟨25679870816254643920960043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17119913877503095947306695 25679870816254643920960043)
        ·
          refine ⟨38519806224381965881440065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25679870816254643920960043 38519806224381965881440065)
          ·
            refine ⟨28889854668286474411080049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38519806224381965881440065 28889854668286474411080049)
            ·
              refine ⟨21667391001214855808310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28889854668286474411080049 21667391001214855808310037)
              ·
                refine ⟨1015658953181946366014533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21667391001214855808310037 1015658953181946366014533)
                ·
                  refine ⟨190436053721614943627725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015658953181946366014533 190436053721614943627725)
                  ·
                    rfl

theorem cell20_417232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_417232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417232 prefixEnd_417232 := by exact prefixLift 417232
  have htrace : WordTrace (prefixWord ++ tailWord_417232) baseStart_417232 baseEnd_417232 := by
    simpa [prefixWord, tailWord_417232, baseEnd_417232] using wordTrace_append hprefix tailTrace_417232
  have hstable : (prefixWord ++ tailWord_417232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417232).length < 2 ^ (prefixWord ++ tailWord_417232).sum := by decide
  have hdescent : baseEnd_417232 < baseStart_417232 := by decide
  rcases family_descends (prefixWord ++ tailWord_417232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417239 : List Nat := [1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_417239 : Nat := 118140960795 + 417239 * 2 ^ 59
def prefixEnd_417239 : Nat := 4983230072969 + 3 ^ 40 * 417239 * 2
def baseEnd_417239 : Nat := 63479749570784676798121

theorem tailTrace_417239 : CollatzResearch.WordTrace tailWord_417239 prefixEnd_417239 63479749570784676798121 := by
  unfold tailWord_417239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217956535421836593110771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10145304356947891062073847 15217956535421836593110771)
  ·
    refine ⟨22826934803132754889666157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15217956535421836593110771 22826934803132754889666157)
    ·
      refine ⟨8560100551174783083624809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22826934803132754889666157 8560100551174783083624809)
      ·
        refine ⟨6420075413381087312718607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8560100551174783083624809 6420075413381087312718607)
        ·
          refine ⟨9630113120071630969077911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6420075413381087312718607 9630113120071630969077911)
          ·
            refine ⟨14445169680107446453616867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9630113120071630969077911 14445169680107446453616867)
            ·
              refine ⟨21667754520161169680425301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14445169680107446453616867 21667754520161169680425301)
              ·
                refine ⟨63479749570784676798121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21667754520161169680425301 63479749570784676798121)
                ·
                  rfl

theorem cell20_417239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_417239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417239 prefixEnd_417239 := by exact prefixLift 417239
  have htrace : WordTrace (prefixWord ++ tailWord_417239) baseStart_417239 baseEnd_417239 := by
    simpa [prefixWord, tailWord_417239, baseEnd_417239] using wordTrace_append hprefix tailTrace_417239
  have hstable : (prefixWord ++ tailWord_417239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417239).length < 2 ^ (prefixWord ++ tailWord_417239).sum := by decide
  have hdescent : baseEnd_417239 < baseStart_417239 := by decide
  rcases family_descends (prefixWord ++ tailWord_417239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417245 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 2]
def baseStart_417245 : Nat := 118140960795 + 417245 * 2 ^ 59
def prefixEnd_417245 : Nat := 4983230072969 + 3 ^ 40 * 417245 * 2
def baseEnd_417245 : Nat := 190441987275844676194339

theorem tailTrace_417245 : CollatzResearch.WordTrace tailWord_417245 prefixEnd_417245 190441987275844676194339 := by
  unfold tailWord_417245
  simp only [CollatzResearch.WordTrace]
  refine ⟨15218175373400099617829189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10145450248933399745219459 15218175373400099617829189)
  ·
    refine ⟨2853407882512518678342973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15218175373400099617829189 2853407882512518678342973)
    ·
      refine ⟨1070027955942194504378615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2853407882512518678342973 1070027955942194504378615)
      ·
        refine ⟨1605041933913291756567923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070027955942194504378615 1605041933913291756567923)
        ·
          refine ⟨2407562900869937634851885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605041933913291756567923 2407562900869937634851885)
          ·
            refine ⟨902836087826226613069457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407562900869937634851885 902836087826226613069457)
            ·
              refine ⟨677127065869669959802093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902836087826226613069457 677127065869669959802093)
              ·
                refine ⟨253922649701126234925785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 677127065869669959802093 253922649701126234925785)
                ·
                  refine ⟨190441987275844676194339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253922649701126234925785 190441987275844676194339)
                  ·
                    rfl

theorem cell20_417245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_417245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417245 prefixEnd_417245 := by exact prefixLift 417245
  have htrace : WordTrace (prefixWord ++ tailWord_417245) baseStart_417245 baseEnd_417245 := by
    simpa [prefixWord, tailWord_417245, baseEnd_417245] using wordTrace_append hprefix tailTrace_417245
  have hstable : (prefixWord ++ tailWord_417245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417245).length < 2 ^ (prefixWord ++ tailWord_417245).sum := by decide
  have hdescent : baseEnd_417245 < baseStart_417245 := by decide
  rcases family_descends (prefixWord ++ tailWord_417245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417266 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_417266 : Nat := 118140960795 + 417266 * 2 ^ 59
def prefixEnd_417266 : Nat := 4983230072969 + 3 ^ 40 * 417266 * 2
def baseEnd_417266 : Nat := 190451572248061936494253

theorem tailTrace_417266 : CollatzResearch.WordTrace tailWord_417266 prefixEnd_417266 190451572248061936494253 := by
  unfold tailWord_417266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804735326581005051085913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10145960870882680136229101 3804735326581005051085913)
  ·
    refine ⟨2853551494935753788314435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3804735326581005051085913 2853551494935753788314435)
    ·
      refine ⟨4280327242403630682471653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853551494935753788314435 4280327242403630682471653)
      ·
        refine ⟨802561357950680752963435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4280327242403630682471653 802561357950680752963435)
        ·
          refine ⟨1203842036926021129445153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802561357950680752963435 1203842036926021129445153)
          ·
            refine ⟨902881527694515847083865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203842036926021129445153 902881527694515847083865)
            ·
              refine ⟨677161145770886885312899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902881527694515847083865 677161145770886885312899)
              ·
                refine ⟨1015741718656330327969349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677161145770886885312899 1015741718656330327969349)
                ·
                  refine ⟨190451572248061936494253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015741718656330327969349 190451572248061936494253)
                  ·
                    rfl

theorem cell20_417266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_417266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417266 prefixEnd_417266 := by exact prefixLift 417266
  have htrace : WordTrace (prefixWord ++ tailWord_417266) baseStart_417266 baseEnd_417266 := by
    simpa [prefixWord, tailWord_417266, baseEnd_417266] using wordTrace_append hprefix tailTrace_417266
  have hstable : (prefixWord ++ tailWord_417266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417266).length < 2 ^ (prefixWord ++ tailWord_417266).sum := by decide
  have hdescent : baseEnd_417266 < baseStart_417266 := by decide
  rcases family_descends (prefixWord ++ tailWord_417266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417287 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_417287 : Nat := 118140960795 + 417287 * 2 ^ 59
def prefixEnd_417287 : Nat := 4983230072969 + 3 ^ 40 * 417287 * 2
def baseEnd_417287 : Nat := 190461157220279196794167

theorem tailTrace_417287 : CollatzResearch.WordTrace tailWord_417287 prefixEnd_417287 190461157220279196794167 := by
  unfold tailWord_417287
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219707239247940790858115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10146471492831960527238743 15219707239247940790858115)
  ·
    refine ⟨22829560858871911186287173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15219707239247940790858115 22829560858871911186287173)
    ·
      refine ⟨4280542661038483347428845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22829560858871911186287173 4280542661038483347428845)
      ·
        refine ⟨1605203497889431255285817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4280542661038483347428845 1605203497889431255285817)
        ·
          refine ⟨1203902623417073441464363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605203497889431255285817 1203902623417073441464363)
          ·
            refine ⟨1805853935125610162196545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203902623417073441464363 1805853935125610162196545)
            ·
              refine ⟨1354390451344207621647409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805853935125610162196545 1354390451344207621647409)
              ·
                refine ⟨1015792838508155716235557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354390451344207621647409 1015792838508155716235557)
                ·
                  refine ⟨190461157220279196794167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015792838508155716235557 190461157220279196794167)
                  ·
                    rfl

theorem cell20_417287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_417287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417287 prefixEnd_417287 := by exact prefixLift 417287
  have htrace : WordTrace (prefixWord ++ tailWord_417287) baseStart_417287 baseEnd_417287 := by
    simpa [prefixWord, tailWord_417287, baseEnd_417287] using wordTrace_append hprefix tailTrace_417287
  have hstable : (prefixWord ++ tailWord_417287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417287).length < 2 ^ (prefixWord ++ tailWord_417287).sum := by decide
  have hdescent : baseEnd_417287 < baseStart_417287 := by decide
  rcases family_descends (prefixWord ++ tailWord_417287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417301 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_417301 : Nat := 118140960795 + 417301 * 2 ^ 59
def prefixEnd_417301 : Nat := 4983230072969 + 3 ^ 40 * 417301 * 2
def baseEnd_417301 : Nat := 190467547201757370327443

theorem tailTrace_417301 : CollatzResearch.WordTrace tailWord_417301 prefixEnd_417301 190467547201757370327443 := by
  unfold tailWord_417301
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220217861197221181867757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10146811907464814121245171 15220217861197221181867757)
  ·
    refine ⟨5707581697948957943200409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15220217861197221181867757 5707581697948957943200409)
    ·
      refine ⟨4280686273461718457400307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5707581697948957943200409 4280686273461718457400307)
      ·
        refine ⟨6421029410192577686100461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280686273461718457400307 6421029410192577686100461)
        ·
          refine ⟨2407886028822216632287673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6421029410192577686100461 2407886028822216632287673)
          ·
            refine ⟨1805914521616662474215755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407886028822216632287673 1805914521616662474215755)
            ·
              refine ⟨2708871782424993711323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805914521616662474215755 2708871782424993711323633)
              ·
                refine ⟨2031653836818745283492725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708871782424993711323633 2031653836818745283492725)
                ·
                  refine ⟨190467547201757370327443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2031653836818745283492725 190467547201757370327443)
                  ·
                    rfl

theorem cell20_417301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_417301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417301 prefixEnd_417301 := by exact prefixLift 417301
  have htrace : WordTrace (prefixWord ++ tailWord_417301) baseStart_417301 baseEnd_417301 := by
    simpa [prefixWord, tailWord_417301, baseEnd_417301] using wordTrace_append hprefix tailTrace_417301
  have hstable : (prefixWord ++ tailWord_417301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417301).length < 2 ^ (prefixWord ++ tailWord_417301).sum := by decide
  have hdescent : baseEnd_417301 < baseStart_417301 := by decide
  rcases family_descends (prefixWord ++ tailWord_417301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417335 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_417335 : Nat := 118140960795 + 417335 * 2 ^ 59
def prefixEnd_417335 : Nat := 4983230072969 + 3 ^ 40 * 417335 * 2
def baseEnd_417335 : Nat := 190483065728204363193971

theorem tailTrace_417335 : CollatzResearch.WordTrace tailWord_417335 prefixEnd_417335 190483065728204363193971 := by
  unfold tailWord_417335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15221457943074044988605459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10147638628716029992403639 15221457943074044988605459)
  ·
    refine ⟨22832186914611067482908189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15221457943074044988605459 22832186914611067482908189)
    ·
      refine ⟨8562070092979150306090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22832186914611067482908189 8562070092979150306090571)
      ·
        refine ⟨12843105139468725459135857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562070092979150306090571 12843105139468725459135857)
        ·
          refine ⟨9632328854601544094351893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12843105139468725459135857 9632328854601544094351893)
          ·
            refine ⟨451515415059447379422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9632328854601544094351893 451515415059447379422745)
            ·
              refine ⟨338636561294585534567059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451515415059447379422745 338636561294585534567059)
              ·
                refine ⟨507954841941878301850589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338636561294585534567059 507954841941878301850589)
                ·
                  refine ⟨190483065728204363193971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507954841941878301850589 190483065728204363193971)
                  ·
                    rfl

theorem cell20_417335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_417335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417335 prefixEnd_417335 := by exact prefixLift 417335
  have htrace : WordTrace (prefixWord ++ tailWord_417335) baseStart_417335 baseEnd_417335 := by
    simpa [prefixWord, tailWord_417335, baseEnd_417335] using wordTrace_append hprefix tailTrace_417335
  have hstable : (prefixWord ++ tailWord_417335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417335).length < 2 ^ (prefixWord ++ tailWord_417335).sum := by decide
  have hdescent : baseEnd_417335 < baseStart_417335 := by decide
  rcases family_descends (prefixWord ++ tailWord_417335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417366 : List Nat := [5, 2, 2, 2, 1, 8]
def baseStart_417366 : Nat := 118140960795 + 417366 * 2 ^ 59
def prefixEnd_417366 : Nat := 4983230072969 + 3 ^ 40 * 417366 * 2
def baseEnd_417366 : Nat := 7055452406403927154093

theorem tailTrace_417366 : CollatzResearch.WordTrace tailWord_417366 prefixEnd_417366 7055452406403927154093 := by
  unfold tailWord_417366
  simp only [CollatzResearch.WordTrace]
  refine ⟨951411787872608580186497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10148392403974491521989301 951411787872608580186497)
  ·
    refine ⟨713558840904456435139873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 951411787872608580186497 713558840904456435139873)
    ·
      refine ⟨535169130678342326354905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 713558840904456435139873 535169130678342326354905)
      ·
        refine ⟨401376848008756744766179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535169130678342326354905 401376848008756744766179)
        ·
          refine ⟨602065272013135117149269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401376848008756744766179 602065272013135117149269)
          ·
            refine ⟨7055452406403927154093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 602065272013135117149269 7055452406403927154093)
            ·
              rfl

theorem cell20_417366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 8].length) (baseStart_417366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417366 prefixEnd_417366 := by exact prefixLift 417366
  have htrace : WordTrace (prefixWord ++ tailWord_417366) baseStart_417366 baseEnd_417366 := by
    simpa [prefixWord, tailWord_417366, baseEnd_417366] using wordTrace_append hprefix tailTrace_417366
  have hstable : (prefixWord ++ tailWord_417366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417366).length < 2 ^ (prefixWord ++ tailWord_417366).sum := by decide
  have hdescent : baseEnd_417366 < baseStart_417366 := by decide
  rcases family_descends (prefixWord ++ tailWord_417366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417380 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_417380 : Nat := 118140960795 + 417380 * 2 ^ 59
def prefixEnd_417380 : Nat := 4983230072969 + 3 ^ 40 * 417380 * 2
def baseEnd_417380 : Nat := 190503604954384206693787

theorem tailTrace_417380 : CollatzResearch.WordTrace tailWord_417380 prefixEnd_417380 190503604954384206693787 := by
  unfold tailWord_417380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611549613955508836996797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10148732818607345115995729 7611549613955508836996797)
  ·
    refine ⟨2854331105233315813873799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7611549613955508836996797 2854331105233315813873799)
    ·
      refine ⟨4281496657849973720810699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854331105233315813873799 4281496657849973720810699)
      ·
        refine ⟨6422244986774960581216049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281496657849973720810699 6422244986774960581216049)
        ·
          refine ⟨4816683740081220435912037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422244986774960581216049 4816683740081220435912037)
          ·
            refine ⟨903128201265228831733507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4816683740081220435912037 903128201265228831733507)
            ·
              refine ⟨1354692301897843247600261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903128201265228831733507 1354692301897843247600261)
              ·
                refine ⟨254004806605845608925049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1354692301897843247600261 254004806605845608925049)
                ·
                  refine ⟨190503604954384206693787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254004806605845608925049 190503604954384206693787)
                  ·
                    rfl

theorem cell20_417380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_417380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417380 prefixEnd_417380 := by exact prefixLift 417380
  have htrace : WordTrace (prefixWord ++ tailWord_417380) baseStart_417380 baseEnd_417380 := by
    simpa [prefixWord, tailWord_417380, baseEnd_417380] using wordTrace_append hprefix tailTrace_417380
  have hstable : (prefixWord ++ tailWord_417380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417380).length < 2 ^ (prefixWord ++ tailWord_417380).sum := by decide
  have hdescent : baseEnd_417380 < baseStart_417380 := by decide
  rcases family_descends (prefixWord ++ tailWord_417380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417394 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_417394 : Nat := 118140960795 + 417394 * 2 ^ 59
def prefixEnd_417394 : Nat := 4983230072969 + 3 ^ 40 * 417394 * 2
def baseEnd_417394 : Nat := 190509994935862380227063

theorem tailTrace_417394 : CollatzResearch.WordTrace tailWord_417394 prefixEnd_417394 190509994935862380227063 := by
  unfold tailWord_417394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805902462465074516250809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10149073233240198710002157 3805902462465074516250809)
  ·
    refine ⟨2854426846848805887188107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3805902462465074516250809 2854426846848805887188107)
    ·
      refine ⟨4281640270273208830782161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854426846848805887188107 4281640270273208830782161)
      ·
        refine ⟨3211230202704906623086621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4281640270273208830782161 3211230202704906623086621)
        ·
          refine ⟨1204211326014339983657483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3211230202704906623086621 1204211326014339983657483)
          ·
            refine ⟨1806316989021509975486225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204211326014339983657483 1806316989021509975486225)
            ·
              refine ⟨1354737741766132481614669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806316989021509975486225 1354737741766132481614669)
              ·
                refine ⟨508026653162299680605501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354737741766132481614669 508026653162299680605501)
                ·
                  refine ⟨190509994935862380227063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508026653162299680605501 190509994935862380227063)
                  ·
                    rfl

theorem cell20_417394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_417394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417394 prefixEnd_417394 := by exact prefixLift 417394
  have htrace : WordTrace (prefixWord ++ tailWord_417394) baseStart_417394 baseEnd_417394 := by
    simpa [prefixWord, tailWord_417394, baseEnd_417394] using wordTrace_append hprefix tailTrace_417394
  have hstable : (prefixWord ++ tailWord_417394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417394).length < 2 ^ (prefixWord ++ tailWord_417394).sum := by decide
  have hdescent : baseEnd_417394 < baseStart_417394 := by decide
  rcases family_descends (prefixWord ++ tailWord_417394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417408 : List Nat := [2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_417408 : Nat := 118140960795 + 417408 * 2 ^ 59
def prefixEnd_417408 : Nat := 4983230072969 + 3 ^ 40 * 417408 * 2
def baseEnd_417408 : Nat := 63505461639113517920113

theorem tailTrace_417408 : CollatzResearch.WordTrace tailWord_417408 prefixEnd_417408 63505461639113517920113 := by
  unfold tailWord_417408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612060235904789228006439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10149413647873052304008585 7612060235904789228006439)
  ·
    refine ⟨11418090353857183842009659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7612060235904789228006439 11418090353857183842009659)
    ·
      refine ⟨17127135530785775763014489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11418090353857183842009659 17127135530785775763014489)
      ·
        refine ⟨12845351648089331822260867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17127135530785775763014489 12845351648089331822260867)
        ·
          refine ⟨19268027472133997733391301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12845351648089331822260867 19268027472133997733391301)
          ·
            refine ⟨3612755151025124575010869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19268027472133997733391301 3612755151025124575010869)
            ·
              refine ⟨338695795408605428907269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3612755151025124575010869 338695795408605428907269)
              ·
                refine ⟨63505461639113517920113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338695795408605428907269 63505461639113517920113)
                ·
                  rfl

theorem cell20_417408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_417408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417408 prefixEnd_417408 := by exact prefixLift 417408
  have htrace : WordTrace (prefixWord ++ tailWord_417408) baseStart_417408 baseEnd_417408 := by
    simpa [prefixWord, tailWord_417408, baseEnd_417408] using wordTrace_append hprefix tailTrace_417408
  have hstable : (prefixWord ++ tailWord_417408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417408).length < 2 ^ (prefixWord ++ tailWord_417408).sum := by decide
  have hdescent : baseEnd_417408 < baseStart_417408 := by decide
  rcases family_descends (prefixWord ++ tailWord_417408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417418 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_417418 : Nat := 118140960795 + 417418 * 2 ^ 59
def prefixEnd_417418 : Nat := 4983230072969 + 3 ^ 40 * 417418 * 2
def baseEnd_417418 : Nat := 190520949189824963426965

theorem tailTrace_417418 : CollatzResearch.WordTrace tailWord_417418 prefixEnd_417418 190520949189824963426965 := by
  unfold tailWord_417418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806121300443337540969227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10149656801182233442584605 3806121300443337540969227)
  ·
    refine ⟨5709181950665006311453841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806121300443337540969227 5709181950665006311453841)
    ·
      refine ⟨4281886462998754733590381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5709181950665006311453841 4281886462998754733590381)
      ·
        refine ⟨1605707423624533025096393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4281886462998754733590381 1605707423624533025096393)
        ·
          refine ⟨1204280567718399768822295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605707423624533025096393 1204280567718399768822295)
          ·
            refine ⟨1806420851577599653233443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204280567718399768822295 1806420851577599653233443)
            ·
              refine ⟨2709631277366399479850165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806420851577599653233443 2709631277366399479850165)
              ·
                refine ⟨254027932253099951235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2709631277366399479850165 254027932253099951235953)
                ·
                  refine ⟨190520949189824963426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254027932253099951235953 190520949189824963426965)
                  ·
                    rfl

theorem cell20_417418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_417418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417418 prefixEnd_417418 := by exact prefixLift 417418
  have htrace : WordTrace (prefixWord ++ tailWord_417418) baseStart_417418 baseEnd_417418 := by
    simpa [prefixWord, tailWord_417418, baseEnd_417418] using wordTrace_append hprefix tailTrace_417418
  have hstable : (prefixWord ++ tailWord_417418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417418).length < 2 ^ (prefixWord ++ tailWord_417418).sum := by decide
  have hdescent : baseEnd_417418 < baseStart_417418 := by decide
  rcases family_descends (prefixWord ++ tailWord_417418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417428 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_417428 : Nat := 118140960795 + 417428 * 2 ^ 59
def prefixEnd_417428 : Nat := 4983230072969 + 3 ^ 40 * 417428 * 2
def baseEnd_417428 : Nat := 190525513462309373093591

theorem tailTrace_417428 : CollatzResearch.WordTrace tailWord_417428 prefixEnd_417428 190525513462309373093591 := by
  unfold tailWord_417428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612424965868560935870469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10149899954491414581160625 7612424965868560935870469)
  ·
    refine ⟨1427329681100355175475713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7612424965868560935870469 1427329681100355175475713)
    ·
      refine ⟨1070497260825266381606785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427329681100355175475713 1070497260825266381606785)
      ·
        refine ⟨802872945618949786205089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070497260825266381606785 802872945618949786205089)
        ·
          refine ⟨602154709214212339653817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802872945618949786205089 602154709214212339653817)
          ·
            refine ⟨451616031910659254740363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602154709214212339653817 451616031910659254740363)
            ·
              refine ⟨677424047865988882110545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451616031910659254740363 677424047865988882110545)
              ·
                refine ⟨508068035899491661582909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677424047865988882110545 508068035899491661582909)
                ·
                  refine ⟨190525513462309373093591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508068035899491661582909 190525513462309373093591)
                  ·
                    rfl

theorem cell20_417428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_417428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417428 prefixEnd_417428 := by exact prefixLift 417428
  have htrace : WordTrace (prefixWord ++ tailWord_417428) baseStart_417428 baseEnd_417428 := by
    simpa [prefixWord, tailWord_417428, baseEnd_417428] using wordTrace_append hprefix tailTrace_417428
  have hstable : (prefixWord ++ tailWord_417428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417428).length < 2 ^ (prefixWord ++ tailWord_417428).sum := by decide
  have hdescent : baseEnd_417428 < baseStart_417428 := by decide
  rcases family_descends (prefixWord ++ tailWord_417428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417432 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_417432 : Nat := 118140960795 + 417432 * 2 ^ 59
def prefixEnd_417432 : Nat := 4983230072969 + 3 ^ 40 * 417432 * 2
def baseEnd_417432 : Nat := 190527339171303136960241

theorem tailTrace_417432 : CollatzResearch.WordTrace tailWord_417432 prefixEnd_417432 190527339171303136960241 := by
  unfold tailWord_417432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612497911861315277443275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10149997215815087036591033 7612497911861315277443275)
  ·
    refine ⟨11418746867791972916164913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7612497911861315277443275 11418746867791972916164913)
    ·
      refine ⟨8564060150843979687123685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11418746867791972916164913 8564060150843979687123685)
      ·
        refine ⟨1605761278283246191335691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8564060150843979687123685 1605761278283246191335691)
        ·
          refine ⟨2408641917424869287003537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605761278283246191335691 2408641917424869287003537)
          ·
            refine ⟨1806481438068651965252653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408641917424869287003537 1806481438068651965252653)
            ·
              refine ⟨677430539275744486969745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1806481438068651965252653 677430539275744486969745)
              ·
                refine ⟨508072904456808365227309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677430539275744486969745 508072904456808365227309)
                ·
                  refine ⟨190527339171303136960241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508072904456808365227309 190527339171303136960241)
                  ·
                    rfl

theorem cell20_417432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_417432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417432 prefixEnd_417432 := by exact prefixLift 417432
  have htrace : WordTrace (prefixWord ++ tailWord_417432) baseStart_417432 baseEnd_417432 := by
    simpa [prefixWord, tailWord_417432, baseEnd_417432] using wordTrace_append hprefix tailTrace_417432
  have hstable : (prefixWord ++ tailWord_417432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417432).length < 2 ^ (prefixWord ++ tailWord_417432).sum := by decide
  have hdescent : baseEnd_417432 < baseStart_417432 := by decide
  rcases family_descends (prefixWord ++ tailWord_417432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417463 : List Nat := [1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_417463 : Nat := 118140960795 + 417463 * 2 ^ 59
def prefixEnd_417463 : Nat := 4983230072969 + 3 ^ 40 * 417463 * 2
def baseEnd_417463 : Nat := 63513829472001602308927

theorem tailTrace_417463 : CollatzResearch.WordTrace tailWord_417463 prefixEnd_417463 63513829472001602308927 := by
  unfold tailWord_417463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226126486610322849265043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10150750991073548566176695 15226126486610322849265043)
  ·
    refine ⟨22839189729915484273897565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15226126486610322849265043 22839189729915484273897565)
    ·
      refine ⟨8564696148718306602711587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22839189729915484273897565 8564696148718306602711587)
      ·
        refine ⟨12847044223077459904067381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564696148718306602711587 12847044223077459904067381)
        ·
          refine ⟨1204410395913511866006317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12847044223077459904067381 1204410395913511866006317)
          ·
            refine ⟨451653898467566949752369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1204410395913511866006317 451653898467566949752369)
            ·
              refine ⟨338740423850675212314277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451653898467566949752369 338740423850675212314277)
              ·
                refine ⟨63513829472001602308927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338740423850675212314277 63513829472001602308927)
                ·
                  rfl

theorem cell20_417463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_417463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417463 prefixEnd_417463 := by exact prefixLift 417463
  have htrace : WordTrace (prefixWord ++ tailWord_417463) baseStart_417463 baseEnd_417463 := by
    simpa [prefixWord, tailWord_417463, baseEnd_417463] using wordTrace_append hprefix tailTrace_417463
  have hstable : (prefixWord ++ tailWord_417463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417463).length < 2 ^ (prefixWord ++ tailWord_417463).sum := by decide
  have hdescent : baseEnd_417463 < baseStart_417463 := by decide
  rcases family_descends (prefixWord ++ tailWord_417463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417543 : List Nat := [1, 1, 4, 4, 10]
def baseStart_417543 : Nat := 118140960795 + 417543 * 2 ^ 59
def prefixEnd_417543 : Nat := 4983230072969 + 3 ^ 40 * 417543 * 2
def baseEnd_417543 : Nat := 2352814846862717089627

theorem tailTrace_417543 : CollatzResearch.WordTrace tailWord_417543 prefixEnd_417543 2352814846862717089627 := by
  unfold tailWord_417543
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229044326320496512177283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10152696217546997674784855 15229044326320496512177283)
  ·
    refine ⟨22843566489480744768265925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15229044326320496512177283 22843566489480744768265925)
    ·
      refine ⟨4283168716777639644049861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22843566489480744768265925 4283168716777639644049861)
      ·
        refine ⟨803094134395807433259349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4283168716777639644049861 803094134395807433259349)
        ·
          refine ⟨2352814846862717089627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 803094134395807433259349 2352814846862717089627)
          ·
            rfl

theorem cell20_417543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 10].length) (baseStart_417543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417543 prefixEnd_417543 := by exact prefixLift 417543
  have htrace : WordTrace (prefixWord ++ tailWord_417543) baseStart_417543 baseEnd_417543 := by
    simpa [prefixWord, tailWord_417543, baseEnd_417543] using wordTrace_append hprefix tailTrace_417543
  have hstable : (prefixWord ++ tailWord_417543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417543).length < 2 ^ (prefixWord ++ tailWord_417543).sum := by decide
  have hdescent : baseEnd_417543 < baseStart_417543 := by decide
  rcases family_descends (prefixWord ++ tailWord_417543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417546 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_417546 : Nat := 118140960795 + 417546 * 2 ^ 59
def prefixEnd_417546 : Nat := 4983230072969 + 3 ^ 40 * 417546 * 2
def baseEnd_417546 : Nat := 190579371877625407159775

theorem tailTrace_417546 : CollatzResearch.WordTrace tailWord_417546 prefixEnd_417546 190579371877625407159775 := by
  unfold tailWord_417546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807288436327407006134123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10152769163539752016357661 3807288436327407006134123)
  ·
    refine ⟨5710932654491110509201185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807288436327407006134123 5710932654491110509201185)
    ·
      refine ⟨4283199490868332881900889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710932654491110509201185 4283199490868332881900889)
      ·
        refine ⟨3212399618151249661425667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283199490868332881900889 3212399618151249661425667)
        ·
          refine ⟨4818599427226874492138501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212399618151249661425667 4818599427226874492138501)
          ·
            refine ⟨903487392605038967275969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4818599427226874492138501 903487392605038967275969)
            ·
              refine ⟨677615544453779225456977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903487392605038967275969 677615544453779225456977)
              ·
                refine ⟨508211658340334419092733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677615544453779225456977 508211658340334419092733)
                ·
                  refine ⟨190579371877625407159775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508211658340334419092733 190579371877625407159775)
                  ·
                    rfl

theorem cell20_417546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_417546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417546 prefixEnd_417546 := by exact prefixLift 417546
  have htrace : WordTrace (prefixWord ++ tailWord_417546) baseStart_417546 baseEnd_417546 := by
    simpa [prefixWord, tailWord_417546, baseEnd_417546] using wordTrace_append hprefix tailTrace_417546
  have hstable : (prefixWord ++ tailWord_417546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417546).length < 2 ^ (prefixWord ++ tailWord_417546).sum := by decide
  have hdescent : baseEnd_417546 < baseStart_417546 := by decide
  rcases family_descends (prefixWord ++ tailWord_417546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417567 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_417567 : Nat := 118140960795 + 417567 * 2 ^ 59
def prefixEnd_417567 : Nat := 4983230072969 + 3 ^ 40 * 417567 * 2
def baseEnd_417567 : Nat := 190588956849842667459689

theorem tailTrace_417567 : CollatzResearch.WordTrace tailWord_417567 prefixEnd_417567 190588956849842667459689 := by
  unfold tailWord_417567
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229919678233548611050955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10153279785489032407367303 15229919678233548611050955)
  ·
    refine ⟨22844879517350322916576433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15229919678233548611050955 22844879517350322916576433)
    ·
      refine ⟨17133659638012742187432325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22844879517350322916576433 17133659638012742187432325)
      ·
        refine ⟨3212561182127389160143561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17133659638012742187432325 3212561182127389160143561)
        ·
          refine ⟨2409420886595541870107671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212561182127389160143561 2409420886595541870107671)
          ·
            refine ⟨3614131329893312805161507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409420886595541870107671 3614131329893312805161507)
            ·
              refine ⟨5421196994839969207742261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614131329893312805161507 5421196994839969207742261)
              ·
                refine ⟨508237218266247113225837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5421196994839969207742261 508237218266247113225837)
                ·
                  refine ⟨190588956849842667459689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508237218266247113225837 190588956849842667459689)
                  ·
                    rfl

theorem cell20_417567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_417567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417567 prefixEnd_417567 := by exact prefixLift 417567
  have htrace : WordTrace (prefixWord ++ tailWord_417567) baseStart_417567 baseEnd_417567 := by
    simpa [prefixWord, tailWord_417567, baseEnd_417567] using wordTrace_append hprefix tailTrace_417567
  have hstable : (prefixWord ++ tailWord_417567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417567).length < 2 ^ (prefixWord ++ tailWord_417567).sum := by decide
  have hdescent : baseEnd_417567 < baseStart_417567 := by decide
  rcases family_descends (prefixWord ++ tailWord_417567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417598 : List Nat := [4, 2, 1, 2, 2, 2, 7]
def baseStart_417598 : Nat := 118140960795 + 417598 * 2 ^ 59
def prefixEnd_417598 : Nat := 4983230072969 + 3 ^ 40 * 417598 * 2
def baseEnd_417598 : Nat := 21178122899393815269581

theorem tailTrace_417598 : CollatzResearch.WordTrace tailWord_417598 prefixEnd_417598 21178122899393815269581 := by
  unfold tailWord_417598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903881292640155113178681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10154033560747493936952965 1903881292640155113178681)
  ·
    refine ⟨1427910969480116334884011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1903881292640155113178681 1427910969480116334884011)
    ·
      refine ⟨2141866454220174502326017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427910969480116334884011 2141866454220174502326017)
      ·
        refine ⟨1606399840665130876744513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141866454220174502326017 1606399840665130876744513)
        ·
          refine ⟨1204799880498848157558385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606399840665130876744513 1204799880498848157558385)
          ·
            refine ⟨903599910374136118168789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204799880498848157558385 903599910374136118168789)
            ·
              refine ⟨21178122899393815269581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 903599910374136118168789 21178122899393815269581)
              ·
                rfl

theorem cell20_417598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_417598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417598 prefixEnd_417598 := by exact prefixLift 417598
  have htrace : WordTrace (prefixWord ++ tailWord_417598) baseStart_417598 baseEnd_417598 := by
    simpa [prefixWord, tailWord_417598, baseEnd_417598] using wordTrace_append hprefix tailTrace_417598
  have hstable : (prefixWord ++ tailWord_417598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417598).length < 2 ^ (prefixWord ++ tailWord_417598).sum := by decide
  have hdescent : baseEnd_417598 < baseStart_417598 := by decide
  rcases family_descends (prefixWord ++ tailWord_417598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417636 : List Nat := [2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_417636 : Nat := 118140960795 + 417636 * 2 ^ 59
def prefixEnd_417636 : Nat := 4983230072969 + 3 ^ 40 * 417636 * 2
def baseEnd_417636 : Nat := 63540150109995031386469

theorem tailTrace_417636 : CollatzResearch.WordTrace tailWord_417636 prefixEnd_417636 63540150109995031386469 := by
  unfold tailWord_417636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616218157491786697656381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10154957543322382263541841 7616218157491786697656381)
  ·
    refine ⟨2856081809059420011621143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7616218157491786697656381 2856081809059420011621143)
    ·
      refine ⟨4284122713589130017431715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2856081809059420011621143 4284122713589130017431715)
      ·
        refine ⟨6426184070383695026147573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284122713589130017431715 6426184070383695026147573)
        ·
          refine ⟨602454756598471408701335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6426184070383695026147573 602454756598471408701335)
          ·
            refine ⟨903682134897707113052003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602454756598471408701335 903682134897707113052003)
            ·
              refine ⟨1355523202346560669578005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903682134897707113052003 1355523202346560669578005)
              ·
                refine ⟨63540150109995031386469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1355523202346560669578005 63540150109995031386469)
                ·
                  rfl

theorem cell20_417636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_417636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417636 prefixEnd_417636 := by exact prefixLift 417636
  have htrace : WordTrace (prefixWord ++ tailWord_417636) baseStart_417636 baseEnd_417636 := by
    simpa [prefixWord, tailWord_417636, baseEnd_417636] using wordTrace_append hprefix tailTrace_417636
  have hstable : (prefixWord ++ tailWord_417636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417636).length < 2 ^ (prefixWord ++ tailWord_417636).sum := by decide
  have hdescent : baseEnd_417636 < baseStart_417636 := by decide
  rcases family_descends (prefixWord ++ tailWord_417636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417642 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_417642 : Nat := 118140960795 + 417642 * 2 ^ 59
def prefixEnd_417642 : Nat := 4983230072969 + 3 ^ 40 * 417642 * 2
def baseEnd_417642 : Nat := 190623188893475739959383

theorem tailTrace_417642 : CollatzResearch.WordTrace tailWord_417642 prefixEnd_417642 190623188893475739959383 := by
  unfold tailWord_417642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808163788240459105007795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10155103435307890946687453 3808163788240459105007795)
  ·
    refine ⟨5712245682360688657511693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808163788240459105007795 5712245682360688657511693)
    ·
      refine ⟨2142092130885258246566885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5712245682360688657511693 2142092130885258246566885)
      ·
        refine ⟨401642274540985921231291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2142092130885258246566885 401642274540985921231291)
        ·
          refine ⟨602463411811478881846937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401642274540985921231291 602463411811478881846937)
          ·
            refine ⟨451847558858609161385203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602463411811478881846937 451847558858609161385203)
            ·
              refine ⟨677771338287913742077805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451847558858609161385203 677771338287913742077805)
              ·
                refine ⟨254164251857967653279177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 677771338287913742077805 254164251857967653279177)
                ·
                  refine ⟨190623188893475739959383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254164251857967653279177 190623188893475739959383)
                  ·
                    rfl

theorem cell20_417642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_417642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417642 prefixEnd_417642 := by exact prefixLift 417642
  have htrace : WordTrace (prefixWord ++ tailWord_417642) baseStart_417642 baseEnd_417642 := by
    simpa [prefixWord, tailWord_417642, baseEnd_417642] using wordTrace_append hprefix tailTrace_417642
  have hstable : (prefixWord ++ tailWord_417642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417642).length < 2 ^ (prefixWord ++ tailWord_417642).sum := by decide
  have hdescent : baseEnd_417642 < baseStart_417642 := by decide
  rcases family_descends (prefixWord ++ tailWord_417642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417664 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_417664 : Nat := 118140960795 + 417664 * 2 ^ 59
def prefixEnd_417664 : Nat := 4983230072969 + 3 ^ 40 * 417664 * 2
def baseEnd_417664 : Nat := 190633230292941441225959

theorem tailTrace_417664 : CollatzResearch.WordTrace tailWord_417664 prefixEnd_417664 190633230292941441225959 := by
  unfold tailWord_417664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616728779441067088666023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10155638372588089451554697 7616728779441067088666023)
  ·
    refine ⟨11425093169161600632999035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616728779441067088666023 11425093169161600632999035)
    ·
      refine ⟨17137639753742400949498553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11425093169161600632999035 17137639753742400949498553)
      ·
        refine ⟨12853229815306800712123915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17137639753742400949498553 12853229815306800712123915)
        ·
          refine ⟨19279844722960201068185873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853229815306800712123915 19279844722960201068185873)
          ·
            refine ⟨14459883542220150801139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19279844722960201068185873 14459883542220150801139405)
            ·
              refine ⟨5422456328332556550427277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14459883542220150801139405 5422456328332556550427277)
              ·
                refine ⟨2033421123124708706410229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5422456328332556550427277 2033421123124708706410229)
                ·
                  refine ⟨190633230292941441225959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033421123124708706410229 190633230292941441225959)
                  ·
                    rfl

theorem cell20_417664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_417664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417664 prefixEnd_417664 := by exact prefixLift 417664
  have htrace : WordTrace (prefixWord ++ tailWord_417664) baseStart_417664 baseEnd_417664 := by
    simpa [prefixWord, tailWord_417664, baseEnd_417664] using wordTrace_append hprefix tailTrace_417664
  have hstable : (prefixWord ++ tailWord_417664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417664).length < 2 ^ (prefixWord ++ tailWord_417664).sum := by decide
  have hdescent : baseEnd_417664 < baseStart_417664 := by decide
  rcases family_descends (prefixWord ++ tailWord_417664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417667 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_417667 : Nat := 118140960795 + 417667 * 2 ^ 59
def prefixEnd_417667 : Nat := 4983230072969 + 3 ^ 40 * 417667 * 2
def baseEnd_417667 : Nat := 190634599574686764125947

theorem tailTrace_417667 : CollatzResearch.WordTrace tailWord_417667 prefixEnd_417667 190634599574686764125947 := by
  unfold tailWord_417667
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233566977871265689691255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10155711318580843793127503 15233566977871265689691255)
  ·
    refine ⟨22850350466806898534536883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233566977871265689691255 22850350466806898534536883)
    ·
      refine ⟨34275525700210347801805325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22850350466806898534536883 34275525700210347801805325)
      ·
        refine ⟨12853322137578880425676997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34275525700210347801805325 12853322137578880425676997)
        ·
          refine ⟨2409997900796040079814437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12853322137578880425676997 2409997900796040079814437)
          ·
            refine ⟨451874606399257514965207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2409997900796040079814437 451874606399257514965207)
            ·
              refine ⟨677811909598886272447811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451874606399257514965207 677811909598886272447811)
              ·
                refine ⟨1016717864398329408671717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677811909598886272447811 1016717864398329408671717)
                ·
                  refine ⟨190634599574686764125947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016717864398329408671717 190634599574686764125947)
                  ·
                    rfl

theorem cell20_417667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_417667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417667 prefixEnd_417667 := by exact prefixLift 417667
  have htrace : WordTrace (prefixWord ++ tailWord_417667) baseStart_417667 baseEnd_417667 := by
    simpa [prefixWord, tailWord_417667, baseEnd_417667] using wordTrace_append hprefix tailTrace_417667
  have hstable : (prefixWord ++ tailWord_417667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417667).length < 2 ^ (prefixWord ++ tailWord_417667).sum := by decide
  have hdescent : baseEnd_417667 < baseStart_417667 := by decide
  rcases family_descends (prefixWord ++ tailWord_417667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417774 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_417774 : Nat := 118140960795 + 417774 * 2 ^ 59
def prefixEnd_417774 : Nat := 4983230072969 + 3 ^ 40 * 417774 * 2
def baseEnd_417774 : Nat := 190683437290269947558843

theorem tailTrace_417774 : CollatzResearch.WordTrace tailWord_417774 prefixEnd_417774 190683437290269947558843 := by
  unfold tailWord_417774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904683698560452870479547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10158313058989081975890917 1904683698560452870479547)
  ·
    refine ⟨2857025547840679305719321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904683698560452870479547 2857025547840679305719321)
    ·
      refine ⟨2142769160880509479289491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2857025547840679305719321 2142769160880509479289491)
      ·
        refine ⟨3214153741320764218934237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142769160880509479289491 3214153741320764218934237)
        ·
          refine ⟨1205307652995286582100339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3214153741320764218934237 1205307652995286582100339)
          ·
            refine ⟨1807961479492929873150509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205307652995286582100339 1807961479492929873150509)
            ·
              refine ⟨677985554809848702431441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807961479492929873150509 677985554809848702431441)
              ·
                refine ⟨508489166107386526823581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677985554809848702431441 508489166107386526823581)
                ·
                  refine ⟨190683437290269947558843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508489166107386526823581 190683437290269947558843)
                  ·
                    rfl

theorem cell20_417774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_417774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417774 prefixEnd_417774 := by exact prefixLift 417774
  have htrace : WordTrace (prefixWord ++ tailWord_417774) baseStart_417774 baseEnd_417774 := by
    simpa [prefixWord, tailWord_417774, baseEnd_417774] using wordTrace_append hprefix tailTrace_417774
  have hstable : (prefixWord ++ tailWord_417774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417774).length < 2 ^ (prefixWord ++ tailWord_417774).sum := by decide
  have hdescent : baseEnd_417774 < baseStart_417774 := by decide
  rcases family_descends (prefixWord ++ tailWord_417774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417815 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 2]
def baseStart_417815 : Nat := 118140960795 + 417815 * 2 ^ 59
def prefixEnd_417815 : Nat := 4983230072969 + 3 ^ 40 * 417815 * 2
def baseEnd_417815 : Nat := 190702150807456027192009

theorem tailTrace_417815 : CollatzResearch.WordTrace tailWord_417815 prefixEnd_417815 190702150807456027192009 := by
  unfold tailWord_417815
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238964981335086966078899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10159309987556724644052599 15238964981335086966078899)
  ·
    refine ⟨22858447472002630449118349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15238964981335086966078899 22858447472002630449118349)
    ·
      refine ⟨8571917802000986418419381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22858447472002630449118349 8571917802000986418419381)
      ·
        refine ⟨803617293937592476726817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8571917802000986418419381 803617293937592476726817)
        ·
          refine ⟨602712970453194357545113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803617293937592476726817 602712970453194357545113)
          ·
            refine ⟨452034727839895768158835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602712970453194357545113 452034727839895768158835)
            ·
              refine ⟨678052091759843652238253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452034727839895768158835 678052091759843652238253)
              ·
                refine ⟨254269534409941369589345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678052091759843652238253 254269534409941369589345)
                ·
                  refine ⟨190702150807456027192009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254269534409941369589345 190702150807456027192009)
                  ·
                    rfl

theorem cell20_417815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2].length) (baseStart_417815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417815 prefixEnd_417815 := by exact prefixLift 417815
  have htrace : WordTrace (prefixWord ++ tailWord_417815) baseStart_417815 baseEnd_417815 := by
    simpa [prefixWord, tailWord_417815, baseEnd_417815] using wordTrace_append hprefix tailTrace_417815
  have hstable : (prefixWord ++ tailWord_417815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417815).length < 2 ^ (prefixWord ++ tailWord_417815).sum := by decide
  have hdescent : baseEnd_417815 < baseStart_417815 := by decide
  rcases family_descends (prefixWord ++ tailWord_417815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417816 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_417816 : Nat := 118140960795 + 417816 * 2 ^ 59
def prefixEnd_417816 : Nat := 4983230072969 + 3 ^ 40 * 417816 * 2
def baseEnd_417816 : Nat := 190702607234704468158671

theorem tailTrace_417816 : CollatzResearch.WordTrace tailWord_417816 prefixEnd_417816 190702607234704468158671 := by
  unfold tailWord_417816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619500727165732068432651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10159334302887642757910201 7619500727165732068432651)
  ·
    refine ⟨11429251090748598102648977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619500727165732068432651 11429251090748598102648977)
    ·
      refine ⟨8571938318061448576986733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11429251090748598102648977 8571938318061448576986733)
      ·
        refine ⟨3214476869273043216370025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8571938318061448576986733 3214476869273043216370025)
        ·
          refine ⟨2410857651954782412277519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214476869273043216370025 2410857651954782412277519)
          ·
            refine ⟨3616286477932173618416279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410857651954782412277519 3616286477932173618416279)
            ·
              refine ⟨5424429716898260427624419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616286477932173618416279 5424429716898260427624419)
              ·
                refine ⟨8136644575347390641436629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424429716898260427624419 8136644575347390641436629)
                ·
                  refine ⟨190702607234704468158671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8136644575347390641436629 190702607234704468158671)
                  ·
                    rfl

theorem cell20_417816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_417816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417816 prefixEnd_417816 := by exact prefixLift 417816
  have htrace : WordTrace (prefixWord ++ tailWord_417816) baseStart_417816 baseEnd_417816 := by
    simpa [prefixWord, tailWord_417816, baseEnd_417816] using wordTrace_append hprefix tailTrace_417816
  have hstable : (prefixWord ++ tailWord_417816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417816).length < 2 ^ (prefixWord ++ tailWord_417816).sum := by decide
  have hdescent : baseEnd_417816 < baseStart_417816 := by decide
  rcases family_descends (prefixWord ++ tailWord_417816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417832 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_417832 : Nat := 118140960795 + 417832 * 2 ^ 59
def prefixEnd_417832 : Nat := 4983230072969 + 3 ^ 40 * 417832 * 2
def baseEnd_417832 : Nat := 190709910070679523625273

theorem tailTrace_417832 : CollatzResearch.WordTrace tailWord_417832 prefixEnd_417832 190709910070679523625273 := by
  unfold tailWord_417832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619792511136749434723875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10159723348182332579631833 7619792511136749434723875)
  ·
    refine ⟨11429688766705124152085813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619792511136749434723875 11429688766705124152085813)
    ·
      refine ⟨1071533321878605389258045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11429688766705124152085813 1071533321878605389258045)
      ·
        refine ⟨401824995704477020971767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1071533321878605389258045 401824995704477020971767)
        ·
          refine ⟨602737493556715531457651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401824995704477020971767 602737493556715531457651)
          ·
            refine ⟨904106240335073297186477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602737493556715531457651 904106240335073297186477)
            ·
              refine ⟨339039840125652486444929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904106240335073297186477 339039840125652486444929)
              ·
                refine ⟨254279880094239364833697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339039840125652486444929 254279880094239364833697)
                ·
                  refine ⟨190709910070679523625273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254279880094239364833697 190709910070679523625273)
                  ·
                    rfl

theorem cell20_417832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_417832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417832 prefixEnd_417832 := by exact prefixLift 417832
  have htrace : WordTrace (prefixWord ++ tailWord_417832) baseStart_417832 baseEnd_417832 := by
    simpa [prefixWord, tailWord_417832, baseEnd_417832] using wordTrace_append hprefix tailTrace_417832
  have hstable : (prefixWord ++ tailWord_417832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417832).length < 2 ^ (prefixWord ++ tailWord_417832).sum := by decide
  have hdescent : baseEnd_417832 < baseStart_417832 := by decide
  rcases family_descends (prefixWord ++ tailWord_417832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417840 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_417840 : Nat := 118140960795 + 417840 * 2 ^ 59
def prefixEnd_417840 : Nat := 4983230072969 + 3 ^ 40 * 417840 * 2
def baseEnd_417840 : Nat := 190713561488667051358573

theorem tailTrace_417840 : CollatzResearch.WordTrace tailWord_417840 prefixEnd_417840 190713561488667051358573 := by
  unfold tailWord_417840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619938403122258117869487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10159917870829677490492649 7619938403122258117869487)
  ·
    refine ⟨11429907604683387176804231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619938403122258117869487 11429907604683387176804231)
    ·
      refine ⟨17144861407025080765206347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429907604683387176804231 17144861407025080765206347)
      ·
        refine ⟨25717292110537621147809521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144861407025080765206347 25717292110537621147809521)
        ·
          refine ⟨19287969082903215860857141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25717292110537621147809521 19287969082903215860857141)
          ·
            refine ⟨1808247101522176486955357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19287969082903215860857141 1808247101522176486955357)
            ·
              refine ⟨678092663070816182608259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808247101522176486955357 678092663070816182608259)
              ·
                refine ⟨1017138994606224273912389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678092663070816182608259 1017138994606224273912389)
                ·
                  refine ⟨190713561488667051358573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017138994606224273912389 190713561488667051358573)
                  ·
                    rfl

theorem cell20_417840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_417840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417840 prefixEnd_417840 := by exact prefixLift 417840
  have htrace : WordTrace (prefixWord ++ tailWord_417840) baseStart_417840 baseEnd_417840 := by
    simpa [prefixWord, tailWord_417840, baseEnd_417840] using wordTrace_append hprefix tailTrace_417840
  have hstable : (prefixWord ++ tailWord_417840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417840).length < 2 ^ (prefixWord ++ tailWord_417840).sum := by decide
  have hdescent : baseEnd_417840 < baseStart_417840 := by decide
  rcases family_descends (prefixWord ++ tailWord_417840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417861 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_417861 : Nat := 118140960795 + 417861 * 2 ^ 59
def prefixEnd_417861 : Nat := 4983230072969 + 3 ^ 40 * 417861 * 2
def baseEnd_417861 : Nat := 190723146460884311658487

theorem tailTrace_417861 : CollatzResearch.WordTrace tailWord_417861 prefixEnd_417861 190723146460884311658487 := by
  unfold tailWord_417861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240642739168436822253437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10160428492778957881502291 15240642739168436822253437)
  ·
    refine ⟨5715241027188163808345039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15240642739168436822253437 5715241027188163808345039)
    ·
      refine ⟨8572861540782245712517559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715241027188163808345039 8572861540782245712517559)
      ·
        refine ⟨12859292311173368568776339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572861540782245712517559 12859292311173368568776339)
        ·
          refine ⟨19288938466760052853164509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859292311173368568776339 19288938466760052853164509)
          ·
            refine ⟨7233351925035019819936691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19288938466760052853164509 7233351925035019819936691)
            ·
              refine ⟨10850027887552529729905037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233351925035019819936691 10850027887552529729905037)
              ·
                refine ⟨4068760457832198648714389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10850027887552529729905037 4068760457832198648714389)
                ·
                  refine ⟨190723146460884311658487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4068760457832198648714389 190723146460884311658487)
                  ·
                    rfl

theorem cell20_417861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_417861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417861 prefixEnd_417861 := by exact prefixLift 417861
  have htrace : WordTrace (prefixWord ++ tailWord_417861) baseStart_417861 baseEnd_417861 := by
    simpa [prefixWord, tailWord_417861, baseEnd_417861] using wordTrace_append hprefix tailTrace_417861
  have hstable : (prefixWord ++ tailWord_417861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417861).length < 2 ^ (prefixWord ++ tailWord_417861).sum := by decide
  have hdescent : baseEnd_417861 < baseStart_417861 := by decide
  rcases family_descends (prefixWord ++ tailWord_417861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417892 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_417892 : Nat := 118140960795 + 417892 * 2 ^ 59
def prefixEnd_417892 : Nat := 4983230072969 + 3 ^ 40 * 417892 * 2
def baseEnd_417892 : Nat := 190737295705585981625027

theorem tailTrace_417892 : CollatzResearch.WordTrace tailWord_417892 prefixEnd_417892 190737295705585981625027 := by
  unfold tailWord_417892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620886701028064558315965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10161182268037419411087953 7620886701028064558315965)
  ·
    refine ⟨2857832512885524209368487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7620886701028064558315965 2857832512885524209368487)
    ·
      refine ⟨4286748769328286314052731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2857832512885524209368487 4286748769328286314052731)
      ·
        refine ⟨6430123153992429471079097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286748769328286314052731 6430123153992429471079097)
        ·
          refine ⟨4822592365494322103309323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6430123153992429471079097 4822592365494322103309323)
          ·
            refine ⟨7233888548241483154963985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822592365494322103309323 7233888548241483154963985)
            ·
              refine ⟨5425416411181112366222989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233888548241483154963985 5425416411181112366222989)
              ·
                refine ⟨2034531154192917137333621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425416411181112366222989 2034531154192917137333621)
                ·
                  refine ⟨190737295705585981625027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034531154192917137333621 190737295705585981625027)
                  ·
                    rfl

theorem cell20_417892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_417892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417892 prefixEnd_417892 := by exact prefixLift 417892
  have htrace : WordTrace (prefixWord ++ tailWord_417892) baseStart_417892 baseEnd_417892 := by
    simpa [prefixWord, tailWord_417892, baseEnd_417892] using wordTrace_append hprefix tailTrace_417892
  have hstable : (prefixWord ++ tailWord_417892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417892).length < 2 ^ (prefixWord ++ tailWord_417892).sum := by decide
  have hdescent : baseEnd_417892 < baseStart_417892 := by decide
  rcases family_descends (prefixWord ++ tailWord_417892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417895 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 2]
def baseStart_417895 : Nat := 118140960795 + 417895 * 2 ^ 59
def prefixEnd_417895 : Nat := 4983230072969 + 3 ^ 40 * 417895 * 2
def baseEnd_417895 : Nat := 190738664987331304525015

theorem tailTrace_417895 : CollatzResearch.WordTrace tailWord_417895 prefixEnd_417895 190738664987331304525015 := by
  unfold tailWord_417895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15241882821045260628991139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10161255214030173752660759 15241882821045260628991139)
  ·
    refine ⟨22862824231567890943486709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15241882821045260628991139 22862824231567890943486709)
    ·
      refine ⟨2143389771709489775951879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22862824231567890943486709 2143389771709489775951879)
      ·
        refine ⟨3215084657564234663927819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143389771709489775951879 3215084657564234663927819)
        ·
          refine ⟨4822626986346351995891729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215084657564234663927819 4822626986346351995891729)
          ·
            refine ⟨3616970239759763996918797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4822626986346351995891729 3616970239759763996918797)
            ·
              refine ⟨1356363839909911498844549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3616970239759763996918797 1356363839909911498844549)
              ·
                refine ⟨254318219983108406033353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1356363839909911498844549 254318219983108406033353)
                ·
                  refine ⟨190738664987331304525015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254318219983108406033353 190738664987331304525015)
                  ·
                    rfl

theorem cell20_417895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 2].length) (baseStart_417895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417895 prefixEnd_417895 := by exact prefixLift 417895
  have htrace : WordTrace (prefixWord ++ tailWord_417895) baseStart_417895 baseEnd_417895 := by
    simpa [prefixWord, tailWord_417895, baseEnd_417895] using wordTrace_append hprefix tailTrace_417895
  have hstable : (prefixWord ++ tailWord_417895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417895).length < 2 ^ (prefixWord ++ tailWord_417895).sum := by decide
  have hdescent : baseEnd_417895 < baseStart_417895 := by decide
  rcases family_descends (prefixWord ++ tailWord_417895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417916 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_417916 : Nat := 118140960795 + 417916 * 2 ^ 59
def prefixEnd_417916 : Nat := 4983230072969 + 3 ^ 40 * 417916 * 2
def baseEnd_417916 : Nat := 190748249959548564824929

theorem tailTrace_417916 : CollatzResearch.WordTrace tailWord_417916 prefixEnd_417916 190748249959548564824929 := by
  unfold tailWord_417916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621324376984590607752801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10161765835979454143670401 7621324376984590607752801)
  ·
    refine ⟨5715993282738442955814601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7621324376984590607752801 5715993282738442955814601)
    ·
      refine ⟨4286994962053832216860951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5715993282738442955814601 4286994962053832216860951)
      ·
        refine ⟨6430492443080748325291427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286994962053832216860951 6430492443080748325291427)
        ·
          refine ⟨9645738664621122487937141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430492443080748325291427 9645738664621122487937141)
          ·
            refine ⟨904287999808230233244107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9645738664621122487937141 904287999808230233244107)
            ·
              refine ⟨1356431999712345349866161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904287999808230233244107 1356431999712345349866161)
              ·
                refine ⟨1017323999784259012399621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356431999712345349866161 1017323999784259012399621)
                ·
                  refine ⟨190748249959548564824929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017323999784259012399621 190748249959548564824929)
                  ·
                    rfl

theorem cell20_417916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_417916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417916 prefixEnd_417916 := by exact prefixLift 417916
  have htrace : WordTrace (prefixWord ++ tailWord_417916) baseStart_417916 baseEnd_417916 := by
    simpa [prefixWord, tailWord_417916, baseEnd_417916] using wordTrace_append hprefix tailTrace_417916
  have hstable : (prefixWord ++ tailWord_417916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417916).length < 2 ^ (prefixWord ++ tailWord_417916).sum := by decide
  have hdescent : baseEnd_417916 < baseStart_417916 := by decide
  rcases family_descends (prefixWord ++ tailWord_417916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417943 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 3]
def baseStart_417943 : Nat := 118140960795 + 417943 * 2 ^ 59
def prefixEnd_417943 : Nat := 4983230072969 + 3 ^ 40 * 417943 * 2
def baseEnd_417943 : Nat := 190760573495256470924819

theorem tailTrace_417943 : CollatzResearch.WordTrace tailWord_417943 prefixEnd_417943 190760573495256470924819 := by
  unfold tailWord_417943
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243633524871364826738483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10162422349914243217825655 15243633524871364826738483)
  ·
    refine ⟨22865450287307047240107725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15243633524871364826738483 22865450287307047240107725)
    ·
      refine ⟨8574543857740142715040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22865450287307047240107725 8574543857740142715040397)
      ·
        refine ⟨3215453946652553518140149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8574543857740142715040397 3215453946652553518140149)
        ·
          refine ⟨301448807498676892325639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3215453946652553518140149 301448807498676892325639)
          ·
            refine ⟨452173211248015338488459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301448807498676892325639 452173211248015338488459)
            ·
              refine ⟨678259816872023007732689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452173211248015338488459 678259816872023007732689)
              ·
                refine ⟨508694862654017255799517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678259816872023007732689 508694862654017255799517)
                ·
                  refine ⟨190760573495256470924819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508694862654017255799517 190760573495256470924819)
                  ·
                    rfl

theorem cell20_417943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3].length) (baseStart_417943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417943 prefixEnd_417943 := by exact prefixLift 417943
  have htrace : WordTrace (prefixWord ++ tailWord_417943) baseStart_417943 baseEnd_417943 := by
    simpa [prefixWord, tailWord_417943, baseEnd_417943] using wordTrace_append hprefix tailTrace_417943
  have hstable : (prefixWord ++ tailWord_417943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417943).length < 2 ^ (prefixWord ++ tailWord_417943).sum := by decide
  have hdescent : baseEnd_417943 < baseStart_417943 := by decide
  rcases family_descends (prefixWord ++ tailWord_417943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417950 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_417950 : Nat := 118140960795 + 417950 * 2 ^ 59
def prefixEnd_417950 : Nat := 4983230072969 + 3 ^ 40 * 417950 * 2
def baseEnd_417950 : Nat := 190763768485995557691457

theorem tailTrace_417950 : CollatzResearch.WordTrace tailWord_417950 prefixEnd_417950 190763768485995557691457 := by
  unfold tailWord_417950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905486104480750627780413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10162592557230670014828869 1905486104480750627780413)
  ·
    refine ⟨714557289180281485417655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1905486104480750627780413 714557289180281485417655)
    ·
      refine ⟨1071835933770422228126483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714557289180281485417655 1071835933770422228126483)
      ·
        refine ⟨1607753900655633342189725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071835933770422228126483 1607753900655633342189725)
        ·
          refine ⟨602907712745862503321147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1607753900655633342189725 602907712745862503321147)
          ·
            refine ⟨904361569118793754981721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602907712745862503321147 904361569118793754981721)
            ·
              refine ⟨678271176839095316236291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904361569118793754981721 678271176839095316236291)
              ·
                refine ⟨1017406765258642974354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678271176839095316236291 1017406765258642974354437)
                ·
                  refine ⟨190763768485995557691457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017406765258642974354437 190763768485995557691457)
                  ·
                    rfl

theorem cell20_417950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_417950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417950 prefixEnd_417950 := by exact prefixLift 417950
  have htrace : WordTrace (prefixWord ++ tailWord_417950) baseStart_417950 baseEnd_417950 := by
    simpa [prefixWord, tailWord_417950, baseEnd_417950] using wordTrace_append hprefix tailTrace_417950
  have hstable : (prefixWord ++ tailWord_417950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417950).length < 2 ^ (prefixWord ++ tailWord_417950).sum := by decide
  have hdescent : baseEnd_417950 < baseStart_417950 := by decide
  rcases family_descends (prefixWord ++ tailWord_417950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417988 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_417988 : Nat := 118140960795 + 417988 * 2 ^ 59
def prefixEnd_417988 : Nat := 4983230072969 + 3 ^ 40 * 417988 * 2
def baseEnd_417988 : Nat := 190781112721436314424635

theorem tailTrace_417988 : CollatzResearch.WordTrace tailWord_417988 prefixEnd_417988 190781112721436314424635 := by
  unfold tailWord_417988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622637404854168756063309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10163516539805558341417745 7622637404854168756063309)
  ·
    refine ⟨2858489026820313283523741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7622637404854168756063309 2858489026820313283523741)
    ·
      refine ⟨1071933385057617481321403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2858489026820313283523741 1071933385057617481321403)
      ·
        refine ⟨1607900077586426221982105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071933385057617481321403 1607900077586426221982105)
        ·
          refine ⟨1205925058189819666486579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607900077586426221982105 1205925058189819666486579)
          ·
            refine ⟨1808887587284729499729869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205925058189819666486579 1808887587284729499729869)
            ·
              refine ⟨678332845231773562398701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808887587284729499729869 678332845231773562398701)
              ·
                refine ⟨254374816961915085899513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678332845231773562398701 254374816961915085899513)
                ·
                  refine ⟨190781112721436314424635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254374816961915085899513 190781112721436314424635)
                  ·
                    rfl

theorem cell20_417988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_417988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_417988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_417988 prefixEnd_417988 := by exact prefixLift 417988
  have htrace : WordTrace (prefixWord ++ tailWord_417988) baseStart_417988 baseEnd_417988 := by
    simpa [prefixWord, tailWord_417988, baseEnd_417988] using wordTrace_append hprefix tailTrace_417988
  have hstable : (prefixWord ++ tailWord_417988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417988).length < 2 ^ (prefixWord ++ tailWord_417988).sum := by decide
  have hdescent : baseEnd_417988 < baseStart_417988 := by decide
  rcases family_descends (prefixWord ++ tailWord_417988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418005 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 2]
def baseStart_418005 : Nat := 118140960795 + 418005 * 2 ^ 59
def prefixEnd_418005 : Nat := 4983230072969 + 3 ^ 40 * 418005 * 2
def baseEnd_418005 : Nat := 190788871984659810857899

theorem tailTrace_418005 : CollatzResearch.WordTrace tailWord_418005 prefixEnd_418005 190788871984659810857899 := by
  unfold tailWord_418005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15245894850646749415495469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10163929900431166276996979 15245894850646749415495469)
  ·
    refine ⟨5717210568992531030810801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15245894850646749415495469 5717210568992531030810801)
    ·
      refine ⟨4287907926744398273108101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5717210568992531030810801 4287907926744398273108101)
      ·
        refine ⟨803982736264574676207769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4287907926744398273108101 803982736264574676207769)
        ·
          refine ⟨602987052198431007155827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803982736264574676207769 602987052198431007155827)
          ·
            refine ⟨904480578297646510733741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602987052198431007155827 904480578297646510733741)
            ·
              refine ⟨339180216861617441525153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904480578297646510733741 339180216861617441525153)
              ·
                refine ⟨254385162646213081143865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339180216861617441525153 254385162646213081143865)
                ·
                  refine ⟨190788871984659810857899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254385162646213081143865 190788871984659810857899)
                  ·
                    rfl

theorem cell20_418005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_418005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418005 prefixEnd_418005 := by exact prefixLift 418005
  have htrace : WordTrace (prefixWord ++ tailWord_418005) baseStart_418005 baseEnd_418005 := by
    simpa [prefixWord, tailWord_418005, baseEnd_418005] using wordTrace_append hprefix tailTrace_418005
  have hstable : (prefixWord ++ tailWord_418005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418005).length < 2 ^ (prefixWord ++ tailWord_418005).sum := by decide
  have hdescent : baseEnd_418005 < baseStart_418005 := by decide
  rcases family_descends (prefixWord ++ tailWord_418005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418116 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_418116 : Nat := 118140960795 + 418116 * 2 ^ 59
def prefixEnd_418116 : Nat := 4983230072969 + 3 ^ 40 * 418116 * 2
def baseEnd_418116 : Nat := 190839535409236758157445

theorem tailTrace_418116 : CollatzResearch.WordTrace tailWord_418116 prefixEnd_418116 190839535409236758157445 := by
  unfold tailWord_418116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624971676622307686393101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10166628902163076915190801 7624971676622307686393101)
  ·
    refine ⟨2859364378733365382397413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7624971676622307686393101 2859364378733365382397413)
    ·
      refine ⟨536130821012506009199515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2859364378733365382397413 536130821012506009199515)
      ·
        refine ⟨804196231518759013799273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536130821012506009199515 804196231518759013799273)
        ·
          refine ⟨603147173639069260349455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804196231518759013799273 603147173639069260349455)
          ·
            refine ⟨904720760458603890524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603147173639069260349455 904720760458603890524183)
            ·
              refine ⟨1357081140687905835786275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904720760458603890524183 1357081140687905835786275)
              ·
                refine ⟨2035621711031858753679413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357081140687905835786275 2035621711031858753679413)
                ·
                  refine ⟨190839535409236758157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2035621711031858753679413 190839535409236758157445)
                  ·
                    rfl

theorem cell20_418116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_418116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418116 prefixEnd_418116 := by exact prefixLift 418116
  have htrace : WordTrace (prefixWord ++ tailWord_418116) baseStart_418116 baseEnd_418116 := by
    simpa [prefixWord, tailWord_418116, baseEnd_418116] using wordTrace_append hprefix tailTrace_418116
  have hstable : (prefixWord ++ tailWord_418116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418116).length < 2 ^ (prefixWord ++ tailWord_418116).sum := by decide
  have hdescent : baseEnd_418116 < baseStart_418116 := by decide
  rcases family_descends (prefixWord ++ tailWord_418116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418151 : List Nat := [1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_418151 : Nat := 118140960795 + 418151 * 2 ^ 59
def prefixEnd_418151 : Nat := 4983230072969 + 3 ^ 40 * 418151 * 2
def baseEnd_418151 : Nat := 63618503454310730663545

theorem tailTrace_418151 : CollatzResearch.WordTrace tailWord_418151 prefixEnd_418151 63618503454310730663545 := by
  unfold tailWord_418151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251219908117816350310307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167479938745210900206871 15251219908117816350310307)
  ·
    refine ⟨22876829862176724525465461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251219908117816350310307 22876829862176724525465461)
    ·
      refine ⟨2144702799579067924262387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22876829862176724525465461 2144702799579067924262387)
      ·
        refine ⟨3217054199368601886393581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144702799579067924262387 3217054199368601886393581)
        ·
          refine ⟨1206395324763225707397593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217054199368601886393581 1206395324763225707397593)
          ·
            refine ⟨904796493572419280548195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206395324763225707397593 904796493572419280548195)
            ·
              refine ⟨1357194740358628920822293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904796493572419280548195 1357194740358628920822293)
              ·
                refine ⟨63618503454310730663545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1357194740358628920822293 63618503454310730663545)
                ·
                  rfl

theorem cell20_418151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_418151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418151 prefixEnd_418151 := by exact prefixLift 418151
  have htrace : WordTrace (prefixWord ++ tailWord_418151) baseStart_418151 baseEnd_418151 := by
    simpa [prefixWord, tailWord_418151, baseEnd_418151] using wordTrace_append hprefix tailTrace_418151
  have hstable : (prefixWord ++ tailWord_418151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418151).length < 2 ^ (prefixWord ++ tailWord_418151).sum := by decide
  have hdescent : baseEnd_418151 < baseStart_418151 := by decide
  rcases family_descends (prefixWord ++ tailWord_418151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418206 : List Nat := [4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_418206 : Nat := 118140960795 + 418206 * 2 ^ 59
def prefixEnd_418206 : Nat := 4983230072969 + 3 ^ 40 * 418206 * 2
def baseEnd_418206 : Nat := 63626871287198815052359

theorem tailTrace_418206 : CollatzResearch.WordTrace tailWord_418206 prefixEnd_418206 63626871287198815052359 := by
  unfold tailWord_418206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906653240364820092945309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10168817281945707162374981 1906653240364820092945309)
  ·
    refine ⟨714994965136807534854491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1906653240364820092945309 714994965136807534854491)
    ·
      refine ⟨1072492447705211302281737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714994965136807534854491 1072492447705211302281737)
      ·
        refine ⟨804369335778908476711303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072492447705211302281737 804369335778908476711303)
        ·
          refine ⟨1206554003668362715066955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804369335778908476711303 1206554003668362715066955)
          ·
            refine ⟨1809831005502544072600433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206554003668362715066955 1809831005502544072600433)
            ·
              refine ⟨1357373254126908054450325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809831005502544072600433 1357373254126908054450325)
              ·
                refine ⟨63626871287198815052359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1357373254126908054450325 63626871287198815052359)
                ·
                  rfl

theorem cell20_418206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_418206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418206 prefixEnd_418206 := by exact prefixLift 418206
  have htrace : WordTrace (prefixWord ++ tailWord_418206) baseStart_418206 baseEnd_418206 := by
    simpa [prefixWord, tailWord_418206, baseEnd_418206] using wordTrace_append hprefix tailTrace_418206
  have hstable : (prefixWord ++ tailWord_418206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418206).length < 2 ^ (prefixWord ++ tailWord_418206).sum := by decide
  have hdescent : baseEnd_418206 < baseStart_418206 := by decide
  rcases family_descends (prefixWord ++ tailWord_418206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418217 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_418217 : Nat := 118140960795 + 418217 * 2 ^ 59
def prefixEnd_418217 : Nat := 4983230072969 + 3 ^ 40 * 418217 * 2
def baseEnd_418217 : Nat := 190885634561329295790365

theorem tailTrace_418217 : CollatzResearch.WordTrace tailWord_418217 prefixEnd_418217 190885634561329295790365 := by
  unfold tailWord_418217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15253627125878709622212905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169084750585806414808603 15253627125878709622212905)
  ·
    refine ⟨11440220344409032216659679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15253627125878709622212905 11440220344409032216659679)
    ·
      refine ⟨17160330516613548324989519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440220344409032216659679 17160330516613548324989519)
      ·
        refine ⟨25740495774920322487484279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17160330516613548324989519 25740495774920322487484279)
        ·
          refine ⟨38610743662380483731226419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25740495774920322487484279 38610743662380483731226419)
          ·
            refine ⟨57916115493570725596839629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38610743662380483731226419 57916115493570725596839629)
            ·
              refine ⟨21718543310089022098814861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57916115493570725596839629 21718543310089022098814861)
              ·
                refine ⟨8144453741283383287055573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21718543310089022098814861 8144453741283383287055573)
                ·
                  refine ⟨190885634561329295790365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8144453741283383287055573 190885634561329295790365)
                  ·
                    rfl

theorem cell20_418217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_418217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418217 prefixEnd_418217 := by exact prefixLift 418217
  have htrace : WordTrace (prefixWord ++ tailWord_418217) baseStart_418217 baseEnd_418217 := by
    simpa [prefixWord, tailWord_418217, baseEnd_418217] using wordTrace_append hprefix tailTrace_418217
  have hstable : (prefixWord ++ tailWord_418217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418217).length < 2 ^ (prefixWord ++ tailWord_418217).sum := by decide
  have hdescent : baseEnd_418217 < baseStart_418217 := by decide
  rcases family_descends (prefixWord ++ tailWord_418217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418220 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_418220 : Nat := 118140960795 + 418220 * 2 ^ 59
def prefixEnd_418220 : Nat := 4983230072969 + 3 ^ 40 * 418220 * 2
def baseEnd_418220 : Nat := 190887003843074618690353

theorem tailTrace_418220 : CollatzResearch.WordTrace tailWord_418220 prefixEnd_418220 190887003843074618690353 := by
  unfold tailWord_418220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626868272433920567286057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10169157696578560756381409 7626868272433920567286057)
  ·
    refine ⟨5720151204325440425464543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7626868272433920567286057 5720151204325440425464543)
    ·
      refine ⟨8580226806488160638196815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720151204325440425464543 8580226806488160638196815)
      ·
        refine ⟨12870340209732240957295223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580226806488160638196815 12870340209732240957295223)
        ·
          refine ⟨19305510314598361435942835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870340209732240957295223 19305510314598361435942835)
          ·
            refine ⟨28958265471897542153914253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19305510314598361435942835 28958265471897542153914253)
            ·
              refine ⟨10859349551961578307717845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28958265471897542153914253 10859349551961578307717845)
              ·
                refine ⟨254516005124099491587137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10859349551961578307717845 254516005124099491587137)
                ·
                  refine ⟨190887003843074618690353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254516005124099491587137 190887003843074618690353)
                  ·
                    rfl

theorem cell20_418220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_418220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418220 prefixEnd_418220 := by exact prefixLift 418220
  have htrace : WordTrace (prefixWord ++ tailWord_418220) baseStart_418220 baseEnd_418220 := by
    simpa [prefixWord, tailWord_418220, baseEnd_418220] using wordTrace_append hprefix tailTrace_418220
  have hstable : (prefixWord ++ tailWord_418220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418220).length < 2 ^ (prefixWord ++ tailWord_418220).sum := by decide
  have hdescent : baseEnd_418220 < baseStart_418220 := by decide
  rcases family_descends (prefixWord ++ tailWord_418220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418237 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 2]
def baseStart_418237 : Nat := 118140960795 + 418237 * 2 ^ 59
def prefixEnd_418237 : Nat := 4983230072969 + 3 ^ 40 * 418237 * 2
def baseEnd_418237 : Nat := 190894763106298115123617

theorem tailTrace_418237 : CollatzResearch.WordTrace tailWord_418237 prefixEnd_418237 190894763106298115123617 := by
  unfold tailWord_418237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254356585806253037940965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169571057204168691960643 15254356585806253037940965)
  ·
    refine ⟨2860191859838672444613931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15254356585806253037940965 2860191859838672444613931)
    ·
      refine ⟨4290287789758008666920897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860191859838672444613931 4290287789758008666920897)
      ·
        refine ⟨3217715842318506500190673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290287789758008666920897 3217715842318506500190673)
        ·
          refine ⟨2413286881738879875143005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217715842318506500190673 2413286881738879875143005)
          ·
            refine ⟨904982580652079953178627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2413286881738879875143005 904982580652079953178627)
            ·
              refine ⟨1357473870978119929767941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904982580652079953178627 1357473870978119929767941)
              ·
                refine ⟨254526350808397486831489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1357473870978119929767941 254526350808397486831489)
                ·
                  refine ⟨190894763106298115123617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254526350808397486831489 190894763106298115123617)
                  ·
                    rfl

theorem cell20_418237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_418237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418237 prefixEnd_418237 := by exact prefixLift 418237
  have htrace : WordTrace (prefixWord ++ tailWord_418237) baseStart_418237 baseEnd_418237 := by
    simpa [prefixWord, tailWord_418237, baseEnd_418237] using wordTrace_append hprefix tailTrace_418237
  have hstable : (prefixWord ++ tailWord_418237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418237).length < 2 ^ (prefixWord ++ tailWord_418237).sum := by decide
  have hdescent : baseEnd_418237 < baseStart_418237 := by decide
  rcases family_descends (prefixWord ++ tailWord_418237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418255 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_418255 : Nat := 118140960795 + 418255 * 2 ^ 59
def prefixEnd_418255 : Nat := 4983230072969 + 3 ^ 40 * 418255 * 2
def baseEnd_418255 : Nat := 190902978796770052523543

theorem tailTrace_418255 : CollatzResearch.WordTrace tailWord_418255 prefixEnd_418255 190902978796770052523543 := by
  unfold tailWord_418255
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255013099741042112096219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10170008733160694741397479 15255013099741042112096219)
  ·
    refine ⟨22882519649611563168144329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15255013099741042112096219 22882519649611563168144329)
    ·
      refine ⟨17161889737208672376108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22882519649611563168144329 17161889737208672376108247)
      ·
        refine ⟨25742834605813008564162371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17161889737208672376108247 25742834605813008564162371)
        ·
          refine ⟨38614251908719512846243557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25742834605813008564162371 38614251908719512846243557)
          ·
            refine ⟨7240172232884908658670667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38614251908719512846243557 7240172232884908658670667)
            ·
              refine ⟨10860258349327362988006001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240172232884908658670667 10860258349327362988006001)
              ·
                refine ⟨8145193761995522241004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10860258349327362988006001 8145193761995522241004501)
                ·
                  refine ⟨190902978796770052523543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8145193761995522241004501 190902978796770052523543)
                  ·
                    rfl

theorem cell20_418255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_418255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418255 prefixEnd_418255 := by exact prefixLift 418255
  have htrace : WordTrace (prefixWord ++ tailWord_418255) baseStart_418255 baseEnd_418255 := by
    simpa [prefixWord, tailWord_418255, baseEnd_418255] using wordTrace_append hprefix tailTrace_418255
  have hstable : (prefixWord ++ tailWord_418255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418255).length < 2 ^ (prefixWord ++ tailWord_418255).sum := by decide
  have hdescent : baseEnd_418255 < baseStart_418255 := by decide
  rcases family_descends (prefixWord ++ tailWord_418255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418265 : List Nat := [1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_418265 : Nat := 118140960795 + 418265 * 2 ^ 59
def prefixEnd_418265 : Nat := 4983230072969 + 3 ^ 40 * 418265 * 2
def baseEnd_418265 : Nat := 63635847689751487396723

theorem tailTrace_418265 : CollatzResearch.WordTrace tailWord_418265 prefixEnd_418265 63635847689751487396723 := by
  unfold tailWord_418265
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255377829704813819960249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10170251886469875879973499 15255377829704813819960249)
  ·
    refine ⟨11441533372278610364970187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15255377829704813819960249 11441533372278610364970187)
    ·
      refine ⟨17162300058417915547455281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441533372278610364970187 17162300058417915547455281)
      ·
        refine ⟨12871725043813436660591461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17162300058417915547455281 12871725043813436660591461)
        ·
          refine ⟨2413448445715019373860899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12871725043813436660591461 2413448445715019373860899)
          ·
            refine ⟨3620172668572529060791349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413448445715019373860899 3620172668572529060791349)
            ·
              refine ⟨339391187678674599449189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3620172668572529060791349 339391187678674599449189)
              ·
                refine ⟨63635847689751487396723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339391187678674599449189 63635847689751487396723)
                ·
                  rfl

theorem cell20_418265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_418265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418265 prefixEnd_418265 := by exact prefixLift 418265
  have htrace : WordTrace (prefixWord ++ tailWord_418265) baseStart_418265 baseEnd_418265 := by
    simpa [prefixWord, tailWord_418265, baseEnd_418265] using wordTrace_append hprefix tailTrace_418265
  have hstable : (prefixWord ++ tailWord_418265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418265).length < 2 ^ (prefixWord ++ tailWord_418265).sum := by decide
  have hdescent : baseEnd_418265 < baseStart_418265 := by decide
  rcases family_descends (prefixWord ++ tailWord_418265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418279 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_418279 : Nat := 118140960795 + 418279 * 2 ^ 59
def prefixEnd_418279 : Nat := 4983230072969 + 3 ^ 40 * 418279 * 2
def baseEnd_418279 : Nat := 190913933050732635723445

theorem tailTrace_418279 : CollatzResearch.WordTrace tailWord_418279 prefixEnd_418279 190913933050732635723445 := by
  unfold tailWord_418279
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255888451654094210969891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10170592301102729473979927 15255888451654094210969891)
  ·
    refine ⟨22883832677481141316454837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15255888451654094210969891 22883832677481141316454837)
    ·
      refine ⟨2145359313513856998417641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22883832677481141316454837 2145359313513856998417641)
      ·
        refine ⟨1609019485135392748813231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2145359313513856998417641 1609019485135392748813231)
        ·
          refine ⟨2413529227703089123219847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609019485135392748813231 2413529227703089123219847)
          ·
            refine ⟨3620293841554633684829771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413529227703089123219847 3620293841554633684829771)
            ·
              refine ⟨5430440762331950527244657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620293841554633684829771 5430440762331950527244657)
              ·
                refine ⟨4072830571748962895433493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5430440762331950527244657 4072830571748962895433493)
                ·
                  refine ⟨190913933050732635723445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4072830571748962895433493 190913933050732635723445)
                  ·
                    rfl

theorem cell20_418279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_418279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418279 prefixEnd_418279 := by exact prefixLift 418279
  have htrace : WordTrace (prefixWord ++ tailWord_418279) baseStart_418279 baseEnd_418279 := by
    simpa [prefixWord, tailWord_418279, baseEnd_418279] using wordTrace_append hprefix tailTrace_418279
  have hstable : (prefixWord ++ tailWord_418279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418279).length < 2 ^ (prefixWord ++ tailWord_418279).sum := by decide
  have hdescent : baseEnd_418279 < baseStart_418279 := by decide
  rcases family_descends (prefixWord ++ tailWord_418279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418296 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_418296 : Nat := 118140960795 + 418296 * 2 ^ 59
def prefixEnd_418296 : Nat := 4983230072969 + 3 ^ 40 * 418296 * 2
def baseEnd_418296 : Nat := 190921692313956132156709

theorem tailTrace_418296 : CollatzResearch.WordTrace tailWord_418296 prefixEnd_418296 190921692313956132156709 := by
  unfold tailWord_418296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628254246296253057169371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10171005661728337409559161 7628254246296253057169371)
  ·
    refine ⟨11442381369444379585754057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628254246296253057169371 11442381369444379585754057)
    ·
      refine ⟨8581786027083284689315543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11442381369444379585754057 8581786027083284689315543)
      ·
        refine ⟨12872679040624927033973315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8581786027083284689315543 12872679040624927033973315)
        ·
          refine ⟨19309018560937390550959973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12872679040624927033973315 19309018560937390550959973)
          ·
            refine ⟨3620440980175760728304995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19309018560937390550959973 3620440980175760728304995)
            ·
              refine ⟨5430661470263641092457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620440980175760728304995 5430661470263641092457493)
              ·
                refine ⟨254562256418608176208945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5430661470263641092457493 254562256418608176208945)
                ·
                  refine ⟨190921692313956132156709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254562256418608176208945 190921692313956132156709)
                  ·
                    rfl

theorem cell20_418296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_418296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418296 prefixEnd_418296 := by exact prefixLift 418296
  have htrace : WordTrace (prefixWord ++ tailWord_418296) baseStart_418296 baseEnd_418296 := by
    simpa [prefixWord, tailWord_418296, baseEnd_418296] using wordTrace_append hprefix tailTrace_418296
  have hstable : (prefixWord ++ tailWord_418296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418296).length < 2 ^ (prefixWord ++ tailWord_418296).sum := by decide
  have hdescent : baseEnd_418296 < baseStart_418296 := by decide
  rcases family_descends (prefixWord ++ tailWord_418296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418358 : List Nat := [5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_418358 : Nat := 118140960795 + 418358 * 2 ^ 59
def prefixEnd_418358 : Nat := 4983230072969 + 3 ^ 40 * 418358 * 2
def baseEnd_418358 : Nat := 63649996934453157363263

theorem tailTrace_418358 : CollatzResearch.WordTrace tailWord_418358 prefixEnd_418358 63649996934453157363263 := by
  unfold tailWord_418358
  simp only [CollatzResearch.WordTrace]
  refine ⟨953673113647993168943483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10172513212245260468730485 953673113647993168943483)
  ·
    refine ⟨1430509670471989753415225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953673113647993168943483 1430509670471989753415225)
    ·
      refine ⟨1072882252853992315061419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430509670471989753415225 1072882252853992315061419)
      ·
        refine ⟨1609323379280988472592129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072882252853992315061419 1609323379280988472592129)
        ·
          refine ⟨1206992534460741354444097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609323379280988472592129 1206992534460741354444097)
          ·
            refine ⟨905244400845556015833073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206992534460741354444097 905244400845556015833073)
            ·
              refine ⟨678933300634167011874805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905244400845556015833073 678933300634167011874805)
              ·
                refine ⟨63649996934453157363263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 678933300634167011874805 63649996934453157363263)
                ·
                  rfl

theorem cell20_418358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_418358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418358 prefixEnd_418358 := by exact prefixLift 418358
  have htrace : WordTrace (prefixWord ++ tailWord_418358) baseStart_418358 baseEnd_418358 := by
    simpa [prefixWord, tailWord_418358, baseEnd_418358] using wordTrace_append hprefix tailTrace_418358
  have hstable : (prefixWord ++ tailWord_418358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418358).length < 2 ^ (prefixWord ++ tailWord_418358).sum := by decide
  have hdescent : baseEnd_418358 < baseStart_418358 := by decide
  rcases family_descends (prefixWord ++ tailWord_418358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418362 : List Nat := [3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_418362 : Nat := 118140960795 + 418362 * 2 ^ 59
def prefixEnd_418362 : Nat := 4983230072969 + 3 ^ 40 * 418362 * 2
def baseEnd_418362 : Nat := 63650605504117745318813

theorem tailTrace_418362 : CollatzResearch.WordTrace tailWord_418362 prefixEnd_418362 63650605504117745318813 := by
  unfold tailWord_418362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814728927588349846560335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10172610473568932924160893 3814728927588349846560335)
  ·
    refine ⟨5722093391382524769840503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814728927588349846560335 5722093391382524769840503)
    ·
      refine ⟨8583140087073787154760755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722093391382524769840503 8583140087073787154760755)
      ·
        refine ⟨12874710130610680732141133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583140087073787154760755 12874710130610680732141133)
        ·
          refine ⟨4828016298979005274552925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12874710130610680732141133 4828016298979005274552925)
          ·
            refine ⟨1810506112117126977957347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4828016298979005274552925 1810506112117126977957347)
            ·
              refine ⟨2715759168175690466936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810506112117126977957347 2715759168175690466936021)
              ·
                refine ⟨63650605504117745318813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2715759168175690466936021 63650605504117745318813)
                ·
                  rfl

theorem cell20_418362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_418362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418362 prefixEnd_418362 := by exact prefixLift 418362
  have htrace : WordTrace (prefixWord ++ tailWord_418362) baseStart_418362 baseEnd_418362 := by
    simpa [prefixWord, tailWord_418362, baseEnd_418362] using wordTrace_append hprefix tailTrace_418362
  have hstable : (prefixWord ++ tailWord_418362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418362).length < 2 ^ (prefixWord ++ tailWord_418362).sum := by decide
  have hdescent : baseEnd_418362 < baseStart_418362 := by decide
  rcases family_descends (prefixWord ++ tailWord_418362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418365 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_418365 : Nat := 118140960795 + 418365 * 2 ^ 59
def prefixEnd_418365 : Nat := 4983230072969 + 3 ^ 40 * 418365 * 2
def baseEnd_418365 : Nat := 190953185794098558856427

theorem tailTrace_418365 : CollatzResearch.WordTrace tailWord_418365 prefixEnd_418365 190953185794098558856427 := by
  unfold tailWord_418365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259025129342530898600549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10172683419561687265733699 15259025129342530898600549)
  ·
    refine ⟨2861067211751724543487603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15259025129342530898600549 2861067211751724543487603)
    ·
      refine ⟨4291600817627586815231405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861067211751724543487603 4291600817627586815231405)
      ·
        refine ⟨1609350306610345055711777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4291600817627586815231405 1609350306610345055711777)
        ·
          refine ⟨1207012729957758791783833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609350306610345055711777 1207012729957758791783833)
          ·
            refine ⟨905259547468319093837875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207012729957758791783833 905259547468319093837875)
            ·
              refine ⟨1357889321202478640756813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905259547468319093837875 1357889321202478640756813)
              ·
                refine ⟨509208495450929490283805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357889321202478640756813 509208495450929490283805)
                ·
                  refine ⟨190953185794098558856427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509208495450929490283805 190953185794098558856427)
                  ·
                    rfl

theorem cell20_418365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_418365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418365 prefixEnd_418365 := by exact prefixLift 418365
  have htrace : WordTrace (prefixWord ++ tailWord_418365) baseStart_418365 baseEnd_418365 := by
    simpa [prefixWord, tailWord_418365, baseEnd_418365] using wordTrace_append hprefix tailTrace_418365
  have hstable : (prefixWord ++ tailWord_418365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418365).length < 2 ^ (prefixWord ++ tailWord_418365).sum := by decide
  have hdescent : baseEnd_418365 < baseStart_418365 := by decide
  rcases family_descends (prefixWord ++ tailWord_418365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418398 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_418398 : Nat := 118140960795 + 418398 * 2 ^ 59
def prefixEnd_418398 : Nat := 4983230072969 + 3 ^ 40 * 418398 * 2
def baseEnd_418398 : Nat := 190968247893297110756293

theorem tailTrace_418398 : CollatzResearch.WordTrace tailWord_418398 prefixEnd_418398 190968247893297110756293 := by
  unfold tailWord_418398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907528592277872191818981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10173485825481985023034565 1907528592277872191818981)
  ·
    refine ⟨357661611052101035966059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1907528592277872191818981 357661611052101035966059)
    ·
      refine ⟨536492416578151553949089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357661611052101035966059 536492416578151553949089)
      ·
        refine ⟨402369312433613665461817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536492416578151553949089 402369312433613665461817)
        ·
          refine ⟨301776984325210249096363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402369312433613665461817 301776984325210249096363)
          ·
            refine ⟨452665476487815373644545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301776984325210249096363 452665476487815373644545)
            ·
              refine ⟨339499107365861530233409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452665476487815373644545 339499107365861530233409)
              ·
                refine ⟨254624330524396147675057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339499107365861530233409 254624330524396147675057)
                ·
                  refine ⟨190968247893297110756293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254624330524396147675057 190968247893297110756293)
                  ·
                    rfl

theorem cell20_418398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_418398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418398 prefixEnd_418398 := by exact prefixLift 418398
  have htrace : WordTrace (prefixWord ++ tailWord_418398) baseStart_418398 baseEnd_418398 := by
    simpa [prefixWord, tailWord_418398, baseEnd_418398] using wordTrace_append hprefix tailTrace_418398
  have hstable : (prefixWord ++ tailWord_418398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418398).length < 2 ^ (prefixWord ++ tailWord_418398).sum := by decide
  have hdescent : baseEnd_418398 < baseStart_418398 := by decide
  rcases family_descends (prefixWord ++ tailWord_418398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418402 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_418402 : Nat := 118140960795 + 418402 * 2 ^ 59
def prefixEnd_418402 : Nat := 4983230072969 + 3 ^ 40 * 418402 * 2
def baseEnd_418402 : Nat := 190970073602290874622943

theorem tailTrace_418402 : CollatzResearch.WordTrace tailWord_418402 prefixEnd_418402 190970073602290874622943 := by
  unfold tailWord_418402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815093657552121554424365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10173583086805657478464973 3815093657552121554424365)
  ·
    refine ⟨1430660121582045582909137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3815093657552121554424365 1430660121582045582909137)
    ·
      refine ⟨1072995091186534187181853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430660121582045582909137 1072995091186534187181853)
      ·
        refine ⟨402373159194950320193195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1072995091186534187181853 402373159194950320193195)
        ·
          refine ⟨603559738792425480289793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402373159194950320193195 603559738792425480289793)
          ·
            refine ⟨452669804094319110217345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603559738792425480289793 452669804094319110217345)
            ·
              refine ⟨339502353070739332663009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452669804094319110217345 339502353070739332663009)
              ·
                refine ⟨254626764803054499497257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339502353070739332663009 254626764803054499497257)
                ·
                  refine ⟨190970073602290874622943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254626764803054499497257 190970073602290874622943)
                  ·
                    rfl

theorem cell20_418402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_418402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418402 prefixEnd_418402 := by exact prefixLift 418402
  have htrace : WordTrace (prefixWord ++ tailWord_418402) baseStart_418402 baseEnd_418402 := by
    simpa [prefixWord, tailWord_418402, baseEnd_418402] using wordTrace_append hprefix tailTrace_418402
  have hstable : (prefixWord ++ tailWord_418402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418402).length < 2 ^ (prefixWord ++ tailWord_418402).sum := by decide
  have hdescent : baseEnd_418402 < baseStart_418402 := by decide
  rcases family_descends (prefixWord ++ tailWord_418402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418479 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_418479 : Nat := 118140960795 + 418479 * 2 ^ 59
def prefixEnd_418479 : Nat := 4983230072969 + 3 ^ 40 * 418479 * 2
def baseEnd_418479 : Nat := 191005218500420829055961

theorem tailTrace_418479 : CollatzResearch.WordTrace tailWord_418479 prefixEnd_418479 191005218500420829055961 := by
  unfold tailWord_418479
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263183050929528368250491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175455367286352245500327 15263183050929528368250491)
  ·
    refine ⟨22894774576394292552375737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15263183050929528368250491 22894774576394292552375737)
    ·
      refine ⟨17171080932295719414281803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22894774576394292552375737 17171080932295719414281803)
      ·
        refine ⟨25756621398443579121422705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171080932295719414281803 25756621398443579121422705)
        ·
          refine ⟨19317466048832684341067029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25756621398443579121422705 19317466048832684341067029)
          ·
            refine ⟨905506221039032078487517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19317466048832684341067029 905506221039032078487517)
            ·
              refine ⟨339564832889637029432819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905506221039032078487517 339564832889637029432819)
              ·
                refine ⟨509347249334455544149229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339564832889637029432819 509347249334455544149229)
                ·
                  refine ⟨191005218500420829055961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509347249334455544149229 191005218500420829055961)
                  ·
                    rfl

theorem cell20_418479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_418479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418479 prefixEnd_418479 := by exact prefixLift 418479
  have htrace : WordTrace (prefixWord ++ tailWord_418479) baseStart_418479 baseEnd_418479 := by
    simpa [prefixWord, tailWord_418479, baseEnd_418479] using wordTrace_append hprefix tailTrace_418479
  have hstable : (prefixWord ++ tailWord_418479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418479).length < 2 ^ (prefixWord ++ tailWord_418479).sum := by decide
  have hdescent : baseEnd_418479 < baseStart_418479 := by decide
  rcases family_descends (prefixWord ++ tailWord_418479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418493 : List Nat := [1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_418493 : Nat := 118140960795 + 418493 * 2 ^ 59
def prefixEnd_418493 : Nat := 4983230072969 + 3 ^ 40 * 418493 * 2
def baseEnd_418493 : Nat := 63670536160633000863079

theorem tailTrace_418493 : CollatzResearch.WordTrace tailWord_418493 prefixEnd_418493 63670536160633000863079 := by
  unfold tailWord_418493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263693672878808759260133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175795781919205839506755 15263693672878808759260133)
  ·
    refine ⟨2861942563664776642361275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15263693672878808759260133 2861942563664776642361275)
    ·
      refine ⟨4292913845497164963541913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861942563664776642361275 4292913845497164963541913)
      ·
        refine ⟨3219685384122873722656435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4292913845497164963541913 3219685384122873722656435)
        ·
          refine ⟨4829528076184310583984653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219685384122873722656435 4829528076184310583984653)
          ·
            refine ⟨1811073028569116468994245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4829528076184310583984653 1811073028569116468994245)
            ·
              refine ⟨339576192856709337936421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1811073028569116468994245 339576192856709337936421)
              ·
                refine ⟨63670536160633000863079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339576192856709337936421 63670536160633000863079)
                ·
                  rfl

theorem cell20_418493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_418493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418493 prefixEnd_418493 := by exact prefixLift 418493
  have htrace : WordTrace (prefixWord ++ tailWord_418493) baseStart_418493 baseEnd_418493 := by
    simpa [prefixWord, tailWord_418493, baseEnd_418493] using wordTrace_append hprefix tailTrace_418493
  have hstable : (prefixWord ++ tailWord_418493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418493).length < 2 ^ (prefixWord ++ tailWord_418493).sum := by decide
  have hdescent : baseEnd_418493 < baseStart_418493 := by decide
  rcases family_descends (prefixWord ++ tailWord_418493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418500 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_418500 : Nat := 118140960795 + 418500 * 2 ^ 59
def prefixEnd_418500 : Nat := 4983230072969 + 3 ^ 40 * 418500 * 2
def baseEnd_418500 : Nat := 191014803472638089355875

theorem tailTrace_418500 : CollatzResearch.WordTrace tailWord_418500 prefixEnd_418500 191014803472638089355875 := by
  unfold tailWord_418500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631974491926724477382477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10175965989235632636509969 7631974491926724477382477)
  ·
    refine ⟨2861990434472521679018429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7631974491926724477382477 2861990434472521679018429)
    ·
      refine ⟨1073246412927195629631911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2861990434472521679018429 1073246412927195629631911)
      ·
        refine ⟨1609869619390793444447867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073246412927195629631911 1609869619390793444447867)
        ·
          refine ⟨2414804429086190166671801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609869619390793444447867 2414804429086190166671801)
          ·
            refine ⟨1811103321814642625003851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414804429086190166671801 1811103321814642625003851)
            ·
              refine ⟨2716654982721963937505777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811103321814642625003851 2716654982721963937505777)
              ·
                refine ⟨2037491237041472953129333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716654982721963937505777 2037491237041472953129333)
                ·
                  refine ⟨191014803472638089355875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037491237041472953129333 191014803472638089355875)
                  ·
                    rfl

theorem cell20_418500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_418500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418500 prefixEnd_418500 := by exact prefixLift 418500
  have htrace : WordTrace (prefixWord ++ tailWord_418500) baseStart_418500 baseEnd_418500 := by
    simpa [prefixWord, tailWord_418500, baseEnd_418500] using wordTrace_append hprefix tailTrace_418500
  have hstable : (prefixWord ++ tailWord_418500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418500).length < 2 ^ (prefixWord ++ tailWord_418500).sum := by decide
  have hdescent : baseEnd_418500 < baseStart_418500 := by decide
  rcases family_descends (prefixWord ++ tailWord_418500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418521 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_418521 : Nat := 118140960795 + 418521 * 2 ^ 59
def prefixEnd_418521 : Nat := 4983230072969 + 3 ^ 40 * 418521 * 2
def baseEnd_418521 : Nat := 191024388444855349655789

theorem tailTrace_418521 : CollatzResearch.WordTrace tailWord_418521 prefixEnd_418521 191024388444855349655789 := by
  unfold tailWord_418521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264714916777369541279417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176476611184913027519611 15264714916777369541279417)
  ·
    refine ⟨11448536187583027155959563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15264714916777369541279417 11448536187583027155959563)
    ·
      refine ⟨17172804281374540733939345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448536187583027155959563 17172804281374540733939345)
      ·
        refine ⟨12879603211030905550454509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17172804281374540733939345 12879603211030905550454509)
        ·
          refine ⟨4829851204136589581420441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12879603211030905550454509 4829851204136589581420441)
          ·
            refine ⟨3622388403102442186065331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829851204136589581420441 3622388403102442186065331)
            ·
              refine ⟨5433582604653663279097997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622388403102442186065331 5433582604653663279097997)
              ·
                refine ⟨2037593476745123729661749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5433582604653663279097997 2037593476745123729661749)
                ·
                  refine ⟨191024388444855349655789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037593476745123729661749 191024388444855349655789)
                  ·
                    rfl

theorem cell20_418521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_418521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418521 prefixEnd_418521 := by exact prefixLift 418521
  have htrace : WordTrace (prefixWord ++ tailWord_418521) baseStart_418521 baseEnd_418521 := by
    simpa [prefixWord, tailWord_418521, baseEnd_418521] using wordTrace_append hprefix tailTrace_418521
  have hstable : (prefixWord ++ tailWord_418521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418521).length < 2 ^ (prefixWord ++ tailWord_418521).sum := by decide
  have hdescent : baseEnd_418521 < baseStart_418521 := by decide
  rcases family_descends (prefixWord ++ tailWord_418521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418531 : List Nat := [1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_418531 : Nat := 118140960795 + 418531 * 2 ^ 59
def prefixEnd_418531 : Nat := 4983230072969 + 3 ^ 40 * 418531 * 2
def baseEnd_418531 : Nat := 63676317572446586440805

theorem tailTrace_418531 : CollatzResearch.WordTrace tailWord_418531 prefixEnd_418531 63676317572446586440805 := by
  unfold tailWord_418531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265079646741141249143447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176719764494094166095631 15265079646741141249143447)
  ·
    refine ⟨22897619470111711873715171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265079646741141249143447 22897619470111711873715171)
    ·
      refine ⟨34346429205167567810572757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22897619470111711873715171 34346429205167567810572757)
      ·
        refine ⟨804994434496114870560299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34346429205167567810572757 804994434496114870560299)
        ·
          refine ⟨1207491651744172305840449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804994434496114870560299 1207491651744172305840449)
          ·
            refine ⟨905618738808129229380337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207491651744172305840449 905618738808129229380337)
            ·
              refine ⟨679214054106096922035253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905618738808129229380337 679214054106096922035253)
              ·
                refine ⟨63676317572446586440805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 679214054106096922035253 63676317572446586440805)
                ·
                  rfl

theorem cell20_418531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_418531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418531 prefixEnd_418531 := by exact prefixLift 418531
  have htrace : WordTrace (prefixWord ++ tailWord_418531) baseStart_418531 baseEnd_418531 := by
    simpa [prefixWord, tailWord_418531, baseEnd_418531] using wordTrace_append hprefix tailTrace_418531
  have hstable : (prefixWord ++ tailWord_418531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418531).length < 2 ^ (prefixWord ++ tailWord_418531).sum := by decide
  have hdescent : baseEnd_418531 < baseStart_418531 := by decide
  rcases family_descends (prefixWord ++ tailWord_418531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418659 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_418659 : Nat := 118140960795 + 418659 * 2 ^ 59
def prefixEnd_418659 : Nat := 4983230072969 + 3 ^ 40 * 418659 * 2
def baseEnd_418659 : Nat := 191087375405140203055225

theorem tailTrace_418659 : CollatzResearch.WordTrace tailWord_418659 prefixEnd_418659 191087375405140203055225 := by
  unfold tailWord_418659
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269748190277419109803031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10179832126851612739868687 15269748190277419109803031)
  ·
    refine ⟨22904622285416128664704547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269748190277419109803031 22904622285416128664704547)
    ·
      refine ⟨34356933428124192997056821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22904622285416128664704547 34356933428124192997056821)
      ·
        refine ⟨3220962508886643093474077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34356933428124192997056821 3220962508886643093474077)
        ·
          refine ⟨1207860940832491160052779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3220962508886643093474077 1207860940832491160052779)
          ·
            refine ⟨1811791411248736740079169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207860940832491160052779 1811791411248736740079169)
            ·
              refine ⟨1358843558436552555059377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811791411248736740079169 1358843558436552555059377)
              ·
                refine ⟨1019132668827414416294533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358843558436552555059377 1019132668827414416294533)
                ·
                  refine ⟨191087375405140203055225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019132668827414416294533 191087375405140203055225)
                  ·
                    rfl

theorem cell20_418659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_418659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418659 prefixEnd_418659 := by exact prefixLift 418659
  have htrace : WordTrace (prefixWord ++ tailWord_418659) baseStart_418659 baseEnd_418659 := by
    simpa [prefixWord, tailWord_418659, baseEnd_418659] using wordTrace_append hprefix tailTrace_418659
  have hstable : (prefixWord ++ tailWord_418659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418659).length < 2 ^ (prefixWord ++ tailWord_418659).sum := by decide
  have hdescent : baseEnd_418659 < baseStart_418659 := by decide
  rcases family_descends (prefixWord ++ tailWord_418659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418673 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_418673 : Nat := 118140960795 + 418673 * 2 ^ 59
def prefixEnd_418673 : Nat := 4983230072969 + 3 ^ 40 * 418673 * 2
def baseEnd_418673 : Nat := 191093765386618376588501

theorem tailTrace_418673 : CollatzResearch.WordTrace tailWord_418673 prefixEnd_418673 191093765386618376588501 := by
  unfold tailWord_418673
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270258812226699500812673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10180172541484466333875115 15270258812226699500812673)
  ·
    refine ⟨11452694109170024625609505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15270258812226699500812673 11452694109170024625609505)
    ·
      refine ⟨8589520581877518469207129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11452694109170024625609505 8589520581877518469207129)
      ·
        refine ⟨6442140436408138851905347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589520581877518469207129 6442140436408138851905347)
        ·
          refine ⟨9663210654612208277858021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442140436408138851905347 9663210654612208277858021)
          ·
            refine ⟨1811851997739789052098379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9663210654612208277858021 1811851997739789052098379)
            ·
              refine ⟨2717777996609683578147569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811851997739789052098379 2717777996609683578147569)
              ·
                refine ⟨2038333497457262683610677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717777996609683578147569 2038333497457262683610677)
                ·
                  refine ⟨191093765386618376588501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038333497457262683610677 191093765386618376588501)
                  ·
                    rfl

theorem cell20_418673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_418673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418673 prefixEnd_418673 := by exact prefixLift 418673
  have htrace : WordTrace (prefixWord ++ tailWord_418673) baseStart_418673 baseEnd_418673 := by
    simpa [prefixWord, tailWord_418673, baseEnd_418673] using wordTrace_append hprefix tailTrace_418673
  have hstable : (prefixWord ++ tailWord_418673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418673).length < 2 ^ (prefixWord ++ tailWord_418673).sum := by decide
  have hdescent : baseEnd_418673 < baseStart_418673 := by decide
  rcases family_descends (prefixWord ++ tailWord_418673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418687 : List Nat := [1, 1, 2, 2, 1, 1, 12]
def baseStart_418687 : Nat := 118140960795 + 418687 * 2 ^ 59
def prefixEnd_418687 : Nat := 4983230072969 + 3 ^ 40 * 418687 * 2
def baseEnd_418687 : Nat := 21233350596455172235753

theorem tailTrace_418687 : CollatzResearch.WordTrace tailWord_418687 prefixEnd_418687 21233350596455172235753 := by
  unfold tailWord_418687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270769434175979891822315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10180512956117319927881543 15270769434175979891822315)
  ·
    refine ⟨22906154151263969837733473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15270769434175979891822315 22906154151263969837733473)
    ·
      refine ⟨17179615613447977378300105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22906154151263969837733473 17179615613447977378300105)
      ·
        refine ⟨12884711710085983033725079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17179615613447977378300105 12884711710085983033725079)
        ·
          refine ⟨19327067565128974550587619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12884711710085983033725079 19327067565128974550587619)
          ·
            refine ⟨28990601347693461825881429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19327067565128974550587619 28990601347693461825881429)
            ·
              refine ⟨21233350596455172235753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 28990601347693461825881429 21233350596455172235753)
              ·
                rfl

theorem cell20_418687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_418687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418687 prefixEnd_418687 := by exact prefixLift 418687
  have htrace : WordTrace (prefixWord ++ tailWord_418687) baseStart_418687 baseEnd_418687 := by
    simpa [prefixWord, tailWord_418687, baseEnd_418687] using wordTrace_append hprefix tailTrace_418687
  have hstable : (prefixWord ++ tailWord_418687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418687).length < 2 ^ (prefixWord ++ tailWord_418687).sum := by decide
  have hdescent : baseEnd_418687 < baseStart_418687 := by decide
  rcases family_descends (prefixWord ++ tailWord_418687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418693 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 2]
def baseStart_418693 : Nat := 118140960795 + 418693 * 2 ^ 59
def prefixEnd_418693 : Nat := 4983230072969 + 3 ^ 40 * 418693 * 2
def baseEnd_418693 : Nat := 191102893931587195921753

theorem tailTrace_418693 : CollatzResearch.WordTrace tailWord_418693 prefixEnd_418693 191102893931587195921753 := by
  unfold tailWord_418693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270988272154242916540733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10180658848102828611027155 15270988272154242916540733)
  ·
    refine ⟨5726620602057841093702775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15270988272154242916540733 5726620602057841093702775)
    ·
      refine ⟨8589930903086761640554163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726620602057841093702775 8589930903086761640554163)
      ·
        refine ⟨12884896354630142460831245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8589930903086761640554163 12884896354630142460831245)
        ·
          refine ⟨4831836132986303422811717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12884896354630142460831245 4831836132986303422811717)
          ·
            refine ⟨905969274934931891777197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4831836132986303422811717 905969274934931891777197)
            ·
              refine ⟨339738478100599459416449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905969274934931891777197 339738478100599459416449)
              ·
                refine ⟨254803858575449594562337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339738478100599459416449 254803858575449594562337)
                ·
                  refine ⟨191102893931587195921753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254803858575449594562337 191102893931587195921753)
                  ·
                    rfl

theorem cell20_418693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_418693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418693 prefixEnd_418693 := by exact prefixLift 418693
  have htrace : WordTrace (prefixWord ++ tailWord_418693) baseStart_418693 baseEnd_418693 := by
    simpa [prefixWord, tailWord_418693, baseEnd_418693] using wordTrace_append hprefix tailTrace_418693
  have hstable : (prefixWord ++ tailWord_418693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418693).length < 2 ^ (prefixWord ++ tailWord_418693).sum := by decide
  have hdescent : baseEnd_418693 < baseStart_418693 := by decide
  rcases family_descends (prefixWord ++ tailWord_418693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418697 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_418697 : Nat := 118140960795 + 418697 * 2 ^ 59
def prefixEnd_418697 : Nat := 4983230072969 + 3 ^ 40 * 418697 * 2
def baseEnd_418697 : Nat := 191104719640580959788403

theorem tailTrace_418697 : CollatzResearch.WordTrace tailWord_418697 prefixEnd_418697 191104719640580959788403 := by
  unfold tailWord_418697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271134164139751599686345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10180756109426501066457563 15271134164139751599686345)
  ·
    refine ⟨11453350623104813699764759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15271134164139751599686345 11453350623104813699764759)
    ·
      refine ⟨17180025934657220549647139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11453350623104813699764759 17180025934657220549647139)
      ·
        refine ⟨25770038901985830824470709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17180025934657220549647139 25770038901985830824470709)
        ·
          refine ⟨2415941147061171639794129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25770038901985830824470709 2415941147061171639794129)
          ·
            refine ⟨1811955860295878729845597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415941147061171639794129 1811955860295878729845597)
            ·
              refine ⟨679483447610954523692099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811955860295878729845597 679483447610954523692099)
              ·
                refine ⟨1019225171416431785538149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679483447610954523692099 1019225171416431785538149)
                ·
                  refine ⟨191104719640580959788403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019225171416431785538149 191104719640580959788403)
                  ·
                    rfl

theorem cell20_418697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_418697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418697 prefixEnd_418697 := by exact prefixLift 418697
  have htrace : WordTrace (prefixWord ++ tailWord_418697) baseStart_418697 baseEnd_418697 := by
    simpa [prefixWord, tailWord_418697, baseEnd_418697] using wordTrace_append hprefix tailTrace_418697
  have hstable : (prefixWord ++ tailWord_418697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418697).length < 2 ^ (prefixWord ++ tailWord_418697).sum := by decide
  have hdescent : baseEnd_418697 < baseStart_418697 := by decide
  rcases family_descends (prefixWord ++ tailWord_418697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418752 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_418752 : Nat := 118140960795 + 418752 * 2 ^ 59
def prefixEnd_418752 : Nat := 4983230072969 + 3 ^ 40 * 418752 * 2
def baseEnd_418752 : Nat := 191129823139245212954845

theorem tailTrace_418752 : CollatzResearch.WordTrace tailWord_418752 prefixEnd_418752 191129823139245212954845 := by
  unfold tailWord_418752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636570089470247996469255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10182093452626997328625673 7636570089470247996469255)
  ·
    refine ⟨11454855134205371994703883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7636570089470247996469255 11454855134205371994703883)
    ·
      refine ⟨17182282701308057992055825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11454855134205371994703883 17182282701308057992055825)
      ·
        refine ⟨12886712025981043494041869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17182282701308057992055825 12886712025981043494041869)
        ·
          refine ⟨4832517009742891310265701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12886712025981043494041869 4832517009742891310265701)
          ·
            refine ⟨906096939326792120674819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4832517009742891310265701 906096939326792120674819)
            ·
              refine ⟨1359145408990188181012229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906096939326792120674819 1359145408990188181012229)
              ·
                refine ⟨254839764185660283939793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1359145408990188181012229 254839764185660283939793)
                ·
                  refine ⟨191129823139245212954845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254839764185660283939793 191129823139245212954845)
                  ·
                    rfl

theorem cell20_418752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_418752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418752 prefixEnd_418752 := by exact prefixLift 418752
  have htrace : WordTrace (prefixWord ++ tailWord_418752) baseStart_418752 baseEnd_418752 := by
    simpa [prefixWord, tailWord_418752, baseEnd_418752] using wordTrace_append hprefix tailTrace_418752
  have hstable : (prefixWord ++ tailWord_418752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418752).length < 2 ^ (prefixWord ++ tailWord_418752).sum := by decide
  have hdescent : baseEnd_418752 < baseStart_418752 := by decide
  rcases family_descends (prefixWord ++ tailWord_418752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418766 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_418766 : Nat := 118140960795 + 418766 * 2 ^ 59
def prefixEnd_418766 : Nat := 4983230072969 + 3 ^ 40 * 418766 * 2
def baseEnd_418766 : Nat := 191136213120723386488121

theorem tailTrace_418766 : CollatzResearch.WordTrace tailWord_418766 prefixEnd_418766 191136213120723386488121 := by
  unfold tailWord_418766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909206350111222047993519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10182433867259850922632101 1909206350111222047993519)
  ·
    refine ⟨2863809525166833071990279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909206350111222047993519 2863809525166833071990279)
    ·
      refine ⟨4295714287750249607985419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863809525166833071990279 4295714287750249607985419)
      ·
        refine ⟨6443571431625374411978129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295714287750249607985419 6443571431625374411978129)
        ·
          refine ⟨4832678573719030808983597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443571431625374411978129 4832678573719030808983597)
          ·
            refine ⟨1812254465144636553368849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4832678573719030808983597 1812254465144636553368849)
            ·
              refine ⟨1359190848858477415026637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812254465144636553368849 1359190848858477415026637)
              ·
                refine ⟨509696568321929030634989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359190848858477415026637 509696568321929030634989)
                ·
                  refine ⟨191136213120723386488121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509696568321929030634989 191136213120723386488121)
                  ·
                    rfl

theorem cell20_418766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_418766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418766 prefixEnd_418766 := by exact prefixLift 418766
  have htrace : WordTrace (prefixWord ++ tailWord_418766) baseStart_418766 baseEnd_418766 := by
    simpa [prefixWord, tailWord_418766, baseEnd_418766] using wordTrace_append hprefix tailTrace_418766
  have hstable : (prefixWord ++ tailWord_418766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418766).length < 2 ^ (prefixWord ++ tailWord_418766).sum := by decide
  have hdescent : baseEnd_418766 < baseStart_418766 := by decide
  rcases family_descends (prefixWord ++ tailWord_418766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418786 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_418786 : Nat := 118140960795 + 418786 * 2 ^ 59
def prefixEnd_418786 : Nat := 4983230072969 + 3 ^ 40 * 418786 * 2
def baseEnd_418786 : Nat := 191145341665692205821373

theorem tailTrace_418786 : CollatzResearch.WordTrace tailWord_418786 prefixEnd_418786 191145341665692205821373 := by
  unfold tailWord_418786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818595065204329949919053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10182920173878213199784141 3818595065204329949919053)
  ·
    refine ⟨1431973149451623731219645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3818595065204329949919053 1431973149451623731219645)
    ·
      refine ⟨536989931044358899207367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1431973149451623731219645 536989931044358899207367)
      ·
        refine ⟨805484896566538348811051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536989931044358899207367 805484896566538348811051)
        ·
          refine ⟨1208227344849807523216577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805484896566538348811051 1208227344849807523216577)
          ·
            refine ⟨906170508637355642412433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208227344849807523216577 906170508637355642412433)
            ·
              refine ⟨679627881478016731809325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906170508637355642412433 679627881478016731809325)
              ·
                refine ⟨254860455554256274428497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679627881478016731809325 254860455554256274428497)
                ·
                  refine ⟨191145341665692205821373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254860455554256274428497 191145341665692205821373)
                  ·
                    rfl

theorem cell20_418786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_418786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418786 prefixEnd_418786 := by exact prefixLift 418786
  have htrace : WordTrace (prefixWord ++ tailWord_418786) baseStart_418786 baseEnd_418786 := by
    simpa [prefixWord, tailWord_418786, baseEnd_418786] using wordTrace_append hprefix tailTrace_418786
  have hstable : (prefixWord ++ tailWord_418786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418786).length < 2 ^ (prefixWord ++ tailWord_418786).sum := by decide
  have hdescent : baseEnd_418786 < baseStart_418786 := by decide
  rcases family_descends (prefixWord ++ tailWord_418786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418787 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_418787 : Nat := 118140960795 + 418787 * 2 ^ 59
def prefixEnd_418787 : Nat := 4983230072969 + 3 ^ 40 * 418787 * 2
def baseEnd_418787 : Nat := 191145798092940646788035

theorem tailTrace_418787 : CollatzResearch.WordTrace tailWord_418787 prefixEnd_418787 191145798092940646788035 := by
  unfold tailWord_418787
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274416733813696970462615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10182944489209131313641743 15274416733813696970462615)
  ·
    refine ⟨22911625100720545455693923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15274416733813696970462615 22911625100720545455693923)
    ·
      refine ⟨34367437651080818183540885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911625100720545455693923 34367437651080818183540885)
      ·
        refine ⟨1610973639894413352353479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34367437651080818183540885 1610973639894413352353479)
        ·
          refine ⟨2416460459841620028530219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610973639894413352353479 2416460459841620028530219)
          ·
            refine ⟨3624690689762430042795329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416460459841620028530219 3624690689762430042795329)
            ·
              refine ⟨2718518017321822532096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624690689762430042795329 2718518017321822532096497)
              ·
                refine ⟨2038888512991366899072373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718518017321822532096497 2038888512991366899072373)
                ·
                  refine ⟨191145798092940646788035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038888512991366899072373 191145798092940646788035)
                  ·
                    rfl

theorem cell20_418787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_418787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418787 prefixEnd_418787 := by exact prefixLift 418787
  have htrace : WordTrace (prefixWord ++ tailWord_418787) baseStart_418787 baseEnd_418787 := by
    simpa [prefixWord, tailWord_418787, baseEnd_418787] using wordTrace_append hprefix tailTrace_418787
  have hstable : (prefixWord ++ tailWord_418787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418787).length < 2 ^ (prefixWord ++ tailWord_418787).sum := by decide
  have hdescent : baseEnd_418787 < baseStart_418787 := by decide
  rcases family_descends (prefixWord ++ tailWord_418787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418825 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_418825 : Nat := 118140960795 + 418825 * 2 ^ 59
def prefixEnd_418825 : Nat := 4983230072969 + 3 ^ 40 * 418825 * 2
def baseEnd_418825 : Nat := 191163142328381403521213

theorem tailTrace_418825 : CollatzResearch.WordTrace tailWord_418825 prefixEnd_418825 191163142328381403521213 := by
  unfold tailWord_418825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15275802707676029460345929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10183868471784019640230619 15275802707676029460345929)
  ·
    refine ⟨11456852030757022095259447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15275802707676029460345929 11456852030757022095259447)
    ·
      refine ⟨17185278046135533142889171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11456852030757022095259447 17185278046135533142889171)
      ·
        refine ⟨25777917069203299714333757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17185278046135533142889171 25777917069203299714333757)
        ·
          refine ⟨9666718900951237392875159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25777917069203299714333757 9666718900951237392875159)
          ·
            refine ⟨14500078351426856089312739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666718900951237392875159 14500078351426856089312739)
            ·
              refine ⟨21750117527140284133969109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14500078351426856089312739 21750117527140284133969109)
              ·
                refine ⟨509768379542350409389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21750117527140284133969109 509768379542350409389901)
                ·
                  refine ⟨191163142328381403521213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509768379542350409389901 191163142328381403521213)
                  ·
                    rfl

theorem cell20_418825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_418825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418825 prefixEnd_418825 := by exact prefixLift 418825
  have htrace : WordTrace (prefixWord ++ tailWord_418825) baseStart_418825 baseEnd_418825 := by
    simpa [prefixWord, tailWord_418825, baseEnd_418825] using wordTrace_append hprefix tailTrace_418825
  have hstable : (prefixWord ++ tailWord_418825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418825).length < 2 ^ (prefixWord ++ tailWord_418825).sum := by decide
  have hdescent : baseEnd_418825 < baseStart_418825 := by decide
  rcases family_descends (prefixWord ++ tailWord_418825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418921 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 2]
def baseStart_418921 : Nat := 118140960795 + 418921 * 2 ^ 59
def prefixEnd_418921 : Nat := 4983230072969 + 3 ^ 40 * 418921 * 2
def baseEnd_418921 : Nat := 191206959344231736320821

theorem tailTrace_418921 : CollatzResearch.WordTrace tailWord_418921 prefixEnd_418921 191206959344231736320821 := by
  unfold tailWord_418921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279304115328237855840617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10186202743552158570560411 15279304115328237855840617)
  ·
    refine ⟨11459478086496178391880463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15279304115328237855840617 11459478086496178391880463)
    ·
      refine ⟨17189217129744267587820695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459478086496178391880463 17189217129744267587820695)
      ·
        refine ⟨25783825694616401381731043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189217129744267587820695 25783825694616401381731043)
        ·
          refine ⟨38675738541924602072596565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25783825694616401381731043 38675738541924602072596565)
          ·
            refine ⟨453231311038178930538241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 38675738541924602072596565 453231311038178930538241)
            ·
              refine ⟨339923483278634197903681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453231311038178930538241 339923483278634197903681)
              ·
                refine ⟨254942612458975648427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339923483278634197903681 254942612458975648427761)
                ·
                  refine ⟨191206959344231736320821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254942612458975648427761 191206959344231736320821)
                  ·
                    rfl

theorem cell20_418921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_418921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418921 prefixEnd_418921 := by exact prefixLift 418921
  have htrace : WordTrace (prefixWord ++ tailWord_418921) baseStart_418921 baseEnd_418921 := by
    simpa [prefixWord, tailWord_418921, baseEnd_418921] using wordTrace_append hprefix tailTrace_418921
  have hstable : (prefixWord ++ tailWord_418921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418921).length < 2 ^ (prefixWord ++ tailWord_418921).sum := by decide
  have hdescent : baseEnd_418921 < baseStart_418921 := by decide
  rcases family_descends (prefixWord ++ tailWord_418921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418949 : List Nat := [1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_418949 : Nat := 118140960795 + 418949 * 2 ^ 59
def prefixEnd_418949 : Nat := 4983230072969 + 3 ^ 40 * 418949 * 2
def baseEnd_418949 : Nat := 63739913102396027795791

theorem tailTrace_418949 : CollatzResearch.WordTrace tailWord_418949 prefixEnd_418949 63739913102396027795791 := by
  unfold tailWord_418949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280325359226798637859901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10186883572817865758573267 15280325359226798637859901)
  ·
    refine ⟨5730122009710049489197463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15280325359226798637859901 5730122009710049489197463)
    ·
      refine ⟨8595183014565074233796195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730122009710049489197463 8595183014565074233796195)
      ·
        refine ⟨12892774521847611350694293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595183014565074233796195 12892774521847611350694293)
        ·
          refine ⟨604348805711606782063795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12892774521847611350694293 604348805711606782063795)
          ·
            refine ⟨906523208567410173095693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604348805711606782063795 906523208567410173095693)
            ·
              refine ⟨339946203212778814910885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906523208567410173095693 339946203212778814910885)
              ·
                refine ⟨63739913102396027795791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339946203212778814910885 63739913102396027795791)
                ·
                  rfl

theorem cell20_418949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_418949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418949 prefixEnd_418949 := by exact prefixLift 418949
  have htrace : WordTrace (prefixWord ++ tailWord_418949) baseStart_418949 baseEnd_418949 := by
    simpa [prefixWord, tailWord_418949, baseEnd_418949] using wordTrace_append hprefix tailTrace_418949
  have hstable : (prefixWord ++ tailWord_418949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418949).length < 2 ^ (prefixWord ++ tailWord_418949).sum := by decide
  have hdescent : baseEnd_418949 < baseStart_418949 := by decide
  rcases family_descends (prefixWord ++ tailWord_418949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418963 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 2]
def baseStart_418963 : Nat := 118140960795 + 418963 * 2 ^ 59
def prefixEnd_418963 : Nat := 4983230072969 + 3 ^ 40 * 418963 * 2
def baseEnd_418963 : Nat := 191226129288666256920649

theorem tailTrace_418963 : CollatzResearch.WordTrace tailWord_418963 prefixEnd_418963 191226129288666256920649 := by
  unfold tailWord_418963
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280835981176079028869543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10187223987450719352579695 15280835981176079028869543)
  ·
    refine ⟨22921253971764118543304315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15280835981176079028869543 22921253971764118543304315)
    ·
      refine ⟨34381880957646177814956473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22921253971764118543304315 34381880957646177814956473)
      ·
        refine ⟨25786410718234633361217355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34381880957646177814956473 25786410718234633361217355)
        ·
          refine ⟨38679616077351950041826033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25786410718234633361217355 38679616077351950041826033)
          ·
            refine ⟨29009712058013962531369525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38679616077351950041826033 29009712058013962531369525)
            ·
              refine ⟨2719660505438808987315893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29009712058013962531369525 2719660505438808987315893)
              ·
                refine ⟨254968172384888342560865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2719660505438808987315893 254968172384888342560865)
                ·
                  refine ⟨191226129288666256920649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254968172384888342560865 191226129288666256920649)
                  ·
                    rfl

theorem cell20_418963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 2].length) (baseStart_418963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418963 prefixEnd_418963 := by exact prefixLift 418963
  have htrace : WordTrace (prefixWord ++ tailWord_418963) baseStart_418963 baseEnd_418963 := by
    simpa [prefixWord, tailWord_418963, baseEnd_418963] using wordTrace_append hprefix tailTrace_418963
  have hstable : (prefixWord ++ tailWord_418963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418963).length < 2 ^ (prefixWord ++ tailWord_418963).sum := by decide
  have hdescent : baseEnd_418963 < baseStart_418963 := by decide
  rcases family_descends (prefixWord ++ tailWord_418963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418970 : List Nat := [3, 1, 1, 5, 1, 2, 7]
def baseStart_418970 : Nat := 118140960795 + 418970 * 2 ^ 59
def prefixEnd_418970 : Nat := 4983230072969 + 3 ^ 40 * 418970 * 2
def baseEnd_418970 : Nat := 21247702697711704854143

theorem tailTrace_418970 : CollatzResearch.WordTrace tailWord_418970 prefixEnd_418970 21247702697711704854143 := by
  unfold tailWord_418970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820272823037679806093591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10187394194767146149582909 3820272823037679806093591)
  ·
    refine ⟨5730409234556519709140387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3820272823037679806093591 5730409234556519709140387)
    ·
      refine ⟨8595613851834779563710581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730409234556519709140387 8595613851834779563710581)
      ·
        refine ⟨805838798609510584097867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8595613851834779563710581 805838798609510584097867)
        ·
          refine ⟨1208758197914265876146801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805838798609510584097867 1208758197914265876146801)
          ·
            refine ⟨906568648435699407110101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208758197914265876146801 906568648435699407110101)
            ·
              refine ⟨21247702697711704854143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 906568648435699407110101 21247702697711704854143)
              ·
                rfl

theorem cell20_418970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_418970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418970 prefixEnd_418970 := by exact prefixLift 418970
  have htrace : WordTrace (prefixWord ++ tailWord_418970) baseStart_418970 baseEnd_418970 := by
    simpa [prefixWord, tailWord_418970, baseEnd_418970] using wordTrace_append hprefix tailTrace_418970
  have hstable : (prefixWord ++ tailWord_418970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418970).length < 2 ^ (prefixWord ++ tailWord_418970).sum := by decide
  have hdescent : baseEnd_418970 < baseStart_418970 := by decide
  rcases family_descends (prefixWord ++ tailWord_418970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418977 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_418977 : Nat := 118140960795 + 418977 * 2 ^ 59
def prefixEnd_418977 : Nat := 4983230072969 + 3 ^ 40 * 418977 * 2
def baseEnd_418977 : Nat := 191232519270144430453925

theorem tailTrace_418977 : CollatzResearch.WordTrace tailWord_418977 prefixEnd_418977 191232519270144430453925 := by
  unfold tailWord_418977
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281346603125359419879185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10187564402083572946586123 15281346603125359419879185)
  ·
    refine ⟨11461009952344019564909389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15281346603125359419879185 11461009952344019564909389)
    ·
      refine ⟨4297878732129007336841021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11461009952344019564909389 4297878732129007336841021)
      ·
        refine ⟨1611704524548377751315383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4297878732129007336841021 1611704524548377751315383)
        ·
          refine ⟨2417556786822566626973075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611704524548377751315383 2417556786822566626973075)
          ·
            refine ⟨3626335180233849940459613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417556786822566626973075 3626335180233849940459613)
            ·
              refine ⟨1359875692587693727672355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3626335180233849940459613 1359875692587693727672355)
              ·
                refine ⟨2039813538881540591508533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359875692587693727672355 2039813538881540591508533)
                ·
                  refine ⟨191232519270144430453925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039813538881540591508533 191232519270144430453925)
                  ·
                    rfl

theorem cell20_418977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_418977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418977 prefixEnd_418977 := by exact prefixLift 418977
  have htrace : WordTrace (prefixWord ++ tailWord_418977) baseStart_418977 baseEnd_418977 := by
    simpa [prefixWord, tailWord_418977, baseEnd_418977] using wordTrace_append hprefix tailTrace_418977
  have hstable : (prefixWord ++ tailWord_418977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418977).length < 2 ^ (prefixWord ++ tailWord_418977).sum := by decide
  have hdescent : baseEnd_418977 < baseStart_418977 := by decide
  rcases family_descends (prefixWord ++ tailWord_418977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418980 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_418980 : Nat := 118140960795 + 418980 * 2 ^ 59
def prefixEnd_418980 : Nat := 4983230072969 + 3 ^ 40 * 418980 * 2
def baseEnd_418980 : Nat := 191233888551889753353913

theorem tailTrace_418980 : CollatzResearch.WordTrace tailWord_418980 prefixEnd_418980 191233888551889753353913 := by
  unfold tailWord_418980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640728011057245466119197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10187637348076327288158929 7640728011057245466119197)
  ·
    refine ⟨2865273004146467049794699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7640728011057245466119197 2865273004146467049794699)
    ·
      refine ⟨4297909506219700574692049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865273004146467049794699 4297909506219700574692049)
      ·
        refine ⟨3223432129664775431019037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4297909506219700574692049 3223432129664775431019037)
        ·
          refine ⟨1208787048624290786632139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3223432129664775431019037 1208787048624290786632139)
          ·
            refine ⟨1813180572936436179948209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208787048624290786632139 1813180572936436179948209)
            ·
              refine ⟨1359885429702327134961157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813180572936436179948209 1359885429702327134961157)
              ·
                refine ⟨254978518069186337805217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1359885429702327134961157 254978518069186337805217)
                ·
                  refine ⟨191233888551889753353913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254978518069186337805217 191233888551889753353913)
                  ·
                    rfl

theorem cell20_418980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_418980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_418980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_418980 prefixEnd_418980 := by exact prefixLift 418980
  have htrace : WordTrace (prefixWord ++ tailWord_418980) baseStart_418980 baseEnd_418980 := by
    simpa [prefixWord, tailWord_418980, baseEnd_418980] using wordTrace_append hprefix tailTrace_418980
  have hstable : (prefixWord ++ tailWord_418980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418980).length < 2 ^ (prefixWord ++ tailWord_418980).sum := by decide
  have hdescent : baseEnd_418980 < baseStart_418980 := by decide
  rcases family_descends (prefixWord ++ tailWord_418980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419008 : List Nat := [2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_419008 : Nat := 118140960795 + 419008 * 2 ^ 59
def prefixEnd_419008 : Nat := 4983230072969 + 3 ^ 40 * 419008 * 2
def baseEnd_419008 : Nat := 63748889504948700140155

theorem tailTrace_419008 : CollatzResearch.WordTrace tailWord_419008 prefixEnd_419008 63748889504948700140155 := by
  unfold tailWord_419008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641238633006525857128839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10188318177342034476171785 7641238633006525857128839)
  ·
    refine ⟨11461857949509788785693259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641238633006525857128839 11461857949509788785693259)
    ·
      refine ⟨17192786924264683178539889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11461857949509788785693259 17192786924264683178539889)
      ·
        refine ⟨12894590193198512383904917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17192786924264683178539889 12894590193198512383904917)
        ·
          refine ⟨604433915306180267995543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12894590193198512383904917 604433915306180267995543)
          ·
            refine ⟨906650872959270401993315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604433915306180267995543 906650872959270401993315)
            ·
              refine ⟨1359976309438905602989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906650872959270401993315 1359976309438905602989973)
              ·
                refine ⟨63748889504948700140155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1359976309438905602989973 63748889504948700140155)
                ·
                  rfl

theorem cell20_419008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_419008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419008 prefixEnd_419008 := by exact prefixLift 419008
  have htrace : WordTrace (prefixWord ++ tailWord_419008) baseStart_419008 baseEnd_419008 := by
    simpa [prefixWord, tailWord_419008, baseEnd_419008] using wordTrace_append hprefix tailTrace_419008
  have hstable : (prefixWord ++ tailWord_419008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419008).length < 2 ^ (prefixWord ++ tailWord_419008).sum := by decide
  have hdescent : baseEnd_419008 < baseStart_419008 := by decide
  rcases family_descends (prefixWord ++ tailWord_419008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419010 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_419010 : Nat := 118140960795 + 419010 * 2 ^ 59
def prefixEnd_419010 : Nat := 4983230072969 + 3 ^ 40 * 419010 * 2
def baseEnd_419010 : Nat := 191247581369342982353791

theorem tailTrace_419010 : CollatzResearch.WordTrace tailWord_419010 prefixEnd_419010 191247581369342982353791 := by
  unfold tailWord_419010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820637553001451513957621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10188366808003870703886989 3820637553001451513957621)
  ·
    refine ⟨358184770593886079433527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3820637553001451513957621 358184770593886079433527)
    ·
      refine ⟨537277155890829119150291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358184770593886079433527 537277155890829119150291)
      ·
        refine ⟨805915733836243678725437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537277155890829119150291 805915733836243678725437)
        ·
          refine ⟨302218400188591379522039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805915733836243678725437 302218400188591379522039)
          ·
            refine ⟨453327600282887069283059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302218400188591379522039 453327600282887069283059)
            ·
              refine ⟨679991400424330603924589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453327600282887069283059 679991400424330603924589)
              ·
                refine ⟨254996775159123976471721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679991400424330603924589 254996775159123976471721)
                ·
                  refine ⟨191247581369342982353791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254996775159123976471721 191247581369342982353791)
                  ·
                    rfl

theorem cell20_419010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_419010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419010 prefixEnd_419010 := by exact prefixLift 419010
  have htrace : WordTrace (prefixWord ++ tailWord_419010) baseStart_419010 baseEnd_419010 := by
    simpa [prefixWord, tailWord_419010, baseEnd_419010] using wordTrace_append hprefix tailTrace_419010
  have hstable : (prefixWord ++ tailWord_419010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419010).length < 2 ^ (prefixWord ++ tailWord_419010).sum := by decide
  have hdescent : baseEnd_419010 < baseStart_419010 := by decide
  rcases family_descends (prefixWord ++ tailWord_419010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419018 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_419018 : Nat := 118140960795 + 419018 * 2 ^ 59
def prefixEnd_419018 : Nat := 4983230072969 + 3 ^ 40 * 419018 * 2
def baseEnd_419018 : Nat := 191251232787330510087091

theorem tailTrace_419018 : CollatzResearch.WordTrace tailWord_419018 prefixEnd_419018 191251232787330510087091 := by
  unfold tailWord_419018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820710498994205855530427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10188561330651215614747805 3820710498994205855530427)
  ·
    refine ⟨5731065748491308783295641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3820710498994205855530427 5731065748491308783295641)
    ·
      refine ⟨4298299311368481587471731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5731065748491308783295641 4298299311368481587471731)
      ·
        refine ⟨6447448967052722381207597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298299311368481587471731 6447448967052722381207597)
        ·
          refine ⟨2417793362644770892952849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6447448967052722381207597 2417793362644770892952849)
          ·
            refine ⟨1813345021983578169714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417793362644770892952849 1813345021983578169714637)
            ·
              refine ⟨680004383243841813642989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1813345021983578169714637 680004383243841813642989)
              ·
                refine ⟨255001643716440680116121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680004383243841813642989 255001643716440680116121)
                ·
                  refine ⟨191251232787330510087091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255001643716440680116121 191251232787330510087091)
                  ·
                    rfl

theorem cell20_419018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_419018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419018 prefixEnd_419018 := by exact prefixLift 419018
  have htrace : WordTrace (prefixWord ++ tailWord_419018) baseStart_419018 baseEnd_419018 := by
    simpa [prefixWord, tailWord_419018, baseEnd_419018] using wordTrace_append hprefix tailTrace_419018
  have hstable : (prefixWord ++ tailWord_419018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419018).length < 2 ^ (prefixWord ++ tailWord_419018).sum := by decide
  have hdescent : baseEnd_419018 < baseStart_419018 := by decide
  rcases family_descends (prefixWord ++ tailWord_419018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419021 : List Nat := [1, 6, 2, 2, 2, 1, 6]
def baseStart_419021 : Nat := 118140960795 + 419021 * 2 ^ 59
def prefixEnd_419021 : Nat := 4983230072969 + 3 ^ 40 * 419021 * 2
def baseEnd_419021 : Nat := 21250289118786203665231

theorem tailTrace_419021 : CollatzResearch.WordTrace tailWord_419021 prefixEnd_419021 21250289118786203665231 := by
  unfold tailWord_419021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282951414965954934480917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10188634276643969956320611 15282951414965954934480917)
  ·
    refine ⟨716388347576529137553793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15282951414965954934480917 716388347576529137553793)
    ·
      refine ⟨537291260682396853165345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 716388347576529137553793 537291260682396853165345)
      ·
        refine ⟨402968445511797639874009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537291260682396853165345 402968445511797639874009)
        ·
          refine ⟨302226334133848229905507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402968445511797639874009 302226334133848229905507)
          ·
            refine ⟨453339501200772344858261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302226334133848229905507 453339501200772344858261)
            ·
              refine ⟨21250289118786203665231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 453339501200772344858261 21250289118786203665231)
              ·
                rfl

theorem cell20_419021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_419021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419021 prefixEnd_419021 := by exact prefixLift 419021
  have htrace : WordTrace (prefixWord ++ tailWord_419021) baseStart_419021 baseEnd_419021 := by
    simpa [prefixWord, tailWord_419021, baseEnd_419021] using wordTrace_append hprefix tailTrace_419021
  have hstable : (prefixWord ++ tailWord_419021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419021).length < 2 ^ (prefixWord ++ tailWord_419021).sum := by decide
  have hdescent : baseEnd_419021 < baseStart_419021 := by decide
  rcases family_descends (prefixWord ++ tailWord_419021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419039 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 2]
def baseStart_419039 : Nat := 118140960795 + 419039 * 2 ^ 59
def prefixEnd_419039 : Nat := 4983230072969 + 3 ^ 40 * 419039 * 2
def baseEnd_419039 : Nat := 191260817759547770387005

theorem tailTrace_419039 : CollatzResearch.WordTrace tailWord_419039 prefixEnd_419039 191260817759547770387005 := by
  unfold tailWord_419039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283607928900744008636171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189071952600496005757447 15283607928900744008636171)
  ·
    refine ⟨22925411893351116012954257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283607928900744008636171 22925411893351116012954257)
    ·
      refine ⟨17194058920013337009715693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22925411893351116012954257 17194058920013337009715693)
      ·
        refine ⟨6447772095005001378643385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17194058920013337009715693 6447772095005001378643385)
        ·
          refine ⟨4835829071253751033982539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6447772095005001378643385 4835829071253751033982539)
          ·
            refine ⟨7253743606880626550973809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835829071253751033982539 7253743606880626550973809)
            ·
              refine ⟨5440307705160469913230357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7253743606880626550973809 5440307705160469913230357)
              ·
                refine ⟨255014423679397027182673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5440307705160469913230357 255014423679397027182673)
                ·
                  refine ⟨191260817759547770387005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255014423679397027182673 191260817759547770387005)
                  ·
                    rfl

theorem cell20_419039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2].length) (baseStart_419039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419039 prefixEnd_419039 := by exact prefixLift 419039
  have htrace : WordTrace (prefixWord ++ tailWord_419039) baseStart_419039 baseEnd_419039 := by
    simpa [prefixWord, tailWord_419039, baseEnd_419039] using wordTrace_append hprefix tailTrace_419039
  have hstable : (prefixWord ++ tailWord_419039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419039).length < 2 ^ (prefixWord ++ tailWord_419039).sum := by decide
  have hdescent : baseEnd_419039 < baseStart_419039 := by decide
  rcases family_descends (prefixWord ++ tailWord_419039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419077 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 2]
def baseStart_419077 : Nat := 118140960795 + 419077 * 2 ^ 59
def prefixEnd_419077 : Nat := 4983230072969 + 3 ^ 40 * 419077 * 2
def baseEnd_419077 : Nat := 191278161994988527120183

theorem tailTrace_419077 : CollatzResearch.WordTrace tailWord_419077 prefixEnd_419077 191278161994988527120183 := by
  unfold tailWord_419077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284993902763076498519485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189995935175384332346323 15284993902763076498519485)
  ·
    refine ⟨5731872713536153686944807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15284993902763076498519485 5731872713536153686944807)
    ·
      refine ⟨8597809070304230530417211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731872713536153686944807 8597809070304230530417211)
      ·
        refine ⟨12896713605456345795625817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597809070304230530417211 12896713605456345795625817)
        ·
          refine ⟨9672535204092259346719363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12896713605456345795625817 9672535204092259346719363)
          ·
            refine ⟨14508802806138389020079045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9672535204092259346719363 14508802806138389020079045)
            ·
              refine ⟨2720400526150947941264821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14508802806138389020079045 2720400526150947941264821)
              ·
                refine ⟨255037549326651369493577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2720400526150947941264821 255037549326651369493577)
                ·
                  refine ⟨191278161994988527120183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255037549326651369493577 191278161994988527120183)
                  ·
                    rfl

theorem cell20_419077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_419077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419077 prefixEnd_419077 := by exact prefixLift 419077
  have htrace : WordTrace (prefixWord ++ tailWord_419077) baseStart_419077 baseEnd_419077 := by
    simpa [prefixWord, tailWord_419077, baseEnd_419077] using wordTrace_append hprefix tailTrace_419077
  have hstable : (prefixWord ++ tailWord_419077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419077).length < 2 ^ (prefixWord ++ tailWord_419077).sum := by decide
  have hdescent : baseEnd_419077 < baseStart_419077 := by decide
  rcases family_descends (prefixWord ++ tailWord_419077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419090 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_419090 : Nat := 118140960795 + 419090 * 2 ^ 59
def prefixEnd_419090 : Nat := 4983230072969 + 3 ^ 40 * 419090 * 2
def baseEnd_419090 : Nat := 191284095549218259686797

theorem tailTrace_419090 : CollatzResearch.WordTrace tailWord_419090 prefixEnd_419090 191284095549218259686797 := by
  unfold tailWord_419090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821367012928994929685681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10190312034477319812495149 3821367012928994929685681)
  ·
    refine ⟨2866025259696746197264261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821367012928994929685681 2866025259696746197264261)
    ·
      refine ⟨537379736193139911987049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2866025259696746197264261 537379736193139911987049)
      ·
        refine ⟨403034802144854933990287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537379736193139911987049 403034802144854933990287)
        ·
          refine ⟨604552203217282400985431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403034802144854933990287 604552203217282400985431)
          ·
            refine ⟨906828304825923601478147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604552203217282400985431 906828304825923601478147)
            ·
              refine ⟨1360242457238885402217221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906828304825923601478147 1360242457238885402217221)
              ·
                refine ⟨255045460732291012915729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1360242457238885402217221 255045460732291012915729)
                ·
                  refine ⟨191284095549218259686797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255045460732291012915729 191284095549218259686797)
                  ·
                    rfl

theorem cell20_419090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_419090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419090 prefixEnd_419090 := by exact prefixLift 419090
  have htrace : WordTrace (prefixWord ++ tailWord_419090) baseStart_419090 baseEnd_419090 := by
    simpa [prefixWord, tailWord_419090, baseEnd_419090] using wordTrace_append hprefix tailTrace_419090
  have hstable : (prefixWord ++ tailWord_419090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419090).length < 2 ^ (prefixWord ++ tailWord_419090).sum := by decide
  have hdescent : baseEnd_419090 < baseStart_419090 := by decide
  rcases family_descends (prefixWord ++ tailWord_419090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419101 : List Nat := [1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_419101 : Nat := 118140960795 + 419101 * 2 ^ 59
def prefixEnd_419101 : Nat := 4983230072969 + 3 ^ 40 * 419101 * 2
def baseEnd_419101 : Nat := 63763038749650370106695

theorem tailTrace_419101 : CollatzResearch.WordTrace tailWord_419101 prefixEnd_419101 63763038749650370106695 := by
  unfold tailWord_419101
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285869254676128597393157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10190579503117419064928771 15285869254676128597393157)
  ·
    refine ⟨2866100485251774112011217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15285869254676128597393157 2866100485251774112011217)
    ·
      refine ⟨2149575363938830584008413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2866100485251774112011217 2149575363938830584008413)
      ·
        refine ⟨806090761477061469003155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2149575363938830584008413 806090761477061469003155)
        ·
          refine ⟨1209136142215592203504733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806090761477061469003155 1209136142215592203504733)
          ·
            refine ⟨453426053330847076314275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1209136142215592203504733 453426053330847076314275)
            ·
              refine ⟨680139079996270614471413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453426053330847076314275 680139079996270614471413)
              ·
                refine ⟨63763038749650370106695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680139079996270614471413 63763038749650370106695)
                ·
                  rfl

theorem cell20_419101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_419101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419101 prefixEnd_419101 := by exact prefixLift 419101
  have htrace : WordTrace (prefixWord ++ tailWord_419101) baseStart_419101 baseEnd_419101 := by
    simpa [prefixWord, tailWord_419101, baseEnd_419101] using wordTrace_append hprefix tailTrace_419101
  have hstable : (prefixWord ++ tailWord_419101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419101).length < 2 ^ (prefixWord ++ tailWord_419101).sum := by decide
  have hdescent : baseEnd_419101 < baseStart_419101 := by decide
  rcases family_descends (prefixWord ++ tailWord_419101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419132 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_419132 : Nat := 118140960795 + 419132 * 2 ^ 59
def prefixEnd_419132 : Nat := 4983230072969 + 3 ^ 40 * 419132 * 2
def baseEnd_419132 : Nat := 191303265493652780286625

theorem tailTrace_419132 : CollatzResearch.WordTrace tailWord_419132 prefixEnd_419132 191303265493652780286625 := by
  unfold tailWord_419132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643499958781910445885825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10191333278375880594514433 7643499958781910445885825)
  ·
    refine ⟨5732624969086432834414369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7643499958781910445885825 5732624969086432834414369)
    ·
      refine ⟨4299468726814824625810777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5732624969086432834414369 4299468726814824625810777)
      ·
        refine ⟨3224601545111118469358083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4299468726814824625810777 3224601545111118469358083)
        ·
          refine ⟨4836902317666677704037125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224601545111118469358083 4836902317666677704037125)
          ·
            refine ⟨906919184562502069506961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4836902317666677704037125 906919184562502069506961)
            ·
              refine ⟨680189388421876552130221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906919184562502069506961 680189388421876552130221)
              ·
                refine ⟨255071020658203707048833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680189388421876552130221 255071020658203707048833)
                ·
                  refine ⟨191303265493652780286625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255071020658203707048833 191303265493652780286625)
                  ·
                    rfl

theorem cell20_419132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_419132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419132 prefixEnd_419132 := by exact prefixLift 419132
  have htrace : WordTrace (prefixWord ++ tailWord_419132) baseStart_419132 baseEnd_419132 := by
    simpa [prefixWord, tailWord_419132, baseEnd_419132] using wordTrace_append hprefix tailTrace_419132
  have hstable : (prefixWord ++ tailWord_419132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419132).length < 2 ^ (prefixWord ++ tailWord_419132).sum := by decide
  have hdescent : baseEnd_419132 < baseStart_419132 := by decide
  rcases family_descends (prefixWord ++ tailWord_419132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419142 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_419142 : Nat := 118140960795 + 419142 * 2 ^ 59
def prefixEnd_419142 : Nat := 4983230072969 + 3 ^ 40 * 419142 * 2
def baseEnd_419142 : Nat := 191307829766137189953251

theorem tailTrace_419142 : CollatzResearch.WordTrace tailWord_419142 prefixEnd_419142 191307829766137189953251 := by
  unfold tailWord_419142
  simp only [CollatzResearch.WordTrace]
  refine ⟨477730145235237268738615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10191576431685061733090453 477730145235237268738615)
  ·
    refine ⟨716595217852855903107923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 477730145235237268738615 716595217852855903107923)
    ·
      refine ⟨1074892826779283854661885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716595217852855903107923 1074892826779283854661885)
      ·
        refine ⟨403084810042231445498207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1074892826779283854661885 403084810042231445498207)
        ·
          refine ⟨604627215063347168247311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403084810042231445498207 604627215063347168247311)
          ·
            refine ⟨906940822595020752370967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604627215063347168247311 906940822595020752370967)
            ·
              refine ⟨1360411233892531128556451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906940822595020752370967 1360411233892531128556451)
              ·
                refine ⟨2040616850838796692834677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360411233892531128556451 2040616850838796692834677)
                ·
                  refine ⟨191307829766137189953251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040616850838796692834677 191307829766137189953251)
                  ·
                    rfl

theorem cell20_419142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_419142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419142 prefixEnd_419142 := by exact prefixLift 419142
  have htrace : WordTrace (prefixWord ++ tailWord_419142) baseStart_419142 baseEnd_419142 := by
    simpa [prefixWord, tailWord_419142, baseEnd_419142] using wordTrace_append hprefix tailTrace_419142
  have hstable : (prefixWord ++ tailWord_419142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419142).length < 2 ^ (prefixWord ++ tailWord_419142).sum := by decide
  have hdescent : baseEnd_419142 < baseStart_419142 := by decide
  rcases family_descends (prefixWord ++ tailWord_419142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419143 : List Nat := [1, 1, 4, 1, 2, 4, 7]
def baseStart_419143 : Nat := 118140960795 + 419143 * 2 ^ 59
def prefixEnd_419143 : Nat := 4983230072969 + 3 ^ 40 * 419143 * 2
def baseEnd_419143 : Nat := 21256476243709514546657

theorem tailTrace_419143 : CollatzResearch.WordTrace tailWord_419143 prefixEnd_419143 21256476243709514546657 := by
  unfold tailWord_419143
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287401120523969770422083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191600747015979846948055 15287401120523969770422083)
  ·
    refine ⟨22931101680785954655633125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15287401120523969770422083 22931101680785954655633125)
    ·
      refine ⟨4299581565147366497931211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22931101680785954655633125 4299581565147366497931211)
      ·
        refine ⟨6449372347721049746896817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299581565147366497931211 6449372347721049746896817)
        ·
          refine ⟨4837029260790787310172613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6449372347721049746896817 4837029260790787310172613)
          ·
            refine ⟨906942986398272620657365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4837029260790787310172613 906942986398272620657365)
            ·
              refine ⟨21256476243709514546657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 906942986398272620657365 21256476243709514546657)
              ·
                rfl

theorem cell20_419143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_419143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419143 prefixEnd_419143 := by exact prefixLift 419143
  have htrace : WordTrace (prefixWord ++ tailWord_419143) baseStart_419143 baseEnd_419143 := by
    simpa [prefixWord, tailWord_419143, baseEnd_419143] using wordTrace_append hprefix tailTrace_419143
  have hstable : (prefixWord ++ tailWord_419143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419143).length < 2 ^ (prefixWord ++ tailWord_419143).sum := by decide
  have hdescent : baseEnd_419143 < baseStart_419143 := by decide
  rcases family_descends (prefixWord ++ tailWord_419143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419149 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_419149 : Nat := 118140960795 + 419149 * 2 ^ 59
def prefixEnd_419149 : Nat := 4983230072969 + 3 ^ 40 * 419149 * 2
def baseEnd_419149 : Nat := 191311024756876276719889

theorem tailTrace_419149 : CollatzResearch.WordTrace tailWord_419149 prefixEnd_419149 191311024756876276719889 := by
  unfold tailWord_419149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287619958502232795140501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191746639001488530093667 15287619958502232795140501)
  ·
    refine ⟨716607185554792162272211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15287619958502232795140501 716607185554792162272211)
    ·
      refine ⟨1074910778332188243408317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716607185554792162272211 1074910778332188243408317)
      ·
        refine ⟨403091541874570591278119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1074910778332188243408317 403091541874570591278119)
        ·
          refine ⟨604637312811855886917179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403091541874570591278119 604637312811855886917179)
          ·
            refine ⟨906955969217783830375769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604637312811855886917179 906955969217783830375769)
            ·
              refine ⟨680216976913337872781827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906955969217783830375769 680216976913337872781827)
              ·
                refine ⟨1020325465370006809172741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680216976913337872781827 1020325465370006809172741)
                ·
                  refine ⟨191311024756876276719889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020325465370006809172741 191311024756876276719889)
                  ·
                    rfl

theorem cell20_419149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_419149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419149 prefixEnd_419149 := by exact prefixLift 419149
  have htrace : WordTrace (prefixWord ++ tailWord_419149) baseStart_419149 baseEnd_419149 := by
    simpa [prefixWord, tailWord_419149, baseEnd_419149] using wordTrace_append hprefix tailTrace_419149
  have hstable : (prefixWord ++ tailWord_419149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419149).length < 2 ^ (prefixWord ++ tailWord_419149).sum := by decide
  have hdescent : baseEnd_419149 < baseStart_419149 := by decide
  rcases family_descends (prefixWord ++ tailWord_419149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419153 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 2]
def baseStart_419153 : Nat := 118140960795 + 419153 * 2 ^ 59
def prefixEnd_419153 : Nat := 4983230072969 + 3 ^ 40 * 419153 * 2
def baseEnd_419153 : Nat := 191312850465870040586539

theorem tailTrace_419153 : CollatzResearch.WordTrace tailWord_419153 prefixEnd_419153 191312850465870040586539 := by
  unfold tailWord_419153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287765850487741478286113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191843900325160985524075 15287765850487741478286113)
  ·
    refine ⟨11465824387865806108714585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15287765850487741478286113 11465824387865806108714585)
    ·
      refine ⟨8599368290899354581535939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11465824387865806108714585 8599368290899354581535939)
      ·
        refine ⟨12899052436349031872303909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8599368290899354581535939 12899052436349031872303909)
        ·
          refine ⟨2418572331815443476056983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12899052436349031872303909 2418572331815443476056983)
          ·
            refine ⟨3627858497723165214085475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418572331815443476056983 3627858497723165214085475)
            ·
              refine ⟨5441787746584747821128213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627858497723165214085475 5441787746584747821128213)
              ·
                refine ⟨255083800621160054115385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5441787746584747821128213 255083800621160054115385)
                ·
                  refine ⟨191312850465870040586539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255083800621160054115385 191312850465870040586539)
                  ·
                    rfl

theorem cell20_419153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_419153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419153 prefixEnd_419153 := by exact prefixLift 419153
  have htrace : WordTrace (prefixWord ++ tailWord_419153) baseStart_419153 baseEnd_419153 := by
    simpa [prefixWord, tailWord_419153, baseEnd_419153] using wordTrace_append hprefix tailTrace_419153
  have hstable : (prefixWord ++ tailWord_419153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419153).length < 2 ^ (prefixWord ++ tailWord_419153).sum := by decide
  have hdescent : baseEnd_419153 < baseStart_419153 := by decide
  rcases family_descends (prefixWord ++ tailWord_419153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419257 : List Nat := [1, 2, 1, 4, 4, 8]
def baseStart_419257 : Nat := 118140960795 + 419257 * 2 ^ 59
def prefixEnd_419257 : Nat := 4983230072969 + 3 ^ 40 * 419257 * 2
def baseEnd_419257 : Nat := 7087419218507700041461

theorem tailTrace_419257 : CollatzResearch.WordTrace tailWord_419257 prefixEnd_419257 7087419218507700041461 := by
  unfold tailWord_419257
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291559042110967240072025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10194372694740644826714683 15291559042110967240072025)
  ·
    refine ⟨11468669281583225430054019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15291559042110967240072025 11468669281583225430054019)
    ·
      refine ⟨17203003922374838145081029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11468669281583225430054019 17203003922374838145081029)
      ·
        refine ⟨3225563235445282152202693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17203003922374838145081029 3225563235445282152202693)
        ·
          refine ⟨604793106645990403538005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3225563235445282152202693 604793106645990403538005)
          ·
            refine ⟨7087419218507700041461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 604793106645990403538005 7087419218507700041461)
            ·
              rfl

theorem cell20_419257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_419257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419257 prefixEnd_419257 := by exact prefixLift 419257
  have htrace : WordTrace (prefixWord ++ tailWord_419257) baseStart_419257 baseEnd_419257 := by
    simpa [prefixWord, tailWord_419257, baseEnd_419257] using wordTrace_append hprefix tailTrace_419257
  have hstable : (prefixWord ++ tailWord_419257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419257).length < 2 ^ (prefixWord ++ tailWord_419257).sum := by decide
  have hdescent : baseEnd_419257 < baseStart_419257 := by decide
  rcases family_descends (prefixWord ++ tailWord_419257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419264 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_419264 : Nat := 118140960795 + 419264 * 2 ^ 59
def prefixEnd_419264 : Nat := 4983230072969 + 3 ^ 40 * 419264 * 2
def baseEnd_419264 : Nat := 191363513890446987886085

theorem tailTrace_419264 : CollatzResearch.WordTrace tailWord_419264 prefixEnd_419264 191363513890446987886085 := by
  unfold tailWord_419264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645907176542803717788423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10194542902057071623717897 7645907176542803717788423)
  ·
    refine ⟨11468860764814205576682635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7645907176542803717788423 11468860764814205576682635)
    ·
      refine ⟨17203291147221308365023953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11468860764814205576682635 17203291147221308365023953)
      ·
        refine ⟨12902468360415981273767965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17203291147221308365023953 12902468360415981273767965)
        ·
          refine ⟨4838425635155992977662987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12902468360415981273767965 4838425635155992977662987)
          ·
            refine ⟨7257638452733989466494481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838425635155992977662987 7257638452733989466494481)
            ·
              refine ⟨5443228839550492099870861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7257638452733989466494481 5443228839550492099870861)
              ·
                refine ⟨2041210814831434537451573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443228839550492099870861 2041210814831434537451573)
                ·
                  refine ⟨191363513890446987886085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041210814831434537451573 191363513890446987886085)
                  ·
                    rfl

theorem cell20_419264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_419264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419264 prefixEnd_419264 := by exact prefixLift 419264
  have htrace : WordTrace (prefixWord ++ tailWord_419264) baseStart_419264 baseEnd_419264 := by
    simpa [prefixWord, tailWord_419264, baseEnd_419264] using wordTrace_append hprefix tailTrace_419264
  have hstable : (prefixWord ++ tailWord_419264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419264).length < 2 ^ (prefixWord ++ tailWord_419264).sum := by decide
  have hdescent : baseEnd_419264 < baseStart_419264 := by decide
  rcases family_descends (prefixWord ++ tailWord_419264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419266 : List Nat := [3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_419266 : Nat := 118140960795 + 419266 * 2 ^ 59
def prefixEnd_419266 : Nat := 4983230072969 + 3 ^ 40 * 419266 * 2
def baseEnd_419266 : Nat := 63788142248314623273137

theorem tailTrace_419266 : CollatzResearch.WordTrace tailWord_419266 prefixEnd_419266 63788142248314623273137 := by
  unfold tailWord_419266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822971824769590444287413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10194591532718907851433101 3822971824769590444287413)
  ·
    refine ⟨358403608572149104151945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3822971824769590444287413 358403608572149104151945)
    ·
      refine ⟨268802706429111828113959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358403608572149104151945 268802706429111828113959)
      ·
        refine ⟨403204059643667742170939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268802706429111828113959 403204059643667742170939)
        ·
          refine ⟨604806089465501613256409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403204059643667742170939 604806089465501613256409)
          ·
            refine ⟨453604567099126209942307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604806089465501613256409 453604567099126209942307)
            ·
              refine ⟨680406850648689314913461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453604567099126209942307 680406850648689314913461)
              ·
                refine ⟨63788142248314623273137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680406850648689314913461 63788142248314623273137)
                ·
                  rfl

theorem cell20_419266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_419266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419266 prefixEnd_419266 := by exact prefixLift 419266
  have htrace : WordTrace (prefixWord ++ tailWord_419266) baseStart_419266 baseEnd_419266 := by
    simpa [prefixWord, tailWord_419266, baseEnd_419266] using wordTrace_append hprefix tailTrace_419266
  have hstable : (prefixWord ++ tailWord_419266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419266).length < 2 ^ (prefixWord ++ tailWord_419266).sum := by decide
  have hdescent : baseEnd_419266 < baseStart_419266 := by decide
  rcases family_descends (prefixWord ++ tailWord_419266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419274 : List Nat := [3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_419274 : Nat := 118140960795 + 419274 * 2 ^ 59
def prefixEnd_419274 : Nat := 4983230072969 + 3 ^ 40 * 419274 * 2
def baseEnd_419274 : Nat := 63789359387643799184237

theorem tailTrace_419274 : CollatzResearch.WordTrace tailWord_419274 prefixEnd_419274 63789359387643799184237 := by
  unfold tailWord_419274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823044770762344785860219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10194786055366252762293917 3823044770762344785860219)
  ·
    refine ⟨5734567156143517178790329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823044770762344785860219 5734567156143517178790329)
    ·
      refine ⟨4300925367107637884092747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5734567156143517178790329 4300925367107637884092747)
      ·
        refine ⟨6451388050661456826139121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300925367107637884092747 6451388050661456826139121)
        ·
          refine ⟨4838541037996092619604341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6451388050661456826139121 4838541037996092619604341)
          ·
            refine ⟨453613222312133683087907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4838541037996092619604341 453613222312133683087907)
            ·
              refine ⟨680419833468200524631861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453613222312133683087907 680419833468200524631861)
              ·
                refine ⟨63789359387643799184237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680419833468200524631861 63789359387643799184237)
                ·
                  rfl

theorem cell20_419274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_419274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419274 prefixEnd_419274 := by exact prefixLift 419274
  have htrace : WordTrace (prefixWord ++ tailWord_419274) baseStart_419274 baseEnd_419274 := by
    simpa [prefixWord, tailWord_419274, baseEnd_419274] using wordTrace_append hprefix tailTrace_419274
  have hstable : (prefixWord ++ tailWord_419274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419274).length < 2 ^ (prefixWord ++ tailWord_419274).sum := by decide
  have hdescent : baseEnd_419274 < baseStart_419274 := by decide
  rcases family_descends (prefixWord ++ tailWord_419274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419360 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_419360 : Nat := 118140960795 + 419360 * 2 ^ 59
def prefixEnd_419360 : Nat := 4983230072969 + 3 ^ 40 * 419360 * 2
def baseEnd_419360 : Nat := 191407330906297320685693

theorem tailTrace_419360 : CollatzResearch.WordTrace tailWord_419360 prefixEnd_419360 191407330906297320685693 := by
  unfold tailWord_419360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647657880368907915535767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10196877173825210554047689 7647657880368907915535767)
  ·
    refine ⟨11471486820553361873303651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7647657880368907915535767 11471486820553361873303651)
    ·
      refine ⟨17207230230830042809955477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11471486820553361873303651 17207230230830042809955477)
      ·
        refine ⟨806588917070158256716663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17207230230830042809955477 806588917070158256716663)
        ·
          refine ⟨1209883375605237385074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806588917070158256716663 1209883375605237385074995)
          ·
            refine ⟨1814825063407856077612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209883375605237385074995 1814825063407856077612493)
            ·
              refine ⟨680559398777946029104685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1814825063407856077612493 680559398777946029104685)
              ·
                refine ⟨255209774541729760914257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680559398777946029104685 255209774541729760914257)
                ·
                  refine ⟨191407330906297320685693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255209774541729760914257 191407330906297320685693)
                  ·
                    rfl

theorem cell20_419360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_419360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_419360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_419360 prefixEnd_419360 := by exact prefixLift 419360
  have htrace : WordTrace (prefixWord ++ tailWord_419360) baseStart_419360 baseEnd_419360 := by
    simpa [prefixWord, tailWord_419360, baseEnd_419360] using wordTrace_append hprefix tailTrace_419360
  have hstable : (prefixWord ++ tailWord_419360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419360).length < 2 ^ (prefixWord ++ tailWord_419360).sum := by decide
  have hdescent : baseEnd_419360 < baseStart_419360 := by decide
  rcases family_descends (prefixWord ++ tailWord_419360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
