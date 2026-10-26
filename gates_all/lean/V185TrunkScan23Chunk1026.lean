import V185TrunkScan23Chunk1025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6074376 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_6074376 : Nat := 118140960795 + 6074376 * 2 ^ 59
def prefixEnd_6074376 : Nat := 4983230072969 + 3 ^ 40 * 6074376 * 2
def baseEnd_6074376 : Nat := 1039691521378477069888153

theorem tailTrace_6074376 : CollatzResearch.WordTrace tailWord_6074376 prefixEnd_6074376 1039691521378477069888153 := by
  unfold tailWord_6074376
  simp only [CollatzResearch.WordTrace]
  refine ⟨110775346920790323836309491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147700462561053765115079321 110775346920790323836309491)
  ·
    refine ⟨166163020381185485754464237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110775346920790323836309491 166163020381185485754464237)
    ·
      refine ⟨62311132642944557157924089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166163020381185485754464237 62311132642944557157924089)
      ·
        refine ⟨46733349482208417868443067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62311132642944557157924089 46733349482208417868443067)
        ·
          refine ⟨70100024223312626802664601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46733349482208417868443067 70100024223312626802664601)
          ·
            refine ⟨52575018167484470101998451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70100024223312626802664601 52575018167484470101998451)
            ·
              refine ⟨78862527251226705152997677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52575018167484470101998451 78862527251226705152997677)
              ·
                refine ⟨29573447719210014432374129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78862527251226705152997677 29573447719210014432374129)
                ·
                  refine ⟨22180085789407510824280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29573447719210014432374129 22180085789407510824280597)
                  ·
                    refine ⟨1039691521378477069888153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22180085789407510824280597 1039691521378477069888153)
                    ·
                      rfl

theorem cell23_6074376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_6074376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074376 prefixEnd_6074376 := by exact prefixLift 6074376
  have htrace : WordTrace (prefixWord ++ tailWord_6074376) baseStart_6074376 baseEnd_6074376 := by
    simpa [prefixWord, tailWord_6074376, baseEnd_6074376] using wordTrace_append hprefix tailTrace_6074376
  have hstable : (prefixWord ++ tailWord_6074376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074376).length < 2 ^ (prefixWord ++ tailWord_6074376).sum := by decide
  have hdescent : baseEnd_6074376 < baseStart_6074376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074381 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6074381 : Nat := 118140960795 + 6074381 * 2 ^ 59
def prefixEnd_6074381 : Nat := 4983230072969 + 3 ^ 40 * 6074381 * 2
def baseEnd_6074381 : Nat := 3119077131538703690101937

theorem tailTrace_6074381 : CollatzResearch.WordTrace tailWord_6074381 prefixEnd_6074381 3119077131538703690101937 := by
  unfold tailWord_6074381
  simp only [CollatzResearch.WordTrace]
  refine ⟨221550876206562533526550997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147700584137708355684367331 221550876206562533526550997)
  ·
    refine ⟨5192598661091309379528539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 221550876206562533526550997 5192598661091309379528539)
    ·
      refine ⟨7788897991636964069292809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192598661091309379528539 7788897991636964069292809)
      ·
        refine ⟨5841673493727723051969607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788897991636964069292809 5841673493727723051969607)
        ·
          refine ⟨8762510240591584577954411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841673493727723051969607 8762510240591584577954411)
          ·
            refine ⟨13143765360887376866931617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762510240591584577954411 13143765360887376866931617)
            ·
              refine ⟨9857824020665532650198713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13143765360887376866931617 9857824020665532650198713)
              ·
                refine ⟨7393368015499149487649035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857824020665532650198713 7393368015499149487649035)
                ·
                  refine ⟨11090052023248724231473553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7393368015499149487649035 11090052023248724231473553)
                  ·
                    refine ⟨8317539017436543173605165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11090052023248724231473553 8317539017436543173605165)
                    ·
                      refine ⟨3119077131538703690101937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317539017436543173605165 3119077131538703690101937)
                      ·
                        rfl

theorem cell23_6074381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6074381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074381 prefixEnd_6074381 := by exact prefixLift 6074381
  have htrace : WordTrace (prefixWord ++ tailWord_6074381) baseStart_6074381 baseEnd_6074381 := by
    simpa [prefixWord, tailWord_6074381, baseEnd_6074381] using wordTrace_append hprefix tailTrace_6074381
  have hstable : (prefixWord ++ tailWord_6074381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074381).length < 2 ^ (prefixWord ++ tailWord_6074381).sum := by decide
  have hdescent : baseEnd_6074381 < baseStart_6074381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074423 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 5]
def baseStart_6074423 : Nat := 118140960795 + 6074423 * 2 ^ 59
def prefixEnd_6074423 : Nat := 4983230072969 + 3 ^ 40 * 6074423 * 2
def baseEnd_6074423 : Nat := 346566521969576947308527

theorem tailTrace_6074423 : CollatzResearch.WordTrace tailWord_6074423 prefixEnd_6074423 346566521969576947308527 := by
  unfold tailWord_6074423
  simp only [CollatzResearch.WordTrace]
  refine ⟨221552408072410374699579923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147701605381606916466386615 221552408072410374699579923)
  ·
    refine ⟨332328612108615562049369885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221552408072410374699579923 332328612108615562049369885)
    ·
      refine ⟨124623229540730835768513707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332328612108615562049369885 124623229540730835768513707)
      ·
        refine ⟨186934844311096253652770561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124623229540730835768513707 186934844311096253652770561)
        ·
          refine ⟨140201133233322190239577921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186934844311096253652770561 140201133233322190239577921)
          ·
            refine ⟨105150849924991642679683441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140201133233322190239577921 105150849924991642679683441)
            ·
              refine ⟨78863137443743732009762581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105150849924991642679683441 78863137443743732009762581)
              ·
                refine ⟨3696709567675487437957621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78863137443743732009762581 3696709567675487437957621)
                ·
                  refine ⟨346566521969576947308527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3696709567675487437957621 346566521969576947308527)
                  ·
                    rfl

theorem cell23_6074423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 5].length) (baseStart_6074423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074423 prefixEnd_6074423 := by exact prefixLift 6074423
  have htrace : WordTrace (prefixWord ++ tailWord_6074423) baseStart_6074423 baseEnd_6074423 := by
    simpa [prefixWord, tailWord_6074423, baseEnd_6074423] using wordTrace_append hprefix tailTrace_6074423
  have hstable : (prefixWord ++ tailWord_6074423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074423).length < 2 ^ (prefixWord ++ tailWord_6074423).sum := by decide
  have hdescent : baseEnd_6074423 < baseStart_6074423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074443 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 5, 2]
def baseStart_6074443 : Nat := 118140960795 + 6074443 * 2 ^ 59
def prefixEnd_6074443 : Nat := 4983230072969 + 3 ^ 40 * 6074443 * 2
def baseEnd_6074443 : Nat := 3119108967339282447526651

theorem tailTrace_6074443 : CollatzResearch.WordTrace tailWord_6074443 prefixEnd_6074443 3119108967339282447526651 := by
  unfold tailWord_6074443
  simp only [CollatzResearch.WordTrace]
  refine ⟨221553137532337918115307983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147702091688225278743538655 221553137532337918115307983)
  ·
    refine ⟨332329706298506877172961975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221553137532337918115307983 332329706298506877172961975)
    ·
      refine ⟨498494559447760315759442963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332329706298506877172961975 498494559447760315759442963)
      ·
        refine ⟨747741839171640473639164445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498494559447760315759442963 747741839171640473639164445)
        ·
          refine ⟨280403189689365177614686667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747741839171640473639164445 280403189689365177614686667)
          ·
            refine ⟨420604784534047766422030001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280403189689365177614686667 420604784534047766422030001)
            ·
              refine ⟨315453588400535824816522501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420604784534047766422030001 315453588400535824816522501)
              ·
                refine ⟨59147547825100467153097969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315453588400535824816522501 59147547825100467153097969)
                ·
                  refine ⟨44360660868825350364823477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59147547825100467153097969 44360660868825350364823477)
                  ·
                    refine ⟨4158811956452376596702201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44360660868825350364823477 4158811956452376596702201)
                    ·
                      refine ⟨3119108967339282447526651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158811956452376596702201 3119108967339282447526651)
                      ·
                        rfl

theorem cell23_6074443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5, 2].length) (baseStart_6074443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074443 prefixEnd_6074443 := by exact prefixLift 6074443
  have htrace : WordTrace (prefixWord ++ tailWord_6074443) baseStart_6074443 baseEnd_6074443 := by
    simpa [prefixWord, tailWord_6074443, baseEnd_6074443] using wordTrace_append hprefix tailTrace_6074443
  have hstable : (prefixWord ++ tailWord_6074443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074443).length < 2 ^ (prefixWord ++ tailWord_6074443).sum := by decide
  have hdescent : baseEnd_6074443 < baseStart_6074443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074453 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_6074453 : Nat := 118140960795 + 6074453 * 2 ^ 59
def prefixEnd_6074453 : Nat := 4983230072969 + 3 ^ 40 * 6074453 * 2
def baseEnd_6074453 : Nat := 1039704700715275802800535

theorem tailTrace_6074453 : CollatzResearch.WordTrace tailWord_6074453 prefixEnd_6074453 1039704700715275802800535 := by
  unfold tailWord_6074453
  simp only [CollatzResearch.WordTrace]
  refine ⟨221553502262301689823172013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147702334841534459882114675 221553502262301689823172013)
  ·
    refine ⟨83082563348363133683689505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221553502262301689823172013 83082563348363133683689505)
    ·
      refine ⟨62311922511272350262767129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83082563348363133683689505 62311922511272350262767129)
      ·
        refine ⟨46733941883454262697075347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62311922511272350262767129 46733941883454262697075347)
        ·
          refine ⟨70100912825181394045613021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46733941883454262697075347 70100912825181394045613021)
          ·
            refine ⟨26287842309443022767104883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70100912825181394045613021 26287842309443022767104883)
            ·
              refine ⟨39431763464164534150657325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26287842309443022767104883 39431763464164534150657325)
              ·
                refine ⟨14786911299061700306496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39431763464164534150657325 14786911299061700306496497)
                ·
                  refine ⟨11090183474296275229872373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14786911299061700306496497 11090183474296275229872373)
                  ·
                    refine ⟨1039704700715275802800535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11090183474296275229872373 1039704700715275802800535)
                    ·
                      rfl

theorem cell23_6074453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_6074453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074453 prefixEnd_6074453 := by exact prefixLift 6074453
  have htrace : WordTrace (prefixWord ++ tailWord_6074453) baseStart_6074453 baseEnd_6074453 := by
    simpa [prefixWord, tailWord_6074453, baseEnd_6074453] using wordTrace_append hprefix tailTrace_6074453
  have hstable : (prefixWord ++ tailWord_6074453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074453).length < 2 ^ (prefixWord ++ tailWord_6074453).sum := by decide
  have hdescent : baseEnd_6074453 < baseStart_6074453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074473 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_6074473 : Nat := 118140960795 + 6074473 * 2 ^ 59
def prefixEnd_6074473 : Nat := 4983230072969 + 3 ^ 40 * 6074473 * 2
def baseEnd_6074473 : Nat := 3119124371758917330151513

theorem tailTrace_6074473 : CollatzResearch.WordTrace tailWord_6074473 prefixEnd_6074473 3119124371758917330151513 := by
  unfold tailWord_6074473
  simp only [CollatzResearch.WordTrace]
  refine ⟨221554231722229233238900073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147702821148152822159266715 221554231722229233238900073)
  ·
    refine ⟨166165673791671924929175055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221554231722229233238900073 166165673791671924929175055)
    ·
      refine ⟨249248510687507887393762583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166165673791671924929175055 249248510687507887393762583)
      ·
        refine ⟨373872766031261831090643875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249248510687507887393762583 373872766031261831090643875)
        ·
          refine ⟨560809149046892746635965813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373872766031261831090643875 560809149046892746635965813)
          ·
            refine ⟨52575857723146194997121795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 560809149046892746635965813 52575857723146194997121795)
            ·
              refine ⟨78863786584719292495682693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52575857723146194997121795 78863786584719292495682693)
              ·
                refine ⟨14786959984634867342940505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78863786584719292495682693 14786959984634867342940505)
                ·
                  refine ⟨11090219988476150507205379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14786959984634867342940505 11090219988476150507205379)
                  ·
                    refine ⟨16635329982714225760808069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11090219988476150507205379 16635329982714225760808069)
                    ·
                      refine ⟨3119124371758917330151513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16635329982714225760808069 3119124371758917330151513)
                      ·
                        rfl

theorem cell23_6074473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_6074473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074473 prefixEnd_6074473 := by exact prefixLift 6074473
  have htrace : WordTrace (prefixWord ++ tailWord_6074473) baseStart_6074473 baseEnd_6074473 := by
    simpa [prefixWord, tailWord_6074473, baseEnd_6074473] using wordTrace_append hprefix tailTrace_6074473
  have hstable : (prefixWord ++ tailWord_6074473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074473).length < 2 ^ (prefixWord ++ tailWord_6074473).sum := by decide
  have hdescent : baseEnd_6074473 < baseStart_6074473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074474 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_6074474 : Nat := 118140960795 + 6074474 * 2 ^ 59
def prefixEnd_6074474 : Nat := 4983230072969 + 3 ^ 40 * 6074474 * 2
def baseEnd_6074474 : Nat := 346569431693285758471001

theorem tailTrace_6074474 : CollatzResearch.WordTrace tailWord_6074474 prefixEnd_6074474 346569431693285758471001 := by
  unfold tailWord_6074474
  simp only [CollatzResearch.WordTrace]
  refine ⟨55388567048806402602421619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147702845463483740273124317 55388567048806402602421619)
  ·
    refine ⟨83082850573209603903632429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55388567048806402602421619 83082850573209603903632429)
    ·
      refine ⟨31156068964953601463862161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83082850573209603903632429 31156068964953601463862161)
      ·
        refine ⟨23367051723715201097896621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31156068964953601463862161 23367051723715201097896621)
        ·
          refine ⟨8762644396393200411711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23367051723715201097896621 8762644396393200411711233)
          ·
            refine ⟨6571983297294900308783425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762644396393200411711233 6571983297294900308783425)
            ·
              refine ⟨4928987472971175231587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571983297294900308783425 4928987472971175231587569)
              ·
                refine ⟨3696740604728381423690677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928987472971175231587569 3696740604728381423690677)
                ·
                  refine ⟨346569431693285758471001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3696740604728381423690677 346569431693285758471001)
                  ·
                    rfl

theorem cell23_6074474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_6074474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074474 prefixEnd_6074474 := by exact prefixLift 6074474
  have htrace : WordTrace (prefixWord ++ tailWord_6074474) baseStart_6074474 baseEnd_6074474 := by
    simpa [prefixWord, tailWord_6074474, baseEnd_6074474] using wordTrace_append hprefix tailTrace_6074474
  have hstable : (prefixWord ++ tailWord_6074474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074474).length < 2 ^ (prefixWord ++ tailWord_6074474).sum := by decide
  have hdescent : baseEnd_6074474 < baseStart_6074474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074496 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 10]
def baseStart_6074496 : Nat := 118140960795 + 6074496 * 2 ^ 59
def prefixEnd_6074496 : Nat := 4983230072969 + 3 ^ 40 * 6074496 * 2
def baseEnd_6074496 : Nat := 346570686868218971129323

theorem tailTrace_6074496 : CollatzResearch.WordTrace tailWord_6074496 prefixEnd_6074496 346570686868218971129323 := by
  unfold tailWord_6074496
  simp only [CollatzResearch.WordTrace]
  refine ⟨110777535300572954083493671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147703380400763938777991561 110777535300572954083493671)
  ·
    refine ⟨166166302950859431125240507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110777535300572954083493671 166166302950859431125240507)
    ·
      refine ⟨249249454426289146687860761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166166302950859431125240507 249249454426289146687860761)
      ·
        refine ⟨186937090819716860015895571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249249454426289146687860761 186937090819716860015895571)
        ·
          refine ⟨280405636229575290023843357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186937090819716860015895571 280405636229575290023843357)
          ·
            refine ⟨105152113586090733758941259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280405636229575290023843357 105152113586090733758941259)
            ·
              refine ⟨157728170379136100638411889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105152113586090733758941259 157728170379136100638411889)
              ·
                refine ⟨118296127784352075478808917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157728170379136100638411889 118296127784352075478808917)
                ·
                  refine ⟨346570686868218971129323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118296127784352075478808917 346570686868218971129323)
                  ·
                    rfl

theorem cell23_6074496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_6074496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074496 prefixEnd_6074496 := by exact prefixLift 6074496
  have htrace : WordTrace (prefixWord ++ tailWord_6074496) baseStart_6074496 baseEnd_6074496 := by
    simpa [prefixWord, tailWord_6074496, baseEnd_6074496] using wordTrace_append hprefix tailTrace_6074496
  have hstable : (prefixWord ++ tailWord_6074496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074496).length < 2 ^ (prefixWord ++ tailWord_6074496).sum := by decide
  have hdescent : baseEnd_6074496 < baseStart_6074496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074500 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_6074500 : Nat := 118140960795 + 6074500 * 2 ^ 59
def prefixEnd_6074500 : Nat := 4983230072969 + 3 ^ 40 * 6074500 * 2
def baseEnd_6074500 : Nat := 1039712745245529574837963

theorem tailTrace_6074500 : CollatzResearch.WordTrace tailWord_6074500 prefixEnd_6074500 1039712745245529574837963 := by
  unfold tailWord_6074500
  simp only [CollatzResearch.WordTrace]
  refine ⟨110777608246565708425066477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147703477662087611233421969 110777608246565708425066477)
  ·
    refine ⟨41541603092462140659399929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110777608246565708425066477 41541603092462140659399929)
    ·
      refine ⟨31156202319346605494549947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41541603092462140659399929 31156202319346605494549947)
      ·
        refine ⟨46734303479019908241824921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156202319346605494549947 46734303479019908241824921)
        ·
          refine ⟨35050727609264931181368691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46734303479019908241824921 35050727609264931181368691)
          ·
            refine ⟨52576091413897396772053037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35050727609264931181368691 52576091413897396772053037)
            ·
              refine ⟨19716034280211523789519889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52576091413897396772053037 19716034280211523789519889)
              ·
                refine ⟨14787025710158642842139917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19716034280211523789519889 14787025710158642842139917)
                ·
                  refine ⟨5545134641309491065802469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14787025710158642842139917 5545134641309491065802469)
                  ·
                    refine ⟨1039712745245529574837963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545134641309491065802469 1039712745245529574837963)
                    ·
                      rfl

theorem cell23_6074500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_6074500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074500 prefixEnd_6074500 := by exact prefixLift 6074500
  have htrace : WordTrace (prefixWord ++ tailWord_6074500) baseStart_6074500 baseEnd_6074500 := by
    simpa [prefixWord, tailWord_6074500, baseEnd_6074500] using wordTrace_append hprefix tailTrace_6074500
  have hstable : (prefixWord ++ tailWord_6074500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074500).length < 2 ^ (prefixWord ++ tailWord_6074500).sum := by decide
  have hdescent : baseEnd_6074500 < baseStart_6074500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074517 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_6074517 : Nat := 118140960795 + 6074517 * 2 ^ 59
def prefixEnd_6074517 : Nat := 4983230072969 + 3 ^ 40 * 6074517 * 2
def baseEnd_6074517 : Nat := 1039715654969238386000437

theorem tailTrace_6074517 : CollatzResearch.WordTrace tailWord_6074517 prefixEnd_6074517 1039715654969238386000437 := by
  unfold tailWord_6074517
  simp only [CollatzResearch.WordTrace]
  refine ⟨221555836534069828753501805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147703891022713219169001203 221555836534069828753501805)
  ·
    refine ⟨83083438700276185782563177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221555836534069828753501805 83083438700276185782563177)
    ·
      refine ⟨62312579025207139336922383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83083438700276185782563177 62312579025207139336922383)
      ·
        refine ⟨93468868537810709005383575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62312579025207139336922383 93468868537810709005383575)
        ·
          refine ⟨140203302806716063508075363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93468868537810709005383575 140203302806716063508075363)
          ·
            refine ⟨210304954210074095262113045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140203302806716063508075363 210304954210074095262113045)
            ·
              refine ⟨9858044728597223215411549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210304954210074095262113045 9858044728597223215411549)
              ·
                refine ⟨3696766773223958705779331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9858044728597223215411549 3696766773223958705779331)
                ·
                  refine ⟨5545150159835938058668997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696766773223958705779331 5545150159835938058668997)
                  ·
                    refine ⟨1039715654969238386000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545150159835938058668997 1039715654969238386000437)
                    ·
                      rfl

theorem cell23_6074517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_6074517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074517 prefixEnd_6074517 := by exact prefixLift 6074517
  have htrace : WordTrace (prefixWord ++ tailWord_6074517) baseStart_6074517 baseEnd_6074517 := by
    simpa [prefixWord, tailWord_6074517, baseEnd_6074517] using wordTrace_append hprefix tailTrace_6074517
  have hstable : (prefixWord ++ tailWord_6074517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074517).length < 2 ^ (prefixWord ++ tailWord_6074517).sum := by decide
  have hdescent : baseEnd_6074517 < baseStart_6074517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074530 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_6074530 : Nat := 118140960795 + 6074530 * 2 ^ 59
def prefixEnd_6074530 : Nat := 4983230072969 + 3 ^ 40 * 6074530 * 2
def baseEnd_6074530 : Nat := 346572626684024845237639

theorem tailTrace_6074530 : CollatzResearch.WordTrace tailWord_6074530 prefixEnd_6074530 346572626684024845237639 := by
  unfold tailWord_6074530
  simp only [CollatzResearch.WordTrace]
  refine ⟨55389077670755682993431261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147704207122015154649150029 55389077670755682993431261)
  ·
    refine ⟨20770904126533381122536723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55389077670755682993431261 20770904126533381122536723)
    ·
      refine ⟨31156356189800071683805085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20770904126533381122536723 31156356189800071683805085)
      ·
        refine ⟨11683633571175026881426907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31156356189800071683805085 11683633571175026881426907)
        ·
          refine ⟨17525450356762540322140361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11683633571175026881426907 17525450356762540322140361)
          ·
            refine ⟨13144087767571905241605271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17525450356762540322140361 13144087767571905241605271)
            ·
              refine ⟨19716131651357857862407907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144087767571905241605271 19716131651357857862407907)
              ·
                refine ⟨29574197477036786793611861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19716131651357857862407907 29574197477036786793611861)
                ·
                  refine ⟨346572626684024845237639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29574197477036786793611861 346572626684024845237639)
                  ·
                    rfl

theorem cell23_6074530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_6074530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074530 prefixEnd_6074530 := by exact prefixLift 6074530
  have htrace : WordTrace (prefixWord ++ tailWord_6074530) baseStart_6074530 baseEnd_6074530 := by
    simpa [prefixWord, tailWord_6074530, baseEnd_6074530] using wordTrace_append hprefix tailTrace_6074530
  have hstable : (prefixWord ++ tailWord_6074530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074530).length < 2 ^ (prefixWord ++ tailWord_6074530).sum := by decide
  have hdescent : baseEnd_6074530 < baseStart_6074530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074560 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_6074560 : Nat := 118140960795 + 6074560 * 2 ^ 59
def prefixEnd_6074560 : Nat := 4983230072969 + 3 ^ 40 * 6074560 * 2
def baseEnd_6074560 : Nat := 1039723014858619496587871

theorem tailTrace_6074560 : CollatzResearch.WordTrace tailWord_6074560 prefixEnd_6074560 1039723014858619496587871 := by
  unfold tailWord_6074560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110778702436457023548658567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147704936581942698064878089 110778702436457023548658567)
  ·
    refine ⟨166168053654685535322987851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110778702436457023548658567 166168053654685535322987851)
    ·
      refine ⟨249252080482028302984481777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166168053654685535322987851 249252080482028302984481777)
      ·
        refine ⟨186939060361521227238361333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249252080482028302984481777 186939060361521227238361333)
        ·
          refine ⟨17525536908892615053596375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186939060361521227238361333 17525536908892615053596375)
          ·
            refine ⟨26288305363338922580394563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17525536908892615053596375 26288305363338922580394563)
            ·
              refine ⟨39432458045008383870591845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26288305363338922580394563 39432458045008383870591845)
              ·
                refine ⟨7393585883439071975735971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39432458045008383870591845 7393585883439071975735971)
                ·
                  refine ⟨11090378825158607963603957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7393585883439071975735971 11090378825158607963603957)
                  ·
                    refine ⟨1039723014858619496587871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11090378825158607963603957 1039723014858619496587871)
                    ·
                      rfl

theorem cell23_6074560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_6074560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074560 prefixEnd_6074560 := by exact prefixLift 6074560
  have htrace : WordTrace (prefixWord ++ tailWord_6074560) baseStart_6074560 baseEnd_6074560 := by
    simpa [prefixWord, tailWord_6074560, baseEnd_6074560] using wordTrace_append hprefix tailTrace_6074560
  have hstable : (prefixWord ++ tailWord_6074560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074560).length < 2 ^ (prefixWord ++ tailWord_6074560).sum := by decide
  have hdescent : baseEnd_6074560 < baseStart_6074560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074563 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4]
def baseStart_6074563 : Nat := 118140960795 + 6074563 * 2 ^ 59
def prefixEnd_6074563 : Nat := 4983230072969 + 3 ^ 40 * 6074563 * 2
def baseEnd_6074563 : Nat := 3119170585017821978026099

theorem tailTrace_6074563 : CollatzResearch.WordTrace tailWord_6074563 prefixEnd_6074563 3119170585017821978026099 := by
  unfold tailWord_6074563
  simp only [CollatzResearch.WordTrace]
  refine ⟨221557514291903178609676343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147705009527935452406450895 221557514291903178609676343)
  ·
    refine ⟨332336271437854767914514515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221557514291903178609676343 332336271437854767914514515)
    ·
      refine ⟨498504407156782151871771773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332336271437854767914514515 498504407156782151871771773)
      ·
        refine ⟨186939152683793306951914415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498504407156782151871771773 186939152683793306951914415)
        ·
          refine ⟨280408729025689960427871623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186939152683793306951914415 280408729025689960427871623)
          ·
            refine ⟨420613093538534940641807435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280408729025689960427871623 420613093538534940641807435)
            ·
              refine ⟨630919640307802410962711153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420613093538534940641807435 630919640307802410962711153)
              ·
                refine ⟨473189730230851808222033365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630919640307802410962711153 473189730230851808222033365)
                ·
                  refine ⟨11090384302285589255203907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 473189730230851808222033365 11090384302285589255203907)
                  ·
                    refine ⟨16635576453428383882805861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11090384302285589255203907 16635576453428383882805861)
                    ·
                      refine ⟨3119170585017821978026099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16635576453428383882805861 3119170585017821978026099)
                      ·
                        rfl

theorem cell23_6074563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_6074563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074563 prefixEnd_6074563 := by exact prefixLift 6074563
  have htrace : WordTrace (prefixWord ++ tailWord_6074563) baseStart_6074563 baseEnd_6074563 := by
    simpa [prefixWord, tailWord_6074563, baseEnd_6074563] using wordTrace_append hprefix tailTrace_6074563
  have hstable : (prefixWord ++ tailWord_6074563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074563).length < 2 ^ (prefixWord ++ tailWord_6074563).sum := by decide
  have hdescent : baseEnd_6074563 < baseStart_6074563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074593 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6074593 : Nat := 118140960795 + 6074593 * 2 ^ 59
def prefixEnd_6074593 : Nat := 4983230072969 + 3 ^ 40 * 6074593 * 2
def baseEnd_6074593 : Nat := 3119185989437456860650961

theorem tailTrace_6074593 : CollatzResearch.WordTrace tailWord_6074593 prefixEnd_6074593 3119185989437456860650961 := by
  unfold tailWord_6074593
  simp only [CollatzResearch.WordTrace]
  refine ⟨221558608481794493733268433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147705738987862995822178955 221558608481794493733268433)
  ·
    refine ⟨166168956361345870299951325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221558608481794493733268433 166168956361345870299951325)
    ·
      refine ⟨62313358635504701362481747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166168956361345870299951325 62313358635504701362481747)
      ·
        refine ⟨93470037953257052043722621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62313358635504701362481747 93470037953257052043722621)
        ·
          refine ⟨35051264232471394516395983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93470037953257052043722621 35051264232471394516395983)
          ·
            refine ⟨52576896348707091774593975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35051264232471394516395983 52576896348707091774593975)
            ·
              refine ⟨78865344523060637661890963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52576896348707091774593975 78865344523060637661890963)
              ·
                refine ⟨118298016784590956492836445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78865344523060637661890963 118298016784590956492836445)
                ·
                  refine ⟨44361756294221608684813667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118298016784590956492836445 44361756294221608684813667)
                  ·
                    refine ⟨66542634441332413027220501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44361756294221608684813667 66542634441332413027220501)
                    ·
                      refine ⟨3119185989437456860650961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66542634441332413027220501 3119185989437456860650961)
                      ·
                        rfl

theorem cell23_6074593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6074593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074593 prefixEnd_6074593 := by exact prefixLift 6074593
  have htrace : WordTrace (prefixWord ++ tailWord_6074593) baseStart_6074593 baseEnd_6074593 := by
    simpa [prefixWord, tailWord_6074593, baseEnd_6074593] using wordTrace_append hprefix tailTrace_6074593
  have hstable : (prefixWord ++ tailWord_6074593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074593).length < 2 ^ (prefixWord ++ tailWord_6074593).sum := by decide
  have hdescent : baseEnd_6074593 < baseStart_6074593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074600 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6074600 : Nat := 118140960795 + 6074600 * 2 ^ 59
def prefixEnd_6074600 : Nat := 4983230072969 + 3 ^ 40 * 6074600 * 2
def baseEnd_6074600 : Nat := 3119189583802038333263429

theorem tailTrace_6074600 : CollatzResearch.WordTrace tailWord_6074600 prefixEnd_6074600 3119189583802038333263429 := by
  unfold tailWord_6074600
  simp only [CollatzResearch.WordTrace]
  refine ⟨110779431896384566964386627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147705909195179422619182169 110779431896384566964386627)
  ·
    refine ⟨166169147844576850446579941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110779431896384566964386627 166169147844576850446579941)
    ·
      refine ⟨31156715220858159458733739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166169147844576850446579941 31156715220858159458733739)
      ·
        refine ⟨46735072831287239188100609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156715220858159458733739 46735072831287239188100609)
        ·
          refine ⟨35051304623465429391075457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46735072831287239188100609 35051304623465429391075457)
          ·
            refine ⟨26288478467599072043306593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35051304623465429391075457 26288478467599072043306593)
            ·
              refine ⟨19716358850699304032479945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26288478467599072043306593 19716358850699304032479945)
              ·
                refine ⟨14787269138024478024359959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19716358850699304032479945 14787269138024478024359959)
                ·
                  refine ⟨22180903707036717036539939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787269138024478024359959 22180903707036717036539939)
                  ·
                    refine ⟨33271355560555075554809909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22180903707036717036539939 33271355560555075554809909)
                    ·
                      refine ⟨3119189583802038333263429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33271355560555075554809909 3119189583802038333263429)
                      ·
                        rfl

theorem cell23_6074600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6074600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074600 prefixEnd_6074600 := by exact prefixLift 6074600
  have htrace : WordTrace (prefixWord ++ tailWord_6074600) baseStart_6074600 baseEnd_6074600 := by
    simpa [prefixWord, tailWord_6074600, baseEnd_6074600] using wordTrace_append hprefix tailTrace_6074600
  have hstable : (prefixWord ++ tailWord_6074600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074600).length < 2 ^ (prefixWord ++ tailWord_6074600).sum := by decide
  have hdescent : baseEnd_6074600 < baseStart_6074600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074603 : List Nat := [1, 1, 1, 1, 2, 5, 4, 8]
def baseStart_6074603 : Nat := 118140960795 + 6074603 * 2 ^ 59
def prefixEnd_6074603 : Nat := 4983230072969 + 3 ^ 40 * 6074603 * 2
def baseEnd_6074603 : Nat := 115525597194222289686145

theorem tailTrace_6074603 : CollatzResearch.WordTrace tailWord_6074603 prefixEnd_6074603 115525597194222289686145 := by
  unfold tailWord_6074603
  simp only [CollatzResearch.WordTrace]
  refine ⟨221558973211758265441132463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147705982141172176960754975 221558973211758265441132463)
  ·
    refine ⟨332338459817637398161698695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221558973211758265441132463 332338459817637398161698695)
    ·
      refine ⟨498507689726456097242548043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332338459817637398161698695 498507689726456097242548043)
      ·
        refine ⟨747761534589684145863822065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498507689726456097242548043 747761534589684145863822065)
        ·
          refine ⟨560821150942263109397866549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747761534589684145863822065 560821150942263109397866549)
          ·
            refine ⟨52576982900837166506049989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 560821150942263109397866549 52576982900837166506049989)
            ·
              refine ⟨9858184293906968719884373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52576982900837166506049989 9858184293906968719884373)
              ·
                refine ⟨115525597194222289686145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9858184293906968719884373 115525597194222289686145)
                ·
                  rfl

theorem cell23_6074603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 8].length) (baseStart_6074603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074603 prefixEnd_6074603 := by exact prefixLift 6074603
  have htrace : WordTrace (prefixWord ++ tailWord_6074603) baseStart_6074603 baseEnd_6074603 := by
    simpa [prefixWord, tailWord_6074603, baseEnd_6074603] using wordTrace_append hprefix tailTrace_6074603
  have hstable : (prefixWord ++ tailWord_6074603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074603).length < 2 ^ (prefixWord ++ tailWord_6074603).sum := by decide
  have hdescent : baseEnd_6074603 < baseStart_6074603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074607 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 2, 4]
def baseStart_6074607 : Nat := 118140960795 + 6074607 * 2 ^ 59
def prefixEnd_6074607 : Nat := 4983230072969 + 3 ^ 40 * 6074607 * 2
def baseEnd_6074607 : Nat := 1039731059388873268625299

theorem tailTrace_6074607 : CollatzResearch.WordTrace tailWord_6074607 prefixEnd_6074607 1039731059388873268625299 := by
  unfold tailWord_6074607
  simp only [CollatzResearch.WordTrace]
  refine ⟨221559119103743774124278075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147706079402495849416185383 221559119103743774124278075)
  ·
    refine ⟨332338678655615661186417113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221559119103743774124278075 332338678655615661186417113)
    ·
      refine ⟨249254008991711745889812835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332338678655615661186417113 249254008991711745889812835)
      ·
        refine ⟨373881013487567618834719253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249254008991711745889812835 373881013487567618834719253)
        ·
          refine ⟨17525672507229732132877465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 373881013487567618834719253 17525672507229732132877465)
          ·
            refine ⟨13144254380422299099658099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17525672507229732132877465 13144254380422299099658099)
            ·
              refine ⟨19716381570633448649487149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144254380422299099658099 19716381570633448649487149)
              ·
                refine ⟨7393643088987543243557681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19716381570633448649487149 7393643088987543243557681)
                ·
                  refine ⟨5545232316740657432668261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393643088987543243557681 5545232316740657432668261)
                  ·
                    refine ⟨1039731059388873268625299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545232316740657432668261 1039731059388873268625299)
                    ·
                      rfl

theorem cell23_6074607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_6074607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074607 prefixEnd_6074607 := by exact prefixLift 6074607
  have htrace : WordTrace (prefixWord ++ tailWord_6074607) baseStart_6074607 baseEnd_6074607 := by
    simpa [prefixWord, tailWord_6074607, baseEnd_6074607] using wordTrace_append hprefix tailTrace_6074607
  have hstable : (prefixWord ++ tailWord_6074607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074607).length < 2 ^ (prefixWord ++ tailWord_6074607).sum := by decide
  have hdescent : baseEnd_6074607 < baseStart_6074607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074610 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6074610 : Nat := 118140960795 + 6074610 * 2 ^ 59
def prefixEnd_6074610 : Nat := 4983230072969 + 3 ^ 40 * 6074610 * 2
def baseEnd_6074610 : Nat := 3119194718608583294138383

theorem tailTrace_6074610 : CollatzResearch.WordTrace tailWord_6074610 prefixEnd_6074610 3119194718608583294138383 := by
  unfold tailWord_6074610
  simp only [CollatzResearch.WordTrace]
  refine ⟨55389807130683226409159321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147706152348488603757758189 55389807130683226409159321)
  ·
    refine ⟨41542355348012419806869491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55389807130683226409159321 41542355348012419806869491)
    ·
      refine ⟨62313533022018629710304237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41542355348012419806869491 62313533022018629710304237)
      ·
        refine ⟨23367574883256986141364089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62313533022018629710304237 23367574883256986141364089)
        ·
          refine ⟨17525681162442739606023067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23367574883256986141364089 17525681162442739606023067)
          ·
            refine ⟨26288521743664109409034601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17525681162442739606023067 26288521743664109409034601)
            ·
              refine ⟨19716391307748082056775951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26288521743664109409034601 19716391307748082056775951)
              ·
                refine ⟨29574586961622123085163927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19716391307748082056775951 29574586961622123085163927)
                ·
                  refine ⟨44361880442433184627745891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29574586961622123085163927 44361880442433184627745891)
                  ·
                    refine ⟨66542820663649776941618837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44361880442433184627745891 66542820663649776941618837)
                    ·
                      refine ⟨3119194718608583294138383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66542820663649776941618837 3119194718608583294138383)
                      ·
                        rfl

theorem cell23_6074610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6074610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074610 prefixEnd_6074610 := by exact prefixLift 6074610
  have htrace : WordTrace (prefixWord ++ tailWord_6074610) baseStart_6074610 baseEnd_6074610 := by
    simpa [prefixWord, tailWord_6074610, baseEnd_6074610] using wordTrace_append hprefix tailTrace_6074610
  have hstable : (prefixWord ++ tailWord_6074610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074610).length < 2 ^ (prefixWord ++ tailWord_6074610).sum := by decide
  have hdescent : baseEnd_6074610 < baseStart_6074610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074614 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6074614 : Nat := 118140960795 + 6074614 * 2 ^ 59
def prefixEnd_6074614 : Nat := 4983230072969 + 3 ^ 40 * 6074614 * 2
def baseEnd_6074614 : Nat := 3119196772531201278488365

theorem tailTrace_6074614 : CollatzResearch.WordTrace tailWord_6074614 prefixEnd_6074614 3119196772531201278488365 := by
  unfold tailWord_6074614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847460900919900894986431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147706249609812276213188597 13847460900919900894986431)
  ·
    refine ⟨20771191351379851342479647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13847460900919900894986431 20771191351379851342479647)
    ·
      refine ⟨31156787027069777013719471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20771191351379851342479647 31156787027069777013719471)
      ·
        refine ⟨46735180540604665520579207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156787027069777013719471 46735180540604665520579207)
        ·
          refine ⟨70102770810906998280868811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46735180540604665520579207 70102770810906998280868811)
          ·
            refine ⟨105154156216360497421303217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70102770810906998280868811 105154156216360497421303217)
            ·
              refine ⟨78865617162270373065977413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105154156216360497421303217 78865617162270373065977413)
              ·
                refine ⟨14787303217925694949870765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78865617162270373065977413 14787303217925694949870765)
                ·
                  refine ⟨5545238706722135606201537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14787303217925694949870765 5545238706722135606201537)
                  ·
                    refine ⟨4158929030041601704651153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545238706722135606201537 4158929030041601704651153)
                    ·
                      refine ⟨3119196772531201278488365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158929030041601704651153 3119196772531201278488365)
                      ·
                        rfl

theorem cell23_6074614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6074614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074614 prefixEnd_6074614 := by exact prefixLift 6074614
  have htrace : WordTrace (prefixWord ++ tailWord_6074614) baseStart_6074614 baseEnd_6074614 := by
    simpa [prefixWord, tailWord_6074614, baseEnd_6074614] using wordTrace_append hprefix tailTrace_6074614
  have hstable : (prefixWord ++ tailWord_6074614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074614).length < 2 ^ (prefixWord ++ tailWord_6074614).sum := by decide
  have hdescent : baseEnd_6074614 < baseStart_6074614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074631 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6074631 : Nat := 118140960795 + 6074631 * 2 ^ 59
def prefixEnd_6074631 : Nat := 4983230072969 + 3 ^ 40 * 6074631 * 2
def baseEnd_6074631 : Nat := 3119205501702327711975787

theorem tailTrace_6074631 : CollatzResearch.WordTrace tailWord_6074631 prefixEnd_6074631 3119205501702327711975787 := by
  unfold tailWord_6074631
  simp only [CollatzResearch.WordTrace]
  refine ⟨221559994455656826223151747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147706662970437884148767831 221559994455656826223151747)
  ·
    refine ⟨332339991683485239334727621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221559994455656826223151747 332339991683485239334727621)
    ·
      refine ⟨62313748440653482375261429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332339991683485239334727621 62313748440653482375261429)
      ·
        refine ⟨5841913916311263972680759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62313748440653482375261429 5841913916311263972680759)
        ·
          refine ⟨8762870874466895959021139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841913916311263972680759 8762870874466895959021139)
          ·
            refine ⟨13144306311700343938531709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762870874466895959021139 13144306311700343938531709)
            ·
              refine ⟨4929114866887628976949391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13144306311700343938531709 4929114866887628976949391)
              ·
                refine ⟨7393672300331443465424087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929114866887628976949391 7393672300331443465424087)
                ·
                  refine ⟨11090508450497165198136131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7393672300331443465424087 11090508450497165198136131)
                  ·
                    refine ⟨16635762675745747797204197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11090508450497165198136131 16635762675745747797204197)
                    ·
                      refine ⟨3119205501702327711975787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16635762675745747797204197 3119205501702327711975787)
                      ·
                        rfl

theorem cell23_6074631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6074631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074631 prefixEnd_6074631 := by exact prefixLift 6074631
  have htrace : WordTrace (prefixWord ++ tailWord_6074631) baseStart_6074631 baseEnd_6074631 := by
    simpa [prefixWord, tailWord_6074631, baseEnd_6074631] using wordTrace_append hprefix tailTrace_6074631
  have hstable : (prefixWord ++ tailWord_6074631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074631).length < 2 ^ (prefixWord ++ tailWord_6074631).sum := by decide
  have hdescent : baseEnd_6074631 < baseStart_6074631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074643 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_6074643 : Nat := 118140960795 + 6074643 * 2 ^ 59
def prefixEnd_6074643 : Nat := 4983230072969 + 3 ^ 40 * 6074643 * 2
def baseEnd_6074643 : Nat := 3119211663470181665025731

theorem tailTrace_6074643 : CollatzResearch.WordTrace tailWord_6074643 prefixEnd_6074643 3119211663470181665025731 := by
  unfold tailWord_6074643
  simp only [CollatzResearch.WordTrace]
  refine ⟨221560432131613352272588583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147706954754408901515059055 221560432131613352272588583)
  ·
    refine ⟨332340648197420028408882875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221560432131613352272588583 332340648197420028408882875)
    ·
      refine ⟨498510972296130042613324313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332340648197420028408882875 498510972296130042613324313)
      ·
        refine ⟨373883229222097531959993235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498510972296130042613324313 373883229222097531959993235)
        ·
          refine ⟨560824843833146297939989853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373883229222097531959993235 560824843833146297939989853)
          ·
            refine ⟨210309316437429861727496195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560824843833146297939989853 210309316437429861727496195)
            ·
              refine ⟨315463974656144792591244293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210309316437429861727496195 315463974656144792591244293)
              ·
                refine ⟨59149495248027148610858305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315463974656144792591244293 59149495248027148610858305)
                ·
                  refine ⟨44362121436020361458143729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59149495248027148610858305 44362121436020361458143729)
                  ·
                    refine ⟨33271591077015271093607797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44362121436020361458143729 33271591077015271093607797)
                    ·
                      refine ⟨3119211663470181665025731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33271591077015271093607797 3119211663470181665025731)
                      ·
                        rfl

theorem cell23_6074643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_6074643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074643 prefixEnd_6074643 := by exact prefixLift 6074643
  have htrace : WordTrace (prefixWord ++ tailWord_6074643) baseStart_6074643 baseEnd_6074643 := by
    simpa [prefixWord, tailWord_6074643, baseEnd_6074643] using wordTrace_append hprefix tailTrace_6074643
  have hstable : (prefixWord ++ tailWord_6074643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074643).length < 2 ^ (prefixWord ++ tailWord_6074643).sum := by decide
  have hdescent : baseEnd_6074643 < baseStart_6074643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074654 : List Nat := [4, 3, 2, 1, 1, 3, 1, 8]
def baseStart_6074654 : Nat := 118140960795 + 6074654 * 2 ^ 59
def prefixEnd_6074654 : Nat := 4983230072969 + 3 ^ 40 * 6074654 * 2
def baseEnd_6074654 : Nat := 115526567102125226740303

theorem tailTrace_6074654 : CollatzResearch.WordTrace tailWord_6074654 prefixEnd_6074654 115526567102125226740303 := by
  unfold tailWord_6074654
  simp only [CollatzResearch.WordTrace]
  refine ⟨27695104166821687643904877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147707222223049000767492677 27695104166821687643904877)
  ·
    refine ⟨10385664062558132866464329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27695104166821687643904877 10385664062558132866464329)
    ·
      refine ⟨7789248046918599649848247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10385664062558132866464329 7789248046918599649848247)
      ·
        refine ⟨11683872070377899474772371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7789248046918599649848247 11683872070377899474772371)
        ·
          refine ⟨17525808105566849212158557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11683872070377899474772371 17525808105566849212158557)
          ·
            refine ⟨6572178039587568454559459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17525808105566849212158557 6572178039587568454559459)
            ·
              refine ⟨9858267059381352681839189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572178039587568454559459 9858267059381352681839189)
              ·
                refine ⟨115526567102125226740303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9858267059381352681839189 115526567102125226740303)
                ·
                  rfl

theorem cell23_6074654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_6074654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074654 prefixEnd_6074654 := by exact prefixLift 6074654
  have htrace : WordTrace (prefixWord ++ tailWord_6074654) baseStart_6074654 baseEnd_6074654 := by
    simpa [prefixWord, tailWord_6074654, baseEnd_6074654] using wordTrace_append hprefix tailTrace_6074654
  have hstable : (prefixWord ++ tailWord_6074654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074654).length < 2 ^ (prefixWord ++ tailWord_6074654).sum := by decide
  have hdescent : baseEnd_6074654 < baseStart_6074654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074657 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6074657 : Nat := 118140960795 + 6074657 * 2 ^ 59
def prefixEnd_6074657 : Nat := 4983230072969 + 3 ^ 40 * 6074657 * 2
def baseEnd_6074657 : Nat := 3119218852199344610250667

theorem tailTrace_6074657 : CollatzResearch.WordTrace tailWord_6074657 prefixEnd_6074657 3119218852199344610250667 := by
  unfold tailWord_6074657
  simp only [CollatzResearch.WordTrace]
  refine ⟨221560942753562632663598225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147707295169041755109065483 221560942753562632663598225)
  ·
    refine ⟨166170707065171974497698669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221560942753562632663598225 166170707065171974497698669)
    ·
      refine ⟨62314015149439490436637001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166170707065171974497698669 62314015149439490436637001)
      ·
        refine ⟨46735511362079617827477751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62314015149439490436637001 46735511362079617827477751)
        ·
          refine ⟨70103267043119426741216627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46735511362079617827477751 70103267043119426741216627)
          ·
            refine ⟨105154900564679140111824941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70103267043119426741216627 105154900564679140111824941)
            ·
              refine ⟨39433087711754677541934353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105154900564679140111824941 39433087711754677541934353)
              ·
                refine ⟨29574815783816008156450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39433087711754677541934353 29574815783816008156450765)
                ·
                  refine ⟨11090555918931003058669037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29574815783816008156450765 11090555918931003058669037)
                  ·
                    refine ⟨4158958469599126147000889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11090555918931003058669037 4158958469599126147000889)
                    ·
                      refine ⟨3119218852199344610250667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158958469599126147000889 3119218852199344610250667)
                      ·
                        rfl

theorem cell23_6074657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6074657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074657 prefixEnd_6074657 := by exact prefixLift 6074657
  have htrace : WordTrace (prefixWord ++ tailWord_6074657) baseStart_6074657 baseEnd_6074657 := by
    simpa [prefixWord, tailWord_6074657, baseEnd_6074657] using wordTrace_append hprefix tailTrace_6074657
  have hstable : (prefixWord ++ tailWord_6074657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074657).length < 2 ^ (prefixWord ++ tailWord_6074657).sum := by decide
  have hdescent : baseEnd_6074657 < baseStart_6074657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074664 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6074664 : Nat := 118140960795 + 6074664 * 2 ^ 59
def prefixEnd_6074664 : Nat := 4983230072969 + 3 ^ 40 * 6074664 * 2
def baseEnd_6074664 : Nat := 3119222446563926082863135

theorem tailTrace_6074664 : CollatzResearch.WordTrace tailWord_6074664 prefixEnd_6074664 3119222446563926082863135 := by
  unfold tailWord_6074664
  simp only [CollatzResearch.WordTrace]
  refine ⟨110780599032268636429551523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147707465376358181906068697 110780599032268636429551523)
  ·
    refine ⟨166170898548402954644327285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110780599032268636429551523 166170898548402954644327285)
    ·
      refine ⟨15578521738912776997905683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166170898548402954644327285 15578521738912776997905683)
      ·
        refine ⟨23367782608369165496858525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15578521738912776997905683 23367782608369165496858525)
        ·
          refine ⟨8762918478138437061321947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23367782608369165496858525 8762918478138437061321947)
          ·
            refine ⟨13144377717207655591982921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762918478138437061321947 13144377717207655591982921)
            ·
              refine ⟨9858283287905741693987191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13144377717207655591982921 9858283287905741693987191)
              ·
                refine ⟨14787424931858612540980787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9858283287905741693987191 14787424931858612540980787)
                ·
                  refine ⟨22181137397787918811471181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787424931858612540980787 22181137397787918811471181)
                  ·
                    refine ⟨8317926524170469554301693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22181137397787918811471181 8317926524170469554301693)
                    ·
                      refine ⟨3119222446563926082863135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317926524170469554301693 3119222446563926082863135)
                      ·
                        rfl

theorem cell23_6074664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6074664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074664 prefixEnd_6074664 := by exact prefixLift 6074664
  have htrace : WordTrace (prefixWord ++ tailWord_6074664) baseStart_6074664 baseEnd_6074664 := by
    simpa [prefixWord, tailWord_6074664, baseEnd_6074664] using wordTrace_append hprefix tailTrace_6074664
  have hstable : (prefixWord ++ tailWord_6074664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074664).length < 2 ^ (prefixWord ++ tailWord_6074664).sum := by decide
  have hdescent : baseEnd_6074664 < baseStart_6074664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074687 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 4, 2]
def baseStart_6074687 : Nat := 118140960795 + 6074687 * 2 ^ 59
def prefixEnd_6074687 : Nat := 4983230072969 + 3 ^ 40 * 6074687 * 2
def baseEnd_6074687 : Nat := 3119234256618979492875529

theorem tailTrace_6074687 : CollatzResearch.WordTrace tailWord_6074687 prefixEnd_6074687 3119234256618979492875529 := by
  unfold tailWord_6074687
  simp only [CollatzResearch.WordTrace]
  refine ⟨221562036943453947787190315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147708024628969298524793543 221562036943453947787190315)
  ·
    refine ⟨332343055415180921680785473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221562036943453947787190315 332343055415180921680785473)
    ·
      refine ⟨249257291561385691260589105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332343055415180921680785473 249257291561385691260589105)
      ·
        refine ⟨186942968671039268445441829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249257291561385691260589105 186942968671039268445441829)
        ·
          refine ⟨35051806625819862833520343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186942968671039268445441829 35051806625819862833520343)
          ·
            refine ⟨52577709938729794250280515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35051806625819862833520343 52577709938729794250280515)
            ·
              refine ⟨78866564908094691375420773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52577709938729794250280515 78866564908094691375420773)
              ·
                refine ⟨14787480920267754632891395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78866564908094691375420773 14787480920267754632891395)
                ·
                  refine ⟨22181221380401631949337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787480920267754632891395 22181221380401631949337093)
                  ·
                    refine ⟨4158979008825305990500705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22181221380401631949337093 4158979008825305990500705)
                    ·
                      refine ⟨3119234256618979492875529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158979008825305990500705 3119234256618979492875529)
                      ·
                        rfl

theorem cell23_6074687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_6074687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074687 prefixEnd_6074687 := by exact prefixLift 6074687
  have htrace : WordTrace (prefixWord ++ tailWord_6074687) baseStart_6074687 baseEnd_6074687 := by
    simpa [prefixWord, tailWord_6074687, baseEnd_6074687] using wordTrace_append hprefix tailTrace_6074687
  have hstable : (prefixWord ++ tailWord_6074687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074687).length < 2 ^ (prefixWord ++ tailWord_6074687).sum := by decide
  have hdescent : baseEnd_6074687 < baseStart_6074687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074700 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6074700 : Nat := 118140960795 + 6074700 * 2 ^ 59
def prefixEnd_6074700 : Nat := 4983230072969 + 3 ^ 40 * 6074700 * 2
def baseEnd_6074700 : Nat := 3119240931867487942012969

theorem tailTrace_6074700 : CollatzResearch.WordTrace tailWord_6074700 prefixEnd_6074700 3119240931867487942012969 := by
  unfold tailWord_6074700
  simp only [CollatzResearch.WordTrace]
  refine ⟨110781255546203425503706777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147708340728271234004942369 110781255546203425503706777)
  ·
    refine ⟨83085941659652569127780083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110781255546203425503706777 83085941659652569127780083)
    ·
      refine ⟨124628912489478853691670125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83085941659652569127780083 124628912489478853691670125)
      ·
        refine ⟨46735842183554570134376297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124628912489478853691670125 46735842183554570134376297)
        ·
          refine ⟨35051881637665927600782223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46735842183554570134376297 35051881637665927600782223)
          ·
            refine ⟨52577822456498891401173335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35051881637665927600782223 52577822456498891401173335)
            ·
              refine ⟨78866733684748337101760003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52577822456498891401173335 78866733684748337101760003)
              ·
                refine ⟨118300100527122505652640005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78866733684748337101760003 118300100527122505652640005)
                ·
                  refine ⟨22181268848835469809870001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118300100527122505652640005 22181268848835469809870001)
                  ·
                    refine ⟨16635951636626602357402501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22181268848835469809870001 16635951636626602357402501)
                    ·
                      refine ⟨3119240931867487942012969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16635951636626602357402501 3119240931867487942012969)
                      ·
                        rfl

theorem cell23_6074700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6074700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074700 prefixEnd_6074700 := by exact prefixLift 6074700
  have htrace : WordTrace (prefixWord ++ tailWord_6074700) baseStart_6074700 baseEnd_6074700 := by
    simpa [prefixWord, tailWord_6074700, baseEnd_6074700] using wordTrace_append hprefix tailTrace_6074700
  have hstable : (prefixWord ++ tailWord_6074700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074700).length < 2 ^ (prefixWord ++ tailWord_6074700).sum := by decide
  have hdescent : baseEnd_6074700 < baseStart_6074700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_6074703 : Nat := 118140960795 + 6074703 * 2 ^ 59
def prefixEnd_6074703 : Nat := 4983230072969 + 3 ^ 40 * 6074703 * 2
def baseEnd_6074703 : Nat := 3119242472309451430275455

theorem tailTrace_6074703 : CollatzResearch.WordTrace tailWord_6074703 prefixEnd_6074703 3119242472309451430275455 := by
  unfold tailWord_6074703
  simp only [CollatzResearch.WordTrace]
  refine ⟨221562620511395982519772763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147708413674263988346515175 221562620511395982519772763)
  ·
    refine ⟨332343930767093973779659145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221562620511395982519772763 332343930767093973779659145)
    ·
      refine ⟨249257948075320480334744359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332343930767093973779659145 249257948075320480334744359)
      ·
        refine ⟨373886922112980720502116539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249257948075320480334744359 373886922112980720502116539)
        ·
          refine ⟨560830383169471080753174809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373886922112980720502116539 560830383169471080753174809)
          ·
            refine ⟨420622787377103310564881107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560830383169471080753174809 420622787377103310564881107)
            ·
              refine ⟨630934181065654965847321661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420622787377103310564881107 630934181065654965847321661)
              ·
                refine ⟨236600317899620612192745623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630934181065654965847321661 236600317899620612192745623)
                ·
                  refine ⟨354900476849430918289118435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236600317899620612192745623 354900476849430918289118435)
                  ·
                    refine ⟨532350715274146377433677653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354900476849430918289118435 532350715274146377433677653)
                    ·
                      refine ⟨3119242472309451430275455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 532350715274146377433677653 3119242472309451430275455)
                      ·
                        rfl

theorem cell23_6074703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_6074703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074703 prefixEnd_6074703 := by exact prefixLift 6074703
  have htrace : WordTrace (prefixWord ++ tailWord_6074703) baseStart_6074703 baseEnd_6074703 := by
    simpa [prefixWord, tailWord_6074703, baseEnd_6074703] using wordTrace_append hprefix tailTrace_6074703
  have hstable : (prefixWord ++ tailWord_6074703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074703).length < 2 ^ (prefixWord ++ tailWord_6074703).sum := by decide
  have hdescent : baseEnd_6074703 < baseStart_6074703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074704 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2]
def baseStart_6074704 : Nat := 118140960795 + 6074704 * 2 ^ 59
def prefixEnd_6074704 : Nat := 4983230072969 + 3 ^ 40 * 6074704 * 2
def baseEnd_6074704 : Nat := 3119242985790105926362951

theorem tailTrace_6074704 : CollatzResearch.WordTrace tailWord_6074704 prefixEnd_6074704 3119242985790105926362951 := by
  unfold tailWord_6074704
  simp only [CollatzResearch.WordTrace]
  refine ⟨110781328492196179845279583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147708437989594906460372777 110781328492196179845279583)
  ·
    refine ⟨166171992738294269767919375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110781328492196179845279583 166171992738294269767919375)
    ·
      refine ⟨249257989107441404651879063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166171992738294269767919375 249257989107441404651879063)
      ·
        refine ⟨373886983661162106977818595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249257989107441404651879063 373886983661162106977818595)
        ·
          refine ⟨560830475491743160466727893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373886983661162106977818595 560830475491743160466727893)
          ·
            refine ⟨13144464269337730323438935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 560830475491743160466727893 13144464269337730323438935)
            ·
              refine ⟨19716696404006595485158403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144464269337730323438935 19716696404006595485158403)
              ·
                refine ⟨29575044606009893227737605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19716696404006595485158403 29575044606009893227737605)
                ·
                  refine ⟨5545320863626854980200801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29575044606009893227737605 5545320863626854980200801)
                  ·
                    refine ⟨4158990647720141235150601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545320863626854980200801 4158990647720141235150601)
                    ·
                      refine ⟨3119242985790105926362951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158990647720141235150601 3119242985790105926362951)
                      ·
                        rfl

theorem cell23_6074704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2].length) (baseStart_6074704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074704 prefixEnd_6074704 := by exact prefixLift 6074704
  have htrace : WordTrace (prefixWord ++ tailWord_6074704) baseStart_6074704 baseEnd_6074704 := by
    simpa [prefixWord, tailWord_6074704, baseEnd_6074704] using wordTrace_append hprefix tailTrace_6074704
  have hstable : (prefixWord ++ tailWord_6074704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074704).length < 2 ^ (prefixWord ++ tailWord_6074704).sum := by decide
  have hdescent : baseEnd_6074704 < baseStart_6074704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074772 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6074772 : Nat := 118140960795 + 6074772 * 2 ^ 59
def prefixEnd_6074772 : Nat := 4983230072969 + 3 ^ 40 * 6074772 * 2
def baseEnd_6074772 : Nat := 3119277902474611660312639

theorem tailTrace_6074772 : CollatzResearch.WordTrace tailWord_6074772 prefixEnd_6074772 3119277902474611660312639 := by
  unfold tailWord_6074772
  simp only [CollatzResearch.WordTrace]
  refine ⟨110782568574073003652017285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147710091432097338202689713 110782568574073003652017285)
  ·
    refine ⟨20771731607638688184753241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110782568574073003652017285 20771731607638688184753241)
    ·
      refine ⟨15578798705729016138564931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20771731607638688184753241 15578798705729016138564931)
      ·
        refine ⟨23368198058593524207847397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15578798705729016138564931 23368198058593524207847397)
        ·
          refine ⟨4381537135986285788971387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23368198058593524207847397 4381537135986285788971387)
          ·
            refine ⟨6572305703979428683457081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381537135986285788971387 6572305703979428683457081)
            ·
              refine ⟨4929229277984571512592811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572305703979428683457081 4929229277984571512592811)
              ·
                refine ⟨7393843916976857268889217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929229277984571512592811 7393843916976857268889217)
                ·
                  refine ⟨5545382937732642951666913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393843916976857268889217 5545382937732642951666913)
                  ·
                    refine ⟨4159037203299482213750185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545382937732642951666913 4159037203299482213750185)
                    ·
                      refine ⟨3119277902474611660312639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159037203299482213750185 3119277902474611660312639)
                      ·
                        rfl

theorem cell23_6074772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6074772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074772 prefixEnd_6074772 := by exact prefixLift 6074772
  have htrace : WordTrace (prefixWord ++ tailWord_6074772) baseStart_6074772 baseEnd_6074772 := by
    simpa [prefixWord, tailWord_6074772, baseEnd_6074772] using wordTrace_append hprefix tailTrace_6074772
  have hstable : (prefixWord ++ tailWord_6074772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074772).length < 2 ^ (prefixWord ++ tailWord_6074772).sum := by decide
  have hdescent : baseEnd_6074772 < baseStart_6074772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074777 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 6, 2]
def baseStart_6074777 : Nat := 118140960795 + 6074777 * 2 ^ 59
def prefixEnd_6074777 : Nat := 4983230072969 + 3 ^ 40 * 6074777 * 2
def baseEnd_6074777 : Nat := 3119280469877884140750115

theorem tailTrace_6074777 : CollatzResearch.WordTrace tailWord_6074777 prefixEnd_6074777 3119280469877884140750115 := by
  unfold tailWord_6074777
  simp only [CollatzResearch.WordTrace]
  refine ⟨221565319513127893157966585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147710213008751928771977723 221565319513127893157966585)
  ·
    refine ⟨166173989634845919868474939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221565319513127893157966585 166173989634845919868474939)
    ·
      refine ⟨249260984452268879802712409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166173989634845919868474939 249260984452268879802712409)
      ·
        refine ⟨186945738339201659852034307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249260984452268879802712409 186945738339201659852034307)
        ·
          refine ⟨280418607508802489778051461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186945738339201659852034307 280418607508802489778051461)
          ·
            refine ⟨52578488907900466833384649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280418607508802489778051461 52578488907900466833384649)
            ·
              refine ⟨39433866680925350125038487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52578488907900466833384649 39433866680925350125038487)
              ·
                refine ⟨59150800021388025187557731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39433866680925350125038487 59150800021388025187557731)
                ·
                  refine ⟨88726200032082037781336597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59150800021388025187557731 88726200032082037781336597)
                  ·
                    refine ⟨4159040626503845521000153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88726200032082037781336597 4159040626503845521000153)
                    ·
                      refine ⟨3119280469877884140750115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159040626503845521000153 3119280469877884140750115)
                      ·
                        rfl

theorem cell23_6074777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_6074777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074777 prefixEnd_6074777 := by exact prefixLift 6074777
  have htrace : WordTrace (prefixWord ++ tailWord_6074777) baseStart_6074777 baseEnd_6074777 := by
    simpa [prefixWord, tailWord_6074777, baseEnd_6074777] using wordTrace_append hprefix tailTrace_6074777
  have hstable : (prefixWord ++ tailWord_6074777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074777).length < 2 ^ (prefixWord ++ tailWord_6074777).sum := by decide
  have hdescent : baseEnd_6074777 < baseStart_6074777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074814 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_6074814 : Nat := 118140960795 + 6074814 * 2 ^ 59
def prefixEnd_6074814 : Nat := 4983230072969 + 3 ^ 40 * 6074814 * 2
def baseEnd_6074814 : Nat := 3119299468662100495987445

theorem tailTrace_6074814 : CollatzResearch.WordTrace tailWord_6074814 prefixEnd_6074814 3119299468662100495987445 := by
  unfold tailWord_6074814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27695833626749231059632937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147711112675995898984708997 27695833626749231059632937)
  ·
    refine ⟨20771875220061923294724703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27695833626749231059632937 20771875220061923294724703)
    ·
      refine ⟨31157812830092884942087055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20771875220061923294724703 31157812830092884942087055)
      ·
        refine ⟨46736719245139327413130583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31157812830092884942087055 46736719245139327413130583)
        ·
          refine ⟨70105078867708991119695875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46736719245139327413130583 70105078867708991119695875)
          ·
            refine ⟨105157618301563486679543813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70105078867708991119695875 105157618301563486679543813)
            ·
              refine ⟨19717053431543153752414465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105157618301563486679543813 19717053431543153752414465)
              ·
                refine ⟨14787790073657365314310849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19717053431543153752414465 14787790073657365314310849)
                ·
                  refine ⟨11090842555243023985733137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14787790073657365314310849 11090842555243023985733137)
                  ·
                    refine ⟨8318131916432267989299853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11090842555243023985733137 8318131916432267989299853)
                    ·
                      refine ⟨3119299468662100495987445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318131916432267989299853 3119299468662100495987445)
                      ·
                        rfl

theorem cell23_6074814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_6074814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074814 prefixEnd_6074814 := by exact prefixLift 6074814
  have htrace : WordTrace (prefixWord ++ tailWord_6074814) baseStart_6074814 baseEnd_6074814 := by
    simpa [prefixWord, tailWord_6074814, baseEnd_6074814] using wordTrace_append hprefix tailTrace_6074814
  have hstable : (prefixWord ++ tailWord_6074814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074814).length < 2 ^ (prefixWord ++ tailWord_6074814).sum := by decide
  have hdescent : baseEnd_6074814 < baseStart_6074814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074840 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6074840 : Nat := 118140960795 + 6074840 * 2 ^ 59
def prefixEnd_6074840 : Nat := 4983230072969 + 3 ^ 40 * 6074840 * 2
def baseEnd_6074840 : Nat := 3119312819159117394262325

theorem tailTrace_6074840 : CollatzResearch.WordTrace tailWord_6074840 prefixEnd_6074840 3119312819159117394262325 := by
  unfold tailWord_6074840
  simp only [CollatzResearch.WordTrace]
  refine ⟨110783808655949827458754987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147711744874599769945006649 110783808655949827458754987)
  ·
    refine ⟨166175712983924741188132481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110783808655949827458754987 166175712983924741188132481)
    ·
      refine ⟨124631784737943555891099361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166175712983924741188132481 124631784737943555891099361)
      ·
        refine ⟨93473838553457666918324521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124631784737943555891099361 93473838553457666918324521)
        ·
          refine ⟨70105378915093250188743391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93473838553457666918324521 70105378915093250188743391)
          ·
            refine ⟨105158068372639875283115087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70105378915093250188743391 105158068372639875283115087)
            ·
              refine ⟨157737102558959812924672631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105158068372639875283115087 157737102558959812924672631)
              ·
                refine ⟨236605653838439719387008947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157737102558959812924672631 236605653838439719387008947)
                ·
                  refine ⟨354908480757659579080513421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236605653838439719387008947 354908480757659579080513421)
                  ·
                    refine ⟨133090680284122342155192533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354908480757659579080513421 133090680284122342155192533)
                    ·
                      refine ⟨3119312819159117394262325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133090680284122342155192533 3119312819159117394262325)
                      ·
                        rfl

theorem cell23_6074840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6074840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074840 prefixEnd_6074840 := by exact prefixLift 6074840
  have htrace : WordTrace (prefixWord ++ tailWord_6074840) baseStart_6074840 baseEnd_6074840 := by
    simpa [prefixWord, tailWord_6074840, baseEnd_6074840] using wordTrace_append hprefix tailTrace_6074840
  have hstable : (prefixWord ++ tailWord_6074840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074840).length < 2 ^ (prefixWord ++ tailWord_6074840).sum := by decide
  have hdescent : baseEnd_6074840 < baseStart_6074840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074847 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 3, 5]
def baseStart_6074847 : Nat := 118140960795 + 6074847 * 2 ^ 59
def prefixEnd_6074847 : Nat := 4983230072969 + 3 ^ 40 * 6074847 * 2
def baseEnd_6074847 : Nat := 1039772137841232955624931

theorem tailTrace_6074847 : CollatzResearch.WordTrace tailWord_6074847 prefixEnd_6074847 1039772137841232955624931 := by
  unfold tailWord_6074847
  simp only [CollatzResearch.WordTrace]
  refine ⟨221567872622874295113014795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147711915081916196742009863 221567872622874295113014795)
  ·
    refine ⟨332351808934311442669522193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221567872622874295113014795 332351808934311442669522193)
    ·
      refine ⟨249263856700733582002141645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332351808934311442669522193 249263856700733582002141645)
      ·
        refine ⟨93473946262775093250803117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249263856700733582002141645 93473946262775093250803117)
        ·
          refine ⟨35052729848540659969051169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93473946262775093250803117 35052729848540659969051169)
          ·
            refine ⟨26289547386405494976788377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35052729848540659969051169 26289547386405494976788377)
            ·
              refine ⟨19717160539804121232591283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26289547386405494976788377 19717160539804121232591283)
              ·
                refine ⟨29575740809706181848886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19717160539804121232591283 29575740809706181848886925)
                ·
                  refine ⟨11090902803639818193332597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29575740809706181848886925 11090902803639818193332597)
                  ·
                    refine ⟨1039772137841232955624931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11090902803639818193332597 1039772137841232955624931)
                    ·
                      rfl

theorem cell23_6074847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_6074847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074847 prefixEnd_6074847 := by exact prefixLift 6074847
  have htrace : WordTrace (prefixWord ++ tailWord_6074847) baseStart_6074847 baseEnd_6074847 := by
    simpa [prefixWord, tailWord_6074847, baseEnd_6074847] using wordTrace_append hprefix tailTrace_6074847
  have hstable : (prefixWord ++ tailWord_6074847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074847).length < 2 ^ (prefixWord ++ tailWord_6074847).sum := by decide
  have hdescent : baseEnd_6074847 < baseStart_6074847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074894 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_6074894 : Nat := 118140960795 + 6074894 * 2 ^ 59
def prefixEnd_6074894 : Nat := 4983230072969 + 3 ^ 40 * 6074894 * 2
def baseEnd_6074894 : Nat := 1039780182371486727662359

theorem tailTrace_6074894 : CollatzResearch.WordTrace tailWord_6074894 prefixEnd_6074894 1039780182371486727662359 := by
  unfold tailWord_6074894
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696198356713002767496967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147713057902469348093317157 27696198356713002767496967)
  ·
    refine ⟨41544297535069504151245451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27696198356713002767496967 41544297535069504151245451)
    ·
      refine ⟨62316446302604256226868177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41544297535069504151245451 62316446302604256226868177)
      ·
        refine ⟨46737334726953192170151133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62316446302604256226868177 46737334726953192170151133)
        ·
          refine ⟨17526500522607447063806675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46737334726953192170151133 17526500522607447063806675)
          ·
            refine ⟨26289750783911170595710013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17526500522607447063806675 26289750783911170595710013)
            ·
              refine ⟨9858656543966688973391255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26289750783911170595710013 9858656543966688973391255)
              ·
                refine ⟨14787984815950033460086883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9858656543966688973391255 14787984815950033460086883)
                ·
                  refine ⟨22181977223925050190130325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787984815950033460086883 22181977223925050190130325)
                  ·
                    refine ⟨1039780182371486727662359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22181977223925050190130325 1039780182371486727662359)
                    ·
                      rfl

theorem cell23_6074894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_6074894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074894 prefixEnd_6074894 := by exact prefixLift 6074894
  have htrace : WordTrace (prefixWord ++ tailWord_6074894) baseStart_6074894 baseEnd_6074894 := by
    simpa [prefixWord, tailWord_6074894, baseEnd_6074894] using wordTrace_append hprefix tailTrace_6074894
  have hstable : (prefixWord ++ tailWord_6074894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074894).length < 2 ^ (prefixWord ++ tailWord_6074894).sum := by decide
  have hdescent : baseEnd_6074894 < baseStart_6074894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074897 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_6074897 : Nat := 118140960795 + 6074897 * 2 ^ 59
def prefixEnd_6074897 : Nat := 4983230072969 + 3 ^ 40 * 6074897 * 2
def baseEnd_6074897 : Nat := 3119342087556423671249563

theorem tailTrace_6074897 : CollatzResearch.WordTrace tailWord_6074897 prefixEnd_6074897 3119342087556423671249563 := by
  unfold tailWord_6074897
  simp only [CollatzResearch.WordTrace]
  refine ⟨221569696272693153652334945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147713130848462102434889963 221569696272693153652334945)
  ·
    refine ⟨166177272204519865239251209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221569696272693153652334945 166177272204519865239251209)
    ·
      refine ⟨124632954153389898929438407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166177272204519865239251209 124632954153389898929438407)
      ·
        refine ⟨186949431230084848394157611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124632954153389898929438407 186949431230084848394157611)
        ·
          refine ⟨280424146845127272591236417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186949431230084848394157611 280424146845127272591236417)
          ·
            refine ⟨210318110133845454443427313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280424146845127272591236417 210318110133845454443427313)
            ·
              refine ⟨157738582600384090832570485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210318110133845454443427313 157738582600384090832570485)
              ·
                refine ⟨14787992118786008515553483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157738582600384090832570485 14787992118786008515553483)
                ·
                  refine ⟨22181988178179012773330225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14787992118786008515553483 22181988178179012773330225)
                  ·
                    refine ⟨16636491133634259579997669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22181988178179012773330225 16636491133634259579997669)
                    ·
                      refine ⟨3119342087556423671249563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16636491133634259579997669 3119342087556423671249563)
                      ·
                        rfl

theorem cell23_6074897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_6074897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074897 prefixEnd_6074897 := by exact prefixLift 6074897
  have htrace : WordTrace (prefixWord ++ tailWord_6074897) baseStart_6074897 baseEnd_6074897 := by
    simpa [prefixWord, tailWord_6074897, baseEnd_6074897] using wordTrace_append hprefix tailTrace_6074897
  have hstable : (prefixWord ++ tailWord_6074897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074897).length < 2 ^ (prefixWord ++ tailWord_6074897).sum := by decide
  have hdescent : baseEnd_6074897 < baseStart_6074897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074901 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_6074901 : Nat := 118140960795 + 6074901 * 2 ^ 59
def prefixEnd_6074901 : Nat := 4983230072969 + 3 ^ 40 * 6074901 * 2
def baseEnd_6074901 : Nat := 3119344141479041655599545

theorem tailTrace_6074901 : CollatzResearch.WordTrace tailWord_6074901 prefixEnd_6074901 3119344141479041655599545 := by
  unfold tailWord_6074901
  simp only [CollatzResearch.WordTrace]
  refine ⟨221569842164678662335480557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147713228109785774890320371 221569842164678662335480557)
  ·
    refine ⟨83088690811754498375805209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221569842164678662335480557 83088690811754498375805209)
    ·
      refine ⟨62316518108815873781853907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83088690811754498375805209 62316518108815873781853907)
      ·
        refine ⟨93474777163223810672780861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62316518108815873781853907 93474777163223810672780861)
        ·
          refine ⟨35053041436208929002292823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93474777163223810672780861 35053041436208929002292823)
          ·
            refine ⟨52579562154313393503439235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053041436208929002292823 52579562154313393503439235)
            ·
              refine ⟨78869343231470090255158853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52579562154313393503439235 78869343231470090255158853)
              ·
                refine ⟨14788001855900641922842285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78869343231470090255158853 14788001855900641922842285)
                ·
                  refine ⟨5545500695962740721065857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14788001855900641922842285 5545500695962740721065857)
                  ·
                    refine ⟨4159125521972055540799393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545500695962740721065857 4159125521972055540799393)
                    ·
                      refine ⟨3119344141479041655599545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159125521972055540799393 3119344141479041655599545)
                      ·
                        rfl

theorem cell23_6074901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_6074901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074901 prefixEnd_6074901 := by exact prefixLift 6074901
  have htrace : WordTrace (prefixWord ++ tailWord_6074901) baseStart_6074901 baseEnd_6074901 := by
    simpa [prefixWord, tailWord_6074901, baseEnd_6074901] using wordTrace_append hprefix tailTrace_6074901
  have hstable : (prefixWord ++ tailWord_6074901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074901).length < 2 ^ (prefixWord ++ tailWord_6074901).sum := by decide
  have hdescent : baseEnd_6074901 < baseStart_6074901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074912 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6074912 : Nat := 118140960795 + 6074912 * 2 ^ 59
def prefixEnd_6074912 : Nat := 4983230072969 + 3 ^ 40 * 6074912 * 2
def baseEnd_6074912 : Nat := 3119349789766241112561995

theorem tailTrace_6074912 : CollatzResearch.WordTrace tailWord_6074912 prefixEnd_6074912 3119349789766241112561995 := by
  unfold tailWord_6074912
  simp only [CollatzResearch.WordTrace]
  refine ⟨110785121683819405607065495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147713495578425874142753993 110785121683819405607065495)
  ·
    refine ⟨166177682525729108410598243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110785121683819405607065495 166177682525729108410598243)
    ·
      refine ⟨249266523788593662615897365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166177682525729108410598243 249266523788593662615897365)
      ·
        refine ⟨11684368302590327935120189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249266523788593662615897365 11684368302590327935120189)
        ·
          refine ⟨4381638113471372975670071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11684368302590327935120189 4381638113471372975670071)
          ·
            refine ⟨6572457170207059463505107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381638113471372975670071 6572457170207059463505107)
            ·
              refine ⟨9858685755310589195257661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572457170207059463505107 9858685755310589195257661)
              ·
                refine ⟨3697007158241470948221623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9858685755310589195257661 3697007158241470948221623)
                ·
                  refine ⟨5545510737362206422332435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697007158241470948221623 5545510737362206422332435)
                  ·
                    refine ⟨8318266106043309633498653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5545510737362206422332435 8318266106043309633498653)
                    ·
                      refine ⟨3119349789766241112561995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318266106043309633498653 3119349789766241112561995)
                      ·
                        rfl

theorem cell23_6074912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6074912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074912 prefixEnd_6074912 := by exact prefixLift 6074912
  have htrace : WordTrace (prefixWord ++ tailWord_6074912) baseStart_6074912 baseEnd_6074912 := by
    simpa [prefixWord, tailWord_6074912, baseEnd_6074912] using wordTrace_append hprefix tailTrace_6074912
  have hstable : (prefixWord ++ tailWord_6074912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074912).length < 2 ^ (prefixWord ++ tailWord_6074912).sum := by decide
  have hdescent : baseEnd_6074912 < baseStart_6074912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074935 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_6074935 : Nat := 118140960795 + 6074935 * 2 ^ 59
def prefixEnd_6074935 : Nat := 4983230072969 + 3 ^ 40 * 6074935 * 2
def baseEnd_6074935 : Nat := 3119361599821294522574389

theorem tailTrace_6074935 : CollatzResearch.WordTrace tailWord_6074935 prefixEnd_6074935 3119361599821294522574389 := by
  unfold tailWord_6074935
  simp only [CollatzResearch.WordTrace]
  refine ⟨221571082246555486142218259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147714054831036990761478839 221571082246555486142218259)
  ·
    refine ⟨332356623369833229213327389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221571082246555486142218259 332356623369833229213327389)
    ·
      refine ⟨124633733763687460954997771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332356623369833229213327389 124633733763687460954997771)
      ·
        refine ⟨186950600645531191432496657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124633733763687460954997771 186950600645531191432496657)
        ·
          refine ⟨140212950484148393574372493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186950600645531191432496657 140212950484148393574372493)
          ·
            refine ⟨52579856431555647590389685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140212950484148393574372493 52579856431555647590389685)
            ·
              refine ⟨4929361540458341961599033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52579856431555647590389685 4929361540458341961599033)
              ·
                refine ⟨3697021155343756471199275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929361540458341961599033 3697021155343756471199275)
                ·
                  refine ⟨5545531733015634706798913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697021155343756471199275 5545531733015634706798913)
                  ·
                    refine ⟨4159148799761726030099185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545531733015634706798913 4159148799761726030099185)
                    ·
                      refine ⟨3119361599821294522574389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159148799761726030099185 3119361599821294522574389)
                      ·
                        rfl

theorem cell23_6074935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_6074935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074935 prefixEnd_6074935 := by exact prefixLift 6074935
  have htrace : WordTrace (prefixWord ++ tailWord_6074935) baseStart_6074935 baseEnd_6074935 := by
    simpa [prefixWord, tailWord_6074935, baseEnd_6074935] using wordTrace_append hprefix tailTrace_6074935
  have hstable : (prefixWord ++ tailWord_6074935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074935).length < 2 ^ (prefixWord ++ tailWord_6074935).sum := by decide
  have hdescent : baseEnd_6074935 < baseStart_6074935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074937 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_6074937 : Nat := 118140960795 + 6074937 * 2 ^ 59
def prefixEnd_6074937 : Nat := 4983230072969 + 3 ^ 40 * 6074937 * 2
def baseEnd_6074937 : Nat := 1039787542260867838249793

theorem tailTrace_6074937 : CollatzResearch.WordTrace tailWord_6074937 prefixEnd_6074937 1039787542260867838249793 := by
  unfold tailWord_6074937
  simp only [CollatzResearch.WordTrace]
  refine ⟨221571155192548240483791065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147714103461698826989194043 221571155192548240483791065)
  ·
    refine ⟨166178366394411180362843299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221571155192548240483791065 166178366394411180362843299)
    ·
      refine ⟨249267549591616770544264949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166178366394411180362843299 249267549591616770544264949)
      ·
        refine ⟨23368832774214072238524839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249267549591616770544264949 23368832774214072238524839)
        ·
          refine ⟨35053249161321108357787259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23368832774214072238524839 35053249161321108357787259)
          ·
            refine ⟨52579873741981662536680889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053249161321108357787259 52579873741981662536680889)
            ·
              refine ⟨39434905306486246902510667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52579873741981662536680889 39434905306486246902510667)
              ·
                refine ⟨59152357959729370353766001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39434905306486246902510667 59152357959729370353766001)
                ·
                  refine ⟨44364268469797027765324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59152357959729370353766001 44364268469797027765324501)
                  ·
                    refine ⟨1039787542260867838249793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44364268469797027765324501 1039787542260867838249793)
                    ·
                      rfl

theorem cell23_6074937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_6074937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074937 prefixEnd_6074937 := by exact prefixLift 6074937
  have htrace : WordTrace (prefixWord ++ tailWord_6074937) baseStart_6074937 baseEnd_6074937 := by
    simpa [prefixWord, tailWord_6074937, baseEnd_6074937] using wordTrace_append hprefix tailTrace_6074937
  have hstable : (prefixWord ++ tailWord_6074937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074937).length < 2 ^ (prefixWord ++ tailWord_6074937).sum := by decide
  have hdescent : baseEnd_6074937 < baseStart_6074937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074961 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_6074961 : Nat := 118140960795 + 6074961 * 2 ^ 59
def prefixEnd_6074961 : Nat := 4983230072969 + 3 ^ 40 * 6074961 * 2
def baseEnd_6074961 : Nat := 3119374950318311420849269

theorem tailTrace_6074961 : CollatzResearch.WordTrace tailWord_6074961 prefixEnd_6074961 3119374950318311420849269 := by
  unfold tailWord_6074961
  simp only [CollatzResearch.WordTrace]
  refine ⟨221572030544461292582664737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147714687029640861721776491 221572030544461292582664737)
  ·
    refine ⟨166179022908345969436998553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221572030544461292582664737 166179022908345969436998553)
    ·
      refine ⟨124634267181259477077748915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166179022908345969436998553 124634267181259477077748915)
      ·
        refine ⟨186951400771889215616623373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124634267181259477077748915 186951400771889215616623373)
        ·
          refine ⟨70106775289458455856233765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186951400771889215616623373 70106775289458455856233765)
          ·
            refine ⟨13145020366773460473043831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70106775289458455856233765 13145020366773460473043831)
            ·
              refine ⟨19717530550160190709565747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13145020366773460473043831 19717530550160190709565747)
              ·
                refine ⟨29576295825240286064348621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19717530550160190709565747 29576295825240286064348621)
                ·
                  refine ⟨11091110934465107274130733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29576295825240286064348621 11091110934465107274130733)
                  ·
                    refine ⟨4159166600424415227799025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11091110934465107274130733 4159166600424415227799025)
                    ·
                      refine ⟨3119374950318311420849269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159166600424415227799025 3119374950318311420849269)
                      ·
                        rfl

theorem cell23_6074961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_6074961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074961 prefixEnd_6074961 := by exact prefixLift 6074961
  have htrace : WordTrace (prefixWord ++ tailWord_6074961) baseStart_6074961 baseEnd_6074961 := by
    simpa [prefixWord, tailWord_6074961, baseEnd_6074961] using wordTrace_append hprefix tailTrace_6074961
  have hstable : (prefixWord ++ tailWord_6074961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074961).length < 2 ^ (prefixWord ++ tailWord_6074961).sum := by decide
  have hdescent : baseEnd_6074961 < baseStart_6074961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074991 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 4, 2, 2]
def baseStart_6074991 : Nat := 118140960795 + 6074991 * 2 ^ 59
def prefixEnd_6074991 : Nat := 4983230072969 + 3 ^ 40 * 6074991 * 2
def baseEnd_6074991 : Nat := 3119390354737946303474131

theorem tailTrace_6074991 : CollatzResearch.WordTrace tailWord_6074991 prefixEnd_6074991 3119390354737946303474131 := by
  unfold tailWord_6074991
  simp only [CollatzResearch.WordTrace]
  refine ⟨221573124734352607706256827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147715416489568405137504551 221573124734352607706256827)
  ·
    refine ⟨332359687101528911559385241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221573124734352607706256827 332359687101528911559385241)
    ·
      refine ⟨249269765326146683669538931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332359687101528911559385241 249269765326146683669538931)
      ·
        refine ⟨373904647989220025504308397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249269765326146683669538931 373904647989220025504308397)
        ·
          refine ⟨140214242995957509564115649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373904647989220025504308397 140214242995957509564115649)
          ·
            refine ⟨105160682246968132173086737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140214242995957509564115649 105160682246968132173086737)
            ·
              refine ⟨78870511685226099129815053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105160682246968132173086737 78870511685226099129815053)
              ·
                refine ⟨29576441881959787173680645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78870511685226099129815053 29576441881959787173680645)
                ·
                  refine ⟨5545582852867460095065121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29576441881959787173680645 5545582852867460095065121)
                  ·
                    refine ⟨4159187139650595071298841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545582852867460095065121 4159187139650595071298841)
                    ·
                      refine ⟨3119390354737946303474131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159187139650595071298841 3119390354737946303474131)
                      ·
                        rfl

theorem cell23_6074991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 2, 2].length) (baseStart_6074991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074991 prefixEnd_6074991 := by exact prefixLift 6074991
  have htrace : WordTrace (prefixWord ++ tailWord_6074991) baseStart_6074991 baseEnd_6074991 := by
    simpa [prefixWord, tailWord_6074991, baseEnd_6074991] using wordTrace_append hprefix tailTrace_6074991
  have hstable : (prefixWord ++ tailWord_6074991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074991).length < 2 ^ (prefixWord ++ tailWord_6074991).sum := by decide
  have hdescent : baseEnd_6074991 < baseStart_6074991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075008 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2]
def baseStart_6075008 : Nat := 118140960795 + 6075008 * 2 ^ 59
def prefixEnd_6075008 : Nat := 4983230072969 + 3 ^ 40 * 6075008 * 2
def baseEnd_6075008 : Nat := 3119399083909072736961553

theorem tailTrace_6075008 : CollatzResearch.WordTrace tailWord_6075008 prefixEnd_6075008 3119399083909072736961553 := by
  unfold tailWord_6075008
  simp only [CollatzResearch.WordTrace]
  refine ⟨110786872387645509804812839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147715829850194013073083785 110786872387645509804812839)
  ·
    refine ⟨166180308581468264707219259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110786872387645509804812839 166180308581468264707219259)
    ·
      refine ⟨249270462872202397060828889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166180308581468264707219259 249270462872202397060828889)
      ·
        refine ⟨186952847154151797795621667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249270462872202397060828889 186952847154151797795621667)
        ·
          refine ⟨280429270731227696693432501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186952847154151797795621667 280429270731227696693432501)
          ·
            refine ⟨26290244131052596565009297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280429270731227696693432501 26290244131052596565009297)
            ·
              refine ⟨19717683098289447423756973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26290244131052596565009297 19717683098289447423756973)
              ·
                refine ⟨7394131161858542783908865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19717683098289447423756973 7394131161858542783908865)
                ·
                  refine ⟨5545598371393907087931649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7394131161858542783908865 5545598371393907087931649)
                  ·
                    refine ⟨4159198778545430315948737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545598371393907087931649 4159198778545430315948737)
                    ·
                      refine ⟨3119399083909072736961553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159198778545430315948737 3119399083909072736961553)
                      ·
                        rfl

theorem cell23_6075008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_6075008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075008 prefixEnd_6075008 := by exact prefixLift 6075008
  have htrace : WordTrace (prefixWord ++ tailWord_6075008) baseStart_6075008 baseEnd_6075008 := by
    simpa [prefixWord, tailWord_6075008, baseEnd_6075008] using wordTrace_append hprefix tailTrace_6075008
  have hstable : (prefixWord ++ tailWord_6075008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075008).length < 2 ^ (prefixWord ++ tailWord_6075008).sum := by decide
  have hdescent : baseEnd_6075008 < baseStart_6075008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075027 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 7]
def baseStart_6075027 : Nat := 118140960795 + 6075027 * 2 ^ 59
def prefixEnd_6075027 : Nat := 4983230072969 + 3 ^ 40 * 6075027 * 2
def baseEnd_6075027 : Nat := 1039802946680502720874655

theorem tailTrace_6075027 : CollatzResearch.WordTrace tailWord_6075027 prefixEnd_6075027 1039802946680502720874655 := by
  unfold tailWord_6075027
  simp only [CollatzResearch.WordTrace]
  refine ⟨221574437762222185854567335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147716291841481457236378223 221574437762222185854567335)
  ·
    refine ⟨332361656643333278781851003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221574437762222185854567335 332361656643333278781851003)
    ·
      refine ⟨498542484964999918172776505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332361656643333278781851003 498542484964999918172776505)
      ·
        refine ⟨373906863723749938629582379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498542484964999918172776505 373906863723749938629582379)
        ·
          refine ⟨560860295585624907944373569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373906863723749938629582379 560860295585624907944373569)
          ·
            refine ⟨420645221689218680958280177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560860295585624907944373569 420645221689218680958280177)
            ·
              refine ⟨315483916266914010718710133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420645221689218680958280177 315483916266914010718710133)
              ·
                refine ⟨29576617150023188504879075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315483916266914010718710133 29576617150023188504879075)
                ·
                  refine ⟨44364925725034782757318613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29576617150023188504879075 44364925725034782757318613)
                  ·
                    refine ⟨1039802946680502720874655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44364925725034782757318613 1039802946680502720874655)
                    ·
                      rfl

theorem cell23_6075027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_6075027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075027 prefixEnd_6075027 := by exact prefixLift 6075027
  have htrace : WordTrace (prefixWord ++ tailWord_6075027) baseStart_6075027 baseEnd_6075027 := by
    simpa [prefixWord, tailWord_6075027, baseEnd_6075027] using wordTrace_append hprefix tailTrace_6075027
  have hstable : (prefixWord ++ tailWord_6075027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075027).length < 2 ^ (prefixWord ++ tailWord_6075027).sum := by decide
  have hdescent : baseEnd_6075027 < baseStart_6075027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075031 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 5]
def baseStart_6075031 : Nat := 118140960795 + 6075031 * 2 ^ 59
def prefixEnd_6075031 : Nat := 4983230072969 + 3 ^ 40 * 6075031 * 2
def baseEnd_6075031 : Nat := 346601210440458460774883

theorem tailTrace_6075031 : CollatzResearch.WordTrace tailWord_6075031 prefixEnd_6075031 346601210440458460774883 := by
  unfold tailWord_6075031
  simp only [CollatzResearch.WordTrace]
  refine ⟨221574583654207694537712947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147716389102805129691808631 221574583654207694537712947)
  ·
    refine ⟨332361875481311541806569421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221574583654207694537712947 332361875481311541806569421)
    ·
      refine ⟨124635703305491828177463533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332361875481311541806569421 124635703305491828177463533)
      ·
        refine ⟨46738388739559435566548825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124635703305491828177463533 46738388739559435566548825)
        ·
          refine ⟨35053791554669576674911619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46738388739559435566548825 35053791554669576674911619)
          ·
            refine ⟨52580687332004365012367429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053791554669576674911619 52580687332004365012367429)
            ·
              refine ⟨9858878874750818439818893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52580687332004365012367429 9858878874750818439818893)
              ·
                refine ⟨3697079578031556914932085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9858878874750818439818893 3697079578031556914932085)
                ·
                  refine ⟨346601210440458460774883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697079578031556914932085 346601210440458460774883)
                  ·
                    rfl

theorem cell23_6075031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 5].length) (baseStart_6075031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075031 prefixEnd_6075031 := by exact prefixLift 6075031
  have htrace : WordTrace (prefixWord ++ tailWord_6075031) baseStart_6075031 baseEnd_6075031 := by
    simpa [prefixWord, tailWord_6075031, baseEnd_6075031] using wordTrace_append hprefix tailTrace_6075031
  have hstable : (prefixWord ++ tailWord_6075031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075031).length < 2 ^ (prefixWord ++ tailWord_6075031).sum := by decide
  have hdescent : baseEnd_6075031 < baseStart_6075031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075044 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_6075044 : Nat := 118140960795 + 6075044 * 2 ^ 59
def prefixEnd_6075044 : Nat := 4983230072969 + 3 ^ 40 * 6075044 * 2
def baseEnd_6075044 : Nat := 1039805856404211532037129

theorem tailTrace_6075044 : CollatzResearch.WordTrace tailWord_6075044 prefixEnd_6075044 1039805856404211532037129 := by
  unfold tailWord_6075044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110787528901580298878968093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147716705202107065171957457 110787528901580298878968093)
  ·
    refine ⟨41545323338092612079613035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110787528901580298878968093 41545323338092612079613035)
    ·
      refine ⟨62317985007138918119419553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41545323338092612079613035 62317985007138918119419553)
      ·
        refine ⟨46738488755354188589564665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62317985007138918119419553 46738488755354188589564665)
        ·
          refine ⟨35053866566515641442173499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46738488755354188589564665 35053866566515641442173499)
          ·
            refine ⟨52580799849773462163260249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053866566515641442173499 52580799849773462163260249)
            ·
              refine ⟨39435599887330096622445187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52580799849773462163260249 39435599887330096622445187)
              ·
                refine ⟨59153399830995144933667781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39435599887330096622445187 59153399830995144933667781)
                ·
                  refine ⟨11091262468311589675062709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59153399830995144933667781 11091262468311589675062709)
                  ·
                    refine ⟨1039805856404211532037129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11091262468311589675062709 1039805856404211532037129)
                    ·
                      rfl

theorem cell23_6075044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_6075044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075044 prefixEnd_6075044 := by exact prefixLift 6075044
  have htrace : WordTrace (prefixWord ++ tailWord_6075044) baseStart_6075044 baseEnd_6075044 := by
    simpa [prefixWord, tailWord_6075044, baseEnd_6075044] using wordTrace_append hprefix tailTrace_6075044
  have hstable : (prefixWord ++ tailWord_6075044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075044).length < 2 ^ (prefixWord ++ tailWord_6075044).sum := by decide
  have hdescent : baseEnd_6075044 < baseStart_6075044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075104 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 6]
def baseStart_6075104 : Nat := 118140960795 + 6075104 * 2 ^ 59
def prefixEnd_6075104 : Nat := 4983230072969 + 3 ^ 40 * 6075104 * 2
def baseEnd_6075104 : Nat := 346605375339100484595679

theorem tailTrace_6075104 : CollatzResearch.WordTrace tailWord_6075104 prefixEnd_6075104 346605375339100484595679 := by
  unfold tailWord_6075104
  simp only [CollatzResearch.WordTrace]
  refine ⟨110788623091471614002560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147718164121962152003413577 110788623091471614002560183)
  ·
    refine ⟨166182934637207421003840275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110788623091471614002560183 166182934637207421003840275)
    ·
      refine ⟨249274401955811131505760413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166182934637207421003840275 249274401955811131505760413)
      ·
        refine ⟨93477900733429174314660155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249274401955811131505760413 93477900733429174314660155)
        ·
          refine ⟨140216851100143761471990233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93477900733429174314660155 140216851100143761471990233)
          ·
            refine ⟨105162638325107821103992675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140216851100143761471990233 105162638325107821103992675)
            ·
              refine ⟨157743957487661731655989013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105162638325107821103992675 157743957487661731655989013)
              ·
                refine ⟨7394248007234143671374485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157743957487661731655989013 7394248007234143671374485)
                ·
                  refine ⟨346605375339100484595679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7394248007234143671374485 346605375339100484595679)
                  ·
                    rfl

theorem cell23_6075104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_6075104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075104 prefixEnd_6075104 := by exact prefixLift 6075104
  have htrace : WordTrace (prefixWord ++ tailWord_6075104) baseStart_6075104 baseEnd_6075104 := by
    simpa [prefixWord, tailWord_6075104, baseEnd_6075104] using wordTrace_append hprefix tailTrace_6075104
  have hstable : (prefixWord ++ tailWord_6075104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075104).length < 2 ^ (prefixWord ++ tailWord_6075104).sum := by decide
  have hdescent : baseEnd_6075104 < baseStart_6075104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075108 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_6075108 : Nat := 118140960795 + 6075108 * 2 ^ 59
def prefixEnd_6075108 : Nat := 4983230072969 + 3 ^ 40 * 6075108 * 2
def baseEnd_6075108 : Nat := 1039816810658174115237031

theorem tailTrace_6075108 : CollatzResearch.WordTrace tailWord_6075108 prefixEnd_6075108 1039816810658174115237031 := by
  unfold tailWord_6075108
  simp only [CollatzResearch.WordTrace]
  refine ⟨110788696037464368344132989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147718261383285824458843985 110788696037464368344132989)
  ·
    refine ⟨41545761014049138129049871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110788696037464368344132989 41545761014049138129049871)
    ·
      refine ⟨62318641521073707193574807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41545761014049138129049871 62318641521073707193574807)
      ·
        refine ⟨93477962281610560790362211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62318641521073707193574807 93477962281610560790362211)
        ·
          refine ⟨140216943422415841185543317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93477962281610560790362211 140216943422415841185543317)
          ·
            refine ⟨6572669222925742555572343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140216943422415841185543317 6572669222925742555572343)
            ·
              refine ⟨9859003834388613833358515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572669222925742555572343 9859003834388613833358515)
              ·
                refine ⟨14788505751582920750037773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859003834388613833358515 14788505751582920750037773)
                ·
                  refine ⟨5545689656843595281264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14788505751582920750037773 5545689656843595281264165)
                  ·
                    refine ⟨1039816810658174115237031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545689656843595281264165 1039816810658174115237031)
                    ·
                      rfl

theorem cell23_6075108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_6075108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075108 prefixEnd_6075108 := by exact prefixLift 6075108
  have htrace : WordTrace (prefixWord ++ tailWord_6075108) baseStart_6075108 baseEnd_6075108 := by
    simpa [prefixWord, tailWord_6075108, baseEnd_6075108] using wordTrace_append hprefix tailTrace_6075108
  have hstable : (prefixWord ++ tailWord_6075108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075108).length < 2 ^ (prefixWord ++ tailWord_6075108).sum := by decide
  have hdescent : baseEnd_6075108 < baseStart_6075108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075141 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_6075141 : Nat := 118140960795 + 6075141 * 2 ^ 59
def prefixEnd_6075141 : Nat := 4983230072969 + 3 ^ 40 * 6075141 * 2
def baseEnd_6075141 : Nat := 3119467376836120716598441

theorem tailTrace_6075141 : CollatzResearch.WordTrace tailWord_6075141 prefixEnd_6075141 3119467376836120716598441 := by
  unfold tailWord_6075141
  simp only [CollatzResearch.WordTrace]
  refine ⟨221578595683809183324217277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147719063789206122216144851 221578595683809183324217277)
  ·
    refine ⟨83091973381428443746581479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221578595683809183324217277 83091973381428443746581479)
    ·
      refine ⟨124637960072142665619872219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83091973381428443746581479 124637960072142665619872219)
      ·
        refine ⟨186956940108213998429808329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124637960072142665619872219 186956940108213998429808329)
        ·
          refine ⟨140217705081160498822356247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186956940108213998429808329 140217705081160498822356247)
          ·
            refine ⟨210326557621740748233534371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140217705081160498822356247 210326557621740748233534371)
            ·
              refine ⟨315489836432611122350301557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210326557621740748233534371 315489836432611122350301557)
              ·
                refine ⟨29577172165557292720340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315489836432611122350301557 29577172165557292720340771)
                ·
                  refine ⟨44365758248335939080511157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29577172165557292720340771 44365758248335939080511157)
                  ·
                    refine ⟨4159289835781494288797921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44365758248335939080511157 4159289835781494288797921)
                    ·
                      refine ⟨3119467376836120716598441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159289835781494288797921 3119467376836120716598441)
                      ·
                        rfl

theorem cell23_6075141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_6075141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075141 prefixEnd_6075141 := by exact prefixLift 6075141
  have htrace : WordTrace (prefixWord ++ tailWord_6075141) baseStart_6075141 baseEnd_6075141 := by
    simpa [prefixWord, tailWord_6075141, baseEnd_6075141] using wordTrace_append hprefix tailTrace_6075141
  have hstable : (prefixWord ++ tailWord_6075141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075141).length < 2 ^ (prefixWord ++ tailWord_6075141).sum := by decide
  have hdescent : baseEnd_6075141 < baseStart_6075141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075159 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 1, 4]
def baseStart_6075159 : Nat := 118140960795 + 6075159 * 2 ^ 59
def prefixEnd_6075159 : Nat := 4983230072969 + 3 ^ 40 * 6075159 * 2
def baseEnd_6075159 : Nat := 1039825539829300548724453

theorem tailTrace_6075159 : CollatzResearch.WordTrace tailWord_6075159 prefixEnd_6075159 1039825539829300548724453 := by
  unfold tailWord_6075159
  simp only [CollatzResearch.WordTrace]
  refine ⟨221579252197743972398372531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147719501465162648265581687 221579252197743972398372531)
  ·
    refine ⟨332368878296615958597558797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221579252197743972398372531 332368878296615958597558797)
    ·
      refine ⟨124638329361230984474084549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332368878296615958597558797 124638329361230984474084549)
      ·
        refine ⟨23369686755230809588890853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124638329361230984474084549 23369686755230809588890853)
        ·
          refine ⟨4381816266605776797917035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23369686755230809588890853 4381816266605776797917035)
          ·
            refine ⟨6572724399908665196875553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381816266605776797917035 6572724399908665196875553)
            ·
              refine ⟨4929543299931498897656665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572724399908665196875553 4929543299931498897656665)
              ·
                refine ⟨3697157474948624173242499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929543299931498897656665 3697157474948624173242499)
                ·
                  refine ⟨5545736212422936259863749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697157474948624173242499 5545736212422936259863749)
                  ·
                    refine ⟨1039825539829300548724453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545736212422936259863749 1039825539829300548724453)
                    ·
                      rfl

theorem cell23_6075159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_6075159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075159 prefixEnd_6075159 := by exact prefixLift 6075159
  have htrace : WordTrace (prefixWord ++ tailWord_6075159) baseStart_6075159 baseEnd_6075159 := by
    simpa [prefixWord, tailWord_6075159, baseEnd_6075159] using wordTrace_append hprefix tailTrace_6075159
  have hstable : (prefixWord ++ tailWord_6075159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075159).length < 2 ^ (prefixWord ++ tailWord_6075159).sum := by decide
  have hdescent : baseEnd_6075159 < baseStart_6075159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075171 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 6, 2]
def baseStart_6075171 : Nat := 118140960795 + 6075171 * 2 ^ 59
def prefixEnd_6075171 : Nat := 4983230072969 + 3 ^ 40 * 6075171 * 2
def baseEnd_6075171 : Nat := 3119482781255755599223303

theorem tailTrace_6075171 : CollatzResearch.WordTrace tailWord_6075171 prefixEnd_6075171 3119482781255755599223303 := by
  unfold tailWord_6075171
  simp only [CollatzResearch.WordTrace]
  refine ⟨221579689873700498447809367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147719793249133665631872911 221579689873700498447809367)
  ·
    refine ⟨332369534810550747671714051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221579689873700498447809367 332369534810550747671714051)
    ·
      refine ⟨498554302215826121507571077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332369534810550747671714051 498554302215826121507571077)
      ·
        refine ⟨93478931665467397782669577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498554302215826121507571077 93478931665467397782669577)
        ·
          refine ⟨70109198749100548337002183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93478931665467397782669577 70109198749100548337002183)
          ·
            refine ⟨105163798123650822505503275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70109198749100548337002183 105163798123650822505503275)
            ·
              refine ⟨157745697185476233758254913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105163798123650822505503275 157745697185476233758254913)
              ·
                refine ⟨118309272889107175318691185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157745697185476233758254913 118309272889107175318691185)
                ·
                  refine ⟨88731954666830381489018389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118309272889107175318691185 88731954666830381489018389)
                  ·
                    refine ⟨4159310375007674132297737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88731954666830381489018389 4159310375007674132297737)
                    ·
                      refine ⟨3119482781255755599223303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159310375007674132297737 3119482781255755599223303)
                      ·
                        rfl

theorem cell23_6075171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_6075171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075171 prefixEnd_6075171 := by exact prefixLift 6075171
  have htrace : WordTrace (prefixWord ++ tailWord_6075171) baseStart_6075171 baseEnd_6075171 := by
    simpa [prefixWord, tailWord_6075171, baseEnd_6075171] using wordTrace_append hprefix tailTrace_6075171
  have hstable : (prefixWord ++ tailWord_6075171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075171).length < 2 ^ (prefixWord ++ tailWord_6075171).sum := by decide
  have hdescent : baseEnd_6075171 < baseStart_6075171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075184 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_6075184 : Nat := 118140960795 + 6075184 * 2 ^ 59
def prefixEnd_6075184 : Nat := 4983230072969 + 3 ^ 40 * 6075184 * 2
def baseEnd_6075184 : Nat := 3119489456504264048360743

theorem tailTrace_6075184 : CollatzResearch.WordTrace tailWord_6075184 prefixEnd_6075184 3119489456504264048360743 := by
  unfold tailWord_6075184
  simp only [CollatzResearch.WordTrace]
  refine ⟨110790082011326700834016303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147720109348435601112021737 110790082011326700834016303)
  ·
    refine ⟨166185123016990051251024455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110790082011326700834016303 166185123016990051251024455)
    ·
      refine ⟨249277684525485076876536683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166185123016990051251024455 249277684525485076876536683)
      ·
        refine ⟨373916526788227615314805025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249277684525485076876536683 373916526788227615314805025)
        ·
          refine ⟨280437395091170711486103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373916526788227615314805025 280437395091170711486103769)
          ·
            refine ⟨210328046318378033614577827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280437395091170711486103769 210328046318378033614577827)
            ·
              refine ⟨315492069477567050421866741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210328046318378033614577827 315492069477567050421866741)
              ·
                refine ⟨29577381513521910977050007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315492069477567050421866741 29577381513521910977050007)
                ·
                  refine ⟨44366072270282866465575011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29577381513521910977050007 44366072270282866465575011)
                  ·
                    refine ⟨66549108405424299698362517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44366072270282866465575011 66549108405424299698362517)
                    ·
                      refine ⟨3119489456504264048360743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66549108405424299698362517 3119489456504264048360743)
                      ·
                        rfl

theorem cell23_6075184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_6075184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075184 prefixEnd_6075184 := by exact prefixLift 6075184
  have htrace : WordTrace (prefixWord ++ tailWord_6075184) baseStart_6075184 baseEnd_6075184 := by
    simpa [prefixWord, tailWord_6075184, baseEnd_6075184] using wordTrace_append hprefix tailTrace_6075184
  have hstable : (prefixWord ++ tailWord_6075184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075184).length < 2 ^ (prefixWord ++ tailWord_6075184).sum := by decide
  have hdescent : baseEnd_6075184 < baseStart_6075184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075191 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_6075191 : Nat := 118140960795 + 6075191 * 2 ^ 59
def prefixEnd_6075191 : Nat := 4983230072969 + 3 ^ 40 * 6075191 * 2
def baseEnd_6075191 : Nat := 3119493050868845520973211

theorem tailTrace_6075191 : CollatzResearch.WordTrace tailWord_6075191 prefixEnd_6075191 3119493050868845520973211 := by
  unfold tailWord_6075191
  simp only [CollatzResearch.WordTrace]
  refine ⟨221580419333628041863537427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147720279555752027909024951 221580419333628041863537427)
  ·
    refine ⟨332370629000442062795306141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221580419333628041863537427 332370629000442062795306141)
    ·
      refine ⟨124638985875165773548239803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332370629000442062795306141 124638985875165773548239803)
      ·
        refine ⟨186958478812748660322359705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124638985875165773548239803 186958478812748660322359705)
        ·
          refine ⟨140218859109561495241769779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186958478812748660322359705 140218859109561495241769779)
          ·
            refine ⟨210328288664342242862654669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140218859109561495241769779 210328288664342242862654669)
            ·
              refine ⟨78873108249128341073495501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210328288664342242862654669 78873108249128341073495501)
              ·
                refine ⟨29577415593423127902560813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78873108249128341073495501 29577415593423127902560813)
                ·
                  refine ⟨11091530847533672963460305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29577415593423127902560813 11091530847533672963460305)
                  ·
                    refine ⟨8318648135650254722595229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11091530847533672963460305 8318648135650254722595229)
                    ·
                      refine ⟨3119493050868845520973211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318648135650254722595229 3119493050868845520973211)
                      ·
                        rfl

theorem cell23_6075191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_6075191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075191 prefixEnd_6075191 := by exact prefixLift 6075191
  have htrace : WordTrace (prefixWord ++ tailWord_6075191) baseStart_6075191 baseEnd_6075191 := by
    simpa [prefixWord, tailWord_6075191, baseEnd_6075191] using wordTrace_append hprefix tailTrace_6075191
  have hstable : (prefixWord ++ tailWord_6075191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075191).length < 2 ^ (prefixWord ++ tailWord_6075191).sum := by decide
  have hdescent : baseEnd_6075191 < baseStart_6075191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075208 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_6075208 : Nat := 118140960795 + 6075208 * 2 ^ 59
def prefixEnd_6075208 : Nat := 4983230072969 + 3 ^ 40 * 6075208 * 2
def baseEnd_6075208 : Nat := 3119501780039971954460633

theorem tailTrace_6075208 : CollatzResearch.WordTrace tailWord_6075208 prefixEnd_6075208 3119501780039971954460633 := by
  unfold tailWord_6075208
  simp only [CollatzResearch.WordTrace]
  refine ⟨110790519687283226883453139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147720692916377635844604185 110790519687283226883453139)
  ·
    refine ⟨166185779530924840325179709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110790519687283226883453139 166185779530924840325179709)
    ·
      refine ⟨62319667324096815121942391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166185779530924840325179709 62319667324096815121942391)
      ·
        refine ⟨93479500986145222682913587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62319667324096815121942391 93479500986145222682913587)
        ·
          refine ⟨140219251479217834024370381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93479500986145222682913587 140219251479217834024370381)
          ·
            refine ⟨52582219304706687759138893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140219251479217834024370381 52582219304706687759138893)
            ·
              refine ⟨19718332239265007909677085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52582219304706687759138893 19718332239265007909677085)
              ·
                refine ⟨7394374589724377966128907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19718332239265007909677085 7394374589724377966128907)
                ·
                  refine ⟨11091561884586566949193361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7394374589724377966128907 11091561884586566949193361)
                  ·
                    refine ⟨8318671413439925211895021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11091561884586566949193361 8318671413439925211895021)
                    ·
                      refine ⟨3119501780039971954460633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318671413439925211895021 3119501780039971954460633)
                      ·
                        rfl

theorem cell23_6075208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_6075208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075208 prefixEnd_6075208 := by exact prefixLift 6075208
  have htrace : WordTrace (prefixWord ++ tailWord_6075208) baseStart_6075208 baseEnd_6075208 := by
    simpa [prefixWord, tailWord_6075208, baseEnd_6075208] using wordTrace_append hprefix tailTrace_6075208
  have hstable : (prefixWord ++ tailWord_6075208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075208).length < 2 ^ (prefixWord ++ tailWord_6075208).sum := by decide
  have hdescent : baseEnd_6075208 < baseStart_6075208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075224 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_6075224 : Nat := 118140960795 + 6075224 * 2 ^ 59
def prefixEnd_6075224 : Nat := 4983230072969 + 3 ^ 40 * 6075224 * 2
def baseEnd_6075224 : Nat := 1039836665243481297286853

theorem tailTrace_6075224 : CollatzResearch.WordTrace tailWord_6075224 prefixEnd_6075224 1039836665243481297286853 := by
  unfold tailWord_6075224
  simp only [CollatzResearch.WordTrace]
  refine ⟨110790811471254244249744363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147721081961672325666325817 110790811471254244249744363)
  ·
    refine ⟨166186217206881366374616545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110790811471254244249744363 166186217206881366374616545)
    ·
      refine ⟨124639662905161024780962409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166186217206881366374616545 124639662905161024780962409)
      ·
        refine ⟨93479747178870768585721807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124639662905161024780962409 93479747178870768585721807)
        ·
          refine ⟨140219620768306152878582711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93479747178870768585721807 140219620768306152878582711)
          ·
            refine ⟨210329431152459229317874067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140219620768306152878582711 210329431152459229317874067)
            ·
              refine ⟨315494146728688843976811101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210329431152459229317874067 315494146728688843976811101)
              ·
                refine ⟨118310305023258316491304163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315494146728688843976811101 118310305023258316491304163)
                ·
                  refine ⟨177465457534887474736956245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118310305023258316491304163 177465457534887474736956245)
                  ·
                    refine ⟨1039836665243481297286853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177465457534887474736956245 1039836665243481297286853)
                    ·
                      rfl

theorem cell23_6075224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_6075224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075224 prefixEnd_6075224 := by exact prefixLift 6075224
  have htrace : WordTrace (prefixWord ++ tailWord_6075224) baseStart_6075224 baseEnd_6075224 := by
    simpa [prefixWord, tailWord_6075224, baseEnd_6075224] using wordTrace_append hprefix tailTrace_6075224
  have hstable : (prefixWord ++ tailWord_6075224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075224).length < 2 ^ (prefixWord ++ tailWord_6075224).sum := by decide
  have hdescent : baseEnd_6075224 < baseStart_6075224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075248 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2]
def baseStart_6075248 : Nat := 118140960795 + 6075248 * 2 ^ 59
def prefixEnd_6075248 : Nat := 4983230072969 + 3 ^ 40 * 6075248 * 2
def baseEnd_6075248 : Nat := 3119522319266151797960449

theorem tailTrace_6075248 : CollatzResearch.WordTrace tailWord_6075248 prefixEnd_6075248 3119522319266151797960449 := by
  unfold tailWord_6075248
  simp only [CollatzResearch.WordTrace]
  refine ⟨110791249147210770299181199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147721665529614360398908265 110791249147210770299181199)
  ·
    refine ⟨166186873720816155448771799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110791249147210770299181199 166186873720816155448771799)
    ·
      refine ⟨249280310581224233173157699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166186873720816155448771799 249280310581224233173157699)
      ·
        refine ⟨373920465871836349759736549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249280310581224233173157699 373920465871836349759736549)
        ·
          refine ⟨70110087350969315579950603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373920465871836349759736549 70110087350969315579950603)
          ·
            refine ⟨105165131026453973369925905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70110087350969315579950603 105165131026453973369925905)
            ·
              refine ⟨78873848269840480027444429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105165131026453973369925905 78873848269840480027444429)
              ·
                refine ⟨29577693101190180010291661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78873848269840480027444429 29577693101190180010291661)
                ·
                  refine ⟨11091634912946317503859373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29577693101190180010291661 11091634912946317503859373)
                  ·
                    refine ⟨4159363092354869063947265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11091634912946317503859373 4159363092354869063947265)
                    ·
                      refine ⟨3119522319266151797960449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159363092354869063947265 3119522319266151797960449)
                      ·
                        rfl

theorem cell23_6075248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2].length) (baseStart_6075248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075248 prefixEnd_6075248 := by exact prefixLift 6075248
  have htrace : WordTrace (prefixWord ++ tailWord_6075248) baseStart_6075248 baseEnd_6075248 := by
    simpa [prefixWord, tailWord_6075248, baseEnd_6075248] using wordTrace_append hprefix tailTrace_6075248
  have hstable : (prefixWord ++ tailWord_6075248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075248).length < 2 ^ (prefixWord ++ tailWord_6075248).sum := by decide
  have hdescent : baseEnd_6075248 < baseStart_6075248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075281 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_6075281 : Nat := 118140960795 + 6075281 * 2 ^ 59
def prefixEnd_6075281 : Nat := 4983230072969 + 3 ^ 40 * 6075281 * 2
def baseEnd_6075281 : Nat := 3119539264127750168847797

theorem tailTrace_6075281 : CollatzResearch.WordTrace tailWord_6075281 prefixEnd_6075281 3119539264127750168847797 := by
  unfold tailWord_6075281
  simp only [CollatzResearch.WordTrace]
  refine ⟨221583701903301987234313697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147722467935534658156209131 221583701903301987234313697)
  ·
    refine ⟨166187776427476490425735273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221583701903301987234313697 166187776427476490425735273)
    ·
      refine ⟨124640832320607367819301455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166187776427476490425735273 124640832320607367819301455)
      ·
        refine ⟨186961248480911051728952183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124640832320607367819301455 186961248480911051728952183)
        ·
          refine ⟨280441872721366577593428275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186961248480911051728952183 280441872721366577593428275)
          ·
            refine ⟨420662809082049866390142413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280441872721366577593428275 420662809082049866390142413)
            ·
              refine ⟨157748553405768699896303405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420662809082049866390142413 157748553405768699896303405)
              ·
                refine ⟨59155707527163262461113777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157748553405768699896303405 59155707527163262461113777)
                ·
                  refine ⟨44366780645372446845835333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59155707527163262461113777 44366780645372446845835333)
                  ·
                    refine ⟨8318771371007333783594125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44366780645372446845835333 8318771371007333783594125)
                    ·
                      refine ⟨3119539264127750168847797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318771371007333783594125 3119539264127750168847797)
                      ·
                        rfl

theorem cell23_6075281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_6075281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075281 prefixEnd_6075281 := by exact prefixLift 6075281
  have htrace : WordTrace (prefixWord ++ tailWord_6075281) baseStart_6075281 baseEnd_6075281 := by
    simpa [prefixWord, tailWord_6075281, baseEnd_6075281] using wordTrace_append hprefix tailTrace_6075281
  have hstable : (prefixWord ++ tailWord_6075281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075281).length < 2 ^ (prefixWord ++ tailWord_6075281).sum := by decide
  have hdescent : baseEnd_6075281 < baseStart_6075281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075298 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6075298 : Nat := 118140960795 + 6075298 * 2 ^ 59
def prefixEnd_6075298 : Nat := 4983230072969 + 3 ^ 40 * 6075298 * 2
def baseEnd_6075298 : Nat := 3119547993298876602335219

theorem tailTrace_6075298 : CollatzResearch.WordTrace tailWord_6075298 prefixEnd_6075298 3119547993298876602335219 := by
  unfold tailWord_6075298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55396080486060099784420637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147722881296160266091788365 55396080486060099784420637)
  ·
    refine ⟨20773530182272537419157739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55396080486060099784420637 20773530182272537419157739)
    ·
      refine ⟨31160295273408806128736609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20773530182272537419157739 31160295273408806128736609)
      ·
        refine ⟨23370221455056604596552457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31160295273408806128736609 23370221455056604596552457)
        ·
          refine ⟨17527666091292453447414343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23370221455056604596552457 17527666091292453447414343)
          ·
            refine ⟨26291499136938680171121515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17527666091292453447414343 26291499136938680171121515)
            ·
              refine ⟨39437248705408020256682273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26291499136938680171121515 39437248705408020256682273)
              ·
                refine ⟨29577936529056015192511705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39437248705408020256682273 29577936529056015192511705)
                ·
                  refine ⟨22183452396792011394383779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29577936529056015192511705 22183452396792011394383779)
                  ·
                    refine ⟨33275178595188017091575669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22183452396792011394383779 33275178595188017091575669)
                    ·
                      refine ⟨3119547993298876602335219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33275178595188017091575669 3119547993298876602335219)
                      ·
                        rfl

theorem cell23_6075298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6075298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075298 prefixEnd_6075298 := by exact prefixLift 6075298
  have htrace : WordTrace (prefixWord ++ tailWord_6075298) baseStart_6075298 baseEnd_6075298 := by
    simpa [prefixWord, tailWord_6075298, baseEnd_6075298] using wordTrace_append hprefix tailTrace_6075298
  have hstable : (prefixWord ++ tailWord_6075298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075298).length < 2 ^ (prefixWord ++ tailWord_6075298).sum := by decide
  have hdescent : baseEnd_6075298 < baseStart_6075298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075311 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_6075311 : Nat := 118140960795 + 6075311 * 2 ^ 59
def prefixEnd_6075311 : Nat := 4983230072969 + 3 ^ 40 * 6075311 * 2
def baseEnd_6075311 : Nat := 3119554668547385051472659

theorem tailTrace_6075311 : CollatzResearch.WordTrace tailWord_6075311 prefixEnd_6075311 3119554668547385051472659 := by
  unfold tailWord_6075311
  simp only [CollatzResearch.WordTrace]
  refine ⟨221584796093193302357905787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147723197395462201571937191 221584796093193302357905787)
  ·
    refine ⟨332377194139789953536858681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221584796093193302357905787 332377194139789953536858681)
    ·
      refine ⟨249282895604842465152644011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332377194139789953536858681 249282895604842465152644011)
      ·
        refine ⟨373924343407263697728966017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249282895604842465152644011 373924343407263697728966017)
        ·
          refine ⟨280443257555447773296724513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373924343407263697728966017 280443257555447773296724513)
          ·
            refine ⟨210332443166585829972543385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280443257555447773296724513 210332443166585829972543385)
            ·
              refine ⟨157749332374939372479407539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210332443166585829972543385 157749332374939372479407539)
              ·
                refine ⟨236623998562409058719111309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157749332374939372479407539 236623998562409058719111309)
                ·
                  refine ⟨88733999460903397019666741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236623998562409058719111309 88733999460903397019666741)
                  ·
                    refine ⟨8318812449459693470593757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88733999460903397019666741 8318812449459693470593757)
                    ·
                      refine ⟨3119554668547385051472659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318812449459693470593757 3119554668547385051472659)
                      ·
                        rfl

theorem cell23_6075311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_6075311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075311 prefixEnd_6075311 := by exact prefixLift 6075311
  have htrace : WordTrace (prefixWord ++ tailWord_6075311) baseStart_6075311 baseEnd_6075311 := by
    simpa [prefixWord, tailWord_6075311, baseEnd_6075311] using wordTrace_append hprefix tailTrace_6075311
  have hstable : (prefixWord ++ tailWord_6075311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075311).length < 2 ^ (prefixWord ++ tailWord_6075311).sum := by decide
  have hdescent : baseEnd_6075311 < baseStart_6075311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075316 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6075316 : Nat := 118140960795 + 6075316 * 2 ^ 59
def prefixEnd_6075316 : Nat := 4983230072969 + 3 ^ 40 * 6075316 * 2
def baseEnd_6075316 : Nat := 3119557235950657531910137

theorem tailTrace_6075316 : CollatzResearch.WordTrace tailWord_6075316 prefixEnd_6075316 3119557235950657531910137 := by
  unfold tailWord_6075316
  simp only [CollatzResearch.WordTrace]
  refine ⟨110792489229087594105918901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147723318972116792141225201 110792489229087594105918901)
  ·
    refine ⟨10386795865226961947429897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110792489229087594105918901 10386795865226961947429897)
    ·
      refine ⟨7790096898920221460572423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10386795865226961947429897 7790096898920221460572423)
      ·
        refine ⟨11685145348380332190858635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7790096898920221460572423 11685145348380332190858635)
        ·
          refine ⟨17527718022570498286287953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685145348380332190858635 17527718022570498286287953)
          ·
            refine ⟨13145788516927873714715965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17527718022570498286287953 13145788516927873714715965)
            ·
              refine ⟨4929670693847952643018487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13145788516927873714715965 4929670693847952643018487)
              ·
                refine ⟨7394506040771928964527731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929670693847952643018487 7394506040771928964527731)
                ·
                  refine ⟨11091759061157893446791597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7394506040771928964527731 11091759061157893446791597)
                  ·
                    refine ⟨4159409647934210042546849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11091759061157893446791597 4159409647934210042546849)
                    ·
                      refine ⟨3119557235950657531910137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159409647934210042546849 3119557235950657531910137)
                      ·
                        rfl

theorem cell23_6075316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6075316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075316 prefixEnd_6075316 := by exact prefixLift 6075316
  have htrace : WordTrace (prefixWord ++ tailWord_6075316) baseStart_6075316 baseEnd_6075316 := by
    simpa [prefixWord, tailWord_6075316, baseEnd_6075316] using wordTrace_append hprefix tailTrace_6075316
  have hstable : (prefixWord ++ tailWord_6075316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075316).length < 2 ^ (prefixWord ++ tailWord_6075316).sum := by decide
  have hdescent : baseEnd_6075316 < baseStart_6075316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075335 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 5]
def baseStart_6075335 : Nat := 118140960795 + 6075335 * 2 ^ 59
def prefixEnd_6075335 : Nat := 4983230072969 + 3 ^ 40 * 6075335 * 2
def baseEnd_6075335 : Nat := 346618554675899217508061

theorem tailTrace_6075335 : CollatzResearch.WordTrace tailWord_6075335 prefixEnd_6075335 346618554675899217508061 := by
  unfold tailWord_6075335
  simp only [CollatzResearch.WordTrace]
  refine ⟨221585671445106354456779459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147723780963404236304519639 221585671445106354456779459)
  ·
    refine ⟨332378507167659531685169189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221585671445106354456779459 332378507167659531685169189)
    ·
      refine ⟨62320970093936162190969223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332378507167659531685169189 62320970093936162190969223)
      ·
        refine ⟨93481455140904243286453835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62320970093936162190969223 93481455140904243286453835)
        ·
          refine ⟨140222182711356364929680753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93481455140904243286453835 140222182711356364929680753)
          ·
            refine ⟨105166637033517273697260565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140222182711356364929680753 105166637033517273697260565)
            ·
              refine ⟨4929686110946122204559089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105166637033517273697260565 4929686110946122204559089)
              ·
                refine ⟨3697264583209591653419317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929686110946122204559089 3697264583209591653419317)
                ·
                  refine ⟨346618554675899217508061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697264583209591653419317 346618554675899217508061)
                  ·
                    rfl

theorem cell23_6075335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 5].length) (baseStart_6075335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075335 prefixEnd_6075335 := by exact prefixLift 6075335
  have htrace : WordTrace (prefixWord ++ tailWord_6075335) baseStart_6075335 baseEnd_6075335 := by
    simpa [prefixWord, tailWord_6075335, baseEnd_6075335] using wordTrace_append hprefix tailTrace_6075335
  have hstable : (prefixWord ++ tailWord_6075335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075335).length < 2 ^ (prefixWord ++ tailWord_6075335).sum := by decide
  have hdescent : baseEnd_6075335 < baseStart_6075335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075365 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_6075365 : Nat := 118140960795 + 6075365 * 2 ^ 59
def prefixEnd_6075365 : Nat := 4983230072969 + 3 ^ 40 * 6075365 * 2
def baseEnd_6075365 : Nat := 1039860798834242613399137

theorem tailTrace_6075365 : CollatzResearch.WordTrace tailWord_6075365 prefixEnd_6075365 1039860798834242613399137 := by
  unfold tailWord_6075365
  simp only [CollatzResearch.WordTrace]
  refine ⟨221586765634997669580371549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147724510423331779720247699 221586765634997669580371549)
  ·
    refine ⟨83095037113124126092639331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221586765634997669580371549 83095037113124126092639331)
    ·
      refine ⟨124642555669686189138958997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83095037113124126092639331 124642555669686189138958997)
      ·
        refine ⟨5842619797016540115888703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124642555669686189138958997 5842619797016540115888703)
        ·
          refine ⟨8763929695524810173833055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5842619797016540115888703 8763929695524810173833055)
          ·
            refine ⟨13145894543287215260749583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8763929695524810173833055 13145894543287215260749583)
            ·
              refine ⟨19718841814930822891124375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13145894543287215260749583 19718841814930822891124375)
              ·
                refine ⟨29578262722396234336686563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19718841814930822891124375 29578262722396234336686563)
                ·
                  refine ⟨44367394083594351505029845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29578262722396234336686563 44367394083594351505029845)
                  ·
                    refine ⟨1039860798834242613399137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44367394083594351505029845 1039860798834242613399137)
                    ·
                      rfl

theorem cell23_6075365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_6075365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075365 prefixEnd_6075365 := by exact prefixLift 6075365
  have htrace : WordTrace (prefixWord ++ tailWord_6075365) baseStart_6075365 baseEnd_6075365 := by
    simpa [prefixWord, tailWord_6075365, baseEnd_6075365] using wordTrace_append hprefix tailTrace_6075365
  have hstable : (prefixWord ++ tailWord_6075365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075365).length < 2 ^ (prefixWord ++ tailWord_6075365).sum := by decide
  have hdescent : baseEnd_6075365 < baseStart_6075365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075411 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_6075411 : Nat := 118140960795 + 6075411 * 2 ^ 59
def prefixEnd_6075411 : Nat := 4983230072969 + 3 ^ 40 * 6075411 * 2
def baseEnd_6075411 : Nat := 3119606016612834660222199

theorem tailTrace_6075411 : CollatzResearch.WordTrace tailWord_6075411 prefixEnd_6075411 3119606016612834660222199 := by
  unfold tailWord_6075411
  simp only [CollatzResearch.WordTrace]
  refine ⟨221588443392831019436546087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147725628928554012957697391 221588443392831019436546087)
  ·
    refine ⟨332382665089246529154819131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221588443392831019436546087 332382665089246529154819131)
    ·
      refine ⟨498573997633869793732228697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332382665089246529154819131 498573997633869793732228697)
      ·
        refine ⟨373930498225402345299171523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498573997633869793732228697 373930498225402345299171523)
        ·
          refine ⟨560895747338103517948757285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373930498225402345299171523 560895747338103517948757285)
          ·
            refine ⟨105167952625894409615391991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 560895747338103517948757285 105167952625894409615391991)
            ·
              refine ⟨157751928938841614423087987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105167952625894409615391991 157751928938841614423087987)
              ·
                refine ⟨236627893408262421634631981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157751928938841614423087987 236627893408262421634631981)
                ·
                  refine ⟨88735460028098408112986993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236627893408262421634631981 88735460028098408112986993)
                  ·
                    refine ⟨66551595021073806084740245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88735460028098408112986993 66551595021073806084740245)
                    ·
                      refine ⟨3119606016612834660222199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66551595021073806084740245 3119606016612834660222199)
                      ·
                        rfl

theorem cell23_6075411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_6075411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075411 prefixEnd_6075411 := by exact prefixLift 6075411
  have htrace : WordTrace (prefixWord ++ tailWord_6075411) baseStart_6075411 baseEnd_6075411 := by
    simpa [prefixWord, tailWord_6075411, baseEnd_6075411] using wordTrace_append hprefix tailTrace_6075411
  have hstable : (prefixWord ++ tailWord_6075411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075411).length < 2 ^ (prefixWord ++ tailWord_6075411).sum := by decide
  have hdescent : baseEnd_6075411 < baseStart_6075411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075418 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_6075418 : Nat := 118140960795 + 6075418 * 2 ^ 59
def prefixEnd_6075418 : Nat := 4983230072969 + 3 ^ 40 * 6075418 * 2
def baseEnd_6075418 : Nat := 3119609610977416132834667

theorem tailTrace_6075418 : CollatzResearch.WordTrace tailWord_6075418 prefixEnd_6075418 3119609610977416132834667 := by
  unfold tailWord_6075418
  simp only [CollatzResearch.WordTrace]
  refine ⟨55397174675951414908012727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147725799135870439754700605 55397174675951414908012727)
  ·
    refine ⟨83095762013927122362019091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55397174675951414908012727 83095762013927122362019091)
    ·
      refine ⟨124643643020890683543028637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83095762013927122362019091 124643643020890683543028637)
      ·
        refine ⟨46741366132834006328635739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124643643020890683543028637 46741366132834006328635739)
        ·
          refine ⟨70112049199251009492953609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46741366132834006328635739 70112049199251009492953609)
          ·
            refine ⟨52584036899438257119715207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70112049199251009492953609 52584036899438257119715207)
            ·
              refine ⟨78876055349157385679572811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52584036899438257119715207 78876055349157385679572811)
              ·
                refine ⟨118314083023736078519359217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78876055349157385679572811 118314083023736078519359217)
                ·
                  refine ⟨88735562267802058889519413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118314083023736078519359217 88735562267802058889519413)
                  ·
                    refine ⟨8318958962606443020892445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88735562267802058889519413 8318958962606443020892445)
                    ·
                      refine ⟨3119609610977416132834667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8318958962606443020892445 3119609610977416132834667)
                      ·
                        rfl

theorem cell23_6075418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_6075418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075418 prefixEnd_6075418 := by exact prefixLift 6075418
  have htrace : WordTrace (prefixWord ++ tailWord_6075418) baseStart_6075418 baseEnd_6075418 := by
    simpa [prefixWord, tailWord_6075418, baseEnd_6075418] using wordTrace_append hprefix tailTrace_6075418
  have hstable : (prefixWord ++ tailWord_6075418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075418).length < 2 ^ (prefixWord ++ tailWord_6075418).sum := by decide
  have hdescent : baseEnd_6075418 < baseStart_6075418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075446 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6075446 : Nat := 118140960795 + 6075446 * 2 ^ 59
def prefixEnd_6075446 : Nat := 4983230072969 + 3 ^ 40 * 6075446 * 2
def baseEnd_6075446 : Nat := 1039874662811914007761513

theorem tailTrace_6075446 : CollatzResearch.WordTrace tailWord_6075446 prefixEnd_6075446 1039874662811914007761513 := by
  unfold tailWord_6075446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13849357496731513775879387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147726479965136146942713461 13849357496731513775879387)
  ·
    refine ⟨20774036245097270663819081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13849357496731513775879387 20774036245097270663819081)
    ·
      refine ⟨15580527183822952997864311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20774036245097270663819081 15580527183822952997864311)
      ·
        refine ⟨23370790775734429496796467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15580527183822952997864311 23370790775734429496796467)
        ·
          refine ⟨35056186163601644245194701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23370790775734429496796467 35056186163601644245194701)
          ·
            refine ⟨13146069811350616591948013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35056186163601644245194701 13146069811350616591948013)
            ·
              refine ⟨4929776179256481221980505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13146069811350616591948013 4929776179256481221980505)
              ·
                refine ⟨3697332134442360916485379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929776179256481221980505 3697332134442360916485379)
                ·
                  refine ⟨5545998201663541374728069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697332134442360916485379 5545998201663541374728069)
                  ·
                    refine ⟨1039874662811914007761513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5545998201663541374728069 1039874662811914007761513)
                    ·
                      rfl

theorem cell23_6075446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6075446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075446 prefixEnd_6075446 := by exact prefixLift 6075446
  have htrace : WordTrace (prefixWord ++ tailWord_6075446) baseStart_6075446 baseEnd_6075446 := by
    simpa [prefixWord, tailWord_6075446, baseEnd_6075446] using wordTrace_append hprefix tailTrace_6075446
  have hstable : (prefixWord ++ tailWord_6075446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075446).length < 2 ^ (prefixWord ++ tailWord_6075446).sum := by decide
  have hdescent : baseEnd_6075446 < baseStart_6075446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075451 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 10]
def baseStart_6075451 : Nat := 118140960795 + 6075451 * 2 ^ 59
def prefixEnd_6075451 : Nat := 4983230072969 + 3 ^ 40 * 6075451 * 2
def baseEnd_6075451 : Nat := 1039875518613004834574005

theorem tailTrace_6075451 : CollatzResearch.WordTrace tailWord_6075451 prefixEnd_6075451 1039875518613004834574005 := by
  unfold tailWord_6075451
  simp only [CollatzResearch.WordTrace]
  refine ⟨221589902312686106268002207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147726601541790737512001471 221589902312686106268002207)
  ·
    refine ⟨332384853469029159402003311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221589902312686106268002207 332384853469029159402003311)
    ·
      refine ⟨498577280203543739103004967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332384853469029159402003311 498577280203543739103004967)
      ·
        refine ⟨747865920305315608654507451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498577280203543739103004967 747865920305315608654507451)
        ·
          refine ⟨1121798880457973412981761177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747865920305315608654507451 1121798880457973412981761177)
          ·
            refine ⟨841349160343480059736320883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121798880457973412981761177 841349160343480059736320883)
            ·
              refine ⟨1262023740515220089604481325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841349160343480059736320883 1262023740515220089604481325)
              ·
                refine ⟨473258902693207533601680497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262023740515220089604481325 473258902693207533601680497)
                ·
                  refine ⟨354944177019905650201260373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473258902693207533601680497 354944177019905650201260373)
                  ·
                    refine ⟨1039875518613004834574005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 354944177019905650201260373 1039875518613004834574005)
                    ·
                      rfl

theorem cell23_6075451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_6075451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075451 prefixEnd_6075451 := by exact prefixLift 6075451
  have htrace : WordTrace (prefixWord ++ tailWord_6075451) baseStart_6075451 baseEnd_6075451 := by
    simpa [prefixWord, tailWord_6075451, baseEnd_6075451] using wordTrace_append hprefix tailTrace_6075451
  have hstable : (prefixWord ++ tailWord_6075451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075451).length < 2 ^ (prefixWord ++ tailWord_6075451).sum := by decide
  have hdescent : baseEnd_6075451 < baseStart_6075451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075452 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_6075452 : Nat := 118140960795 + 6075452 * 2 ^ 59
def prefixEnd_6075452 : Nat := 4983230072969 + 3 ^ 40 * 6075452 * 2
def baseEnd_6075452 : Nat := 3119627069319668999809511

theorem tailTrace_6075452 : CollatzResearch.WordTrace tailWord_6075452 prefixEnd_6075452 3119627069319668999809511 := by
  unfold tailWord_6075452
  simp only [CollatzResearch.WordTrace]
  refine ⟨110794969392841241719394305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147726625857121655625859073 110794969392841241719394305)
  ·
    refine ⟨83096227044630931289545729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110794969392841241719394305 83096227044630931289545729)
    ·
      refine ⟨62322170283473198467159297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83096227044630931289545729 62322170283473198467159297)
      ·
        refine ⟨46741627712604898850369473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62322170283473198467159297 46741627712604898850369473)
        ·
          refine ⟨35056220784453674137777105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46741627712604898850369473 35056220784453674137777105)
          ·
            refine ⟨26292165588340255603332829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35056220784453674137777105 26292165588340255603332829)
            ·
              refine ⟨9859562095627595851249811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26292165588340255603332829 9859562095627595851249811)
              ·
                refine ⟨14789343143441393776874717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859562095627595851249811 14789343143441393776874717)
                ·
                  refine ⟨5546003678790522666328019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14789343143441393776874717 5546003678790522666328019)
                  ·
                    refine ⟨8319005518185783999492029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546003678790522666328019 8319005518185783999492029)
                    ·
                      refine ⟨3119627069319668999809511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319005518185783999492029 3119627069319668999809511)
                      ·
                        rfl

theorem cell23_6075452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_6075452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075452 prefixEnd_6075452 := by exact prefixLift 6075452
  have htrace : WordTrace (prefixWord ++ tailWord_6075452) baseStart_6075452 baseEnd_6075452 := by
    simpa [prefixWord, tailWord_6075452, baseEnd_6075452] using wordTrace_append hprefix tailTrace_6075452
  have hstable : (prefixWord ++ tailWord_6075452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075452).length < 2 ^ (prefixWord ++ tailWord_6075452).sum := by decide
  have hdescent : baseEnd_6075452 < baseStart_6075452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075468 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_6075468 : Nat := 118140960795 + 6075468 * 2 ^ 59
def prefixEnd_6075468 : Nat := 4983230072969 + 3 ^ 40 * 6075468 * 2
def baseEnd_6075468 : Nat := 1039878428336713645736479

theorem tailTrace_6075468 : CollatzResearch.WordTrace tailWord_6075468 prefixEnd_6075468 1039878428336713645736479 := by
  unfold tailWord_6075468
  simp only [CollatzResearch.WordTrace]
  refine ⟨110795261176812259085685529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147727014902416345447580705 110795261176812259085685529)
  ·
    refine ⟨83096445882609194314264147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110795261176812259085685529 83096445882609194314264147)
    ·
      refine ⟨124644668823913791471396221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83096445882609194314264147 124644668823913791471396221)
      ·
        refine ⟨46741750808967671801773583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124644668823913791471396221 46741750808967671801773583)
        ·
          refine ⟨70112626213451507702660375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46741750808967671801773583 70112626213451507702660375)
          ·
            refine ⟨105168939320177261553990563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70112626213451507702660375 105168939320177261553990563)
            ·
              refine ⟨157753408980265892330985845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105168939320177261553990563 157753408980265892330985845)
              ·
                refine ⟨14789382091899927406029923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157753408980265892330985845 14789382091899927406029923)
                ·
                  refine ⟨22184073137849891109044885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14789382091899927406029923 22184073137849891109044885)
                  ·
                    refine ⟨1039878428336713645736479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22184073137849891109044885 1039878428336713645736479)
                    ·
                      rfl

theorem cell23_6075468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_6075468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075468 prefixEnd_6075468 := by exact prefixLift 6075468
  have htrace : WordTrace (prefixWord ++ tailWord_6075468) baseStart_6075468 baseEnd_6075468 := by
    simpa [prefixWord, tailWord_6075468, baseEnd_6075468] using wordTrace_append hprefix tailTrace_6075468
  have hstable : (prefixWord ++ tailWord_6075468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075468).length < 2 ^ (prefixWord ++ tailWord_6075468).sum := by decide
  have hdescent : baseEnd_6075468 < baseStart_6075468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075495 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_6075495 : Nat := 118140960795 + 6075495 * 2 ^ 59
def prefixEnd_6075495 : Nat := 4983230072969 + 3 ^ 40 * 6075495 * 2
def baseEnd_6075495 : Nat := 3119649148987812331571813

theorem tailTrace_6075495 : CollatzResearch.WordTrace tailWord_6075495 prefixEnd_6075495 3119649148987812331571813 := by
  unfold tailWord_6075495
  simp only [CollatzResearch.WordTrace]
  refine ⟨221591507124526701782603939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147727671416351134521735959 221591507124526701782603939)
  ·
    refine ⟨332387260686790052673905909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221591507124526701782603939 332387260686790052673905909)
    ·
      refine ⟨31161305689386567438178679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332387260686790052673905909 31161305689386567438178679)
      ·
        refine ⟨46741958534079851157268019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31161305689386567438178679 46741958534079851157268019)
        ·
          refine ⟨70112937801119776735902029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46741958534079851157268019 70112937801119776735902029)
          ·
            refine ⟨26292351675419916275963261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70112937801119776735902029 26292351675419916275963261)
            ·
              refine ⟨9859631878282468603486223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26292351675419916275963261 9859631878282468603486223)
              ·
                refine ⟨14789447817423702905229335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859631878282468603486223 14789447817423702905229335)
                ·
                  refine ⟨22184171726135554357844003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14789447817423702905229335 22184171726135554357844003)
                  ·
                    refine ⟨33276257589203331536766005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22184171726135554357844003 33276257589203331536766005)
                    ·
                      refine ⟨3119649148987812331571813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33276257589203331536766005 3119649148987812331571813)
                      ·
                        rfl

theorem cell23_6075495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_6075495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075495 prefixEnd_6075495 := by exact prefixLift 6075495
  have htrace : WordTrace (prefixWord ++ tailWord_6075495) baseStart_6075495 baseEnd_6075495 := by
    simpa [prefixWord, tailWord_6075495, baseEnd_6075495] using wordTrace_append hprefix tailTrace_6075495
  have hstable : (prefixWord ++ tailWord_6075495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075495).length < 2 ^ (prefixWord ++ tailWord_6075495).sum := by decide
  have hdescent : baseEnd_6075495 < baseStart_6075495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075498 : List Nat := [3, 1, 3, 2, 2, 12]
def baseStart_6075498 : Nat := 118140960795 + 6075498 * 2 ^ 59
def prefixEnd_6075498 : Nat := 4983230072969 + 3 ^ 40 * 6075498 * 2
def baseEnd_6075498 : Nat := 12838068680780970451993

theorem tailTrace_6075498 : CollatzResearch.WordTrace tailWord_6075498 prefixEnd_6075498 12838068680780970451993 := by
  unfold tailWord_6075498
  simp only [CollatzResearch.WordTrace]
  refine ⟨55397904135878958323740787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147727744362343888863308765 55397904135878958323740787)
  ·
    refine ⟨83096856203818437485611181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55397904135878958323740787 83096856203818437485611181)
    ·
      refine ⟨31161321076431914057104193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83096856203818437485611181 31161321076431914057104193)
      ·
        refine ⟨23370990807323935542828145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31161321076431914057104193 23370990807323935542828145)
        ·
          refine ⟨17528243105492951657121109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23370990807323935542828145 17528243105492951657121109)
          ·
            refine ⟨12838068680780970451993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17528243105492951657121109 12838068680780970451993)
            ·
              rfl

theorem cell23_6075498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 12].length) (baseStart_6075498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075498 prefixEnd_6075498 := by exact prefixLift 6075498
  have htrace : WordTrace (prefixWord ++ tailWord_6075498) baseStart_6075498 baseEnd_6075498 := by
    simpa [prefixWord, tailWord_6075498, baseEnd_6075498] using wordTrace_append hprefix tailTrace_6075498
  have hstable : (prefixWord ++ tailWord_6075498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075498).length < 2 ^ (prefixWord ++ tailWord_6075498).sum := by decide
  have hdescent : baseEnd_6075498 < baseStart_6075498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075502 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6075502 : Nat := 118140960795 + 6075502 * 2 ^ 59
def prefixEnd_6075502 : Nat := 4983230072969 + 3 ^ 40 * 6075502 * 2
def baseEnd_6075502 : Nat := 1039884247784131268061427

theorem tailTrace_6075502 : CollatzResearch.WordTrace tailWord_6075502 prefixEnd_6075502 1039884247784131268061427 := by
  unfold tailWord_6075502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27698970304437667747263595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147727841623667561318739173 27698970304437667747263595)
  ·
    refine ⟨41548455456656501620895393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27698970304437667747263595 41548455456656501620895393)
    ·
      refine ⟨31161341592492376215671545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41548455456656501620895393 31161341592492376215671545)
      ·
        refine ⟨23371006194369282161753659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31161341592492376215671545 23371006194369282161753659)
        ·
          refine ⟨35056509291553923242630489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23371006194369282161753659 35056509291553923242630489)
          ·
            refine ⟨26292381968665442431972867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35056509291553923242630489 26292381968665442431972867)
            ·
              refine ⟨39438572952998163647959301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26292381968665442431972867 39438572952998163647959301)
              ·
                refine ⟨7394732428687155683992369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39438572952998163647959301 7394732428687155683992369)
                ·
                  refine ⟨5546049321515366762994277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7394732428687155683992369 5546049321515366762994277)
                  ·
                    refine ⟨1039884247784131268061427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546049321515366762994277 1039884247784131268061427)
                    ·
                      rfl

theorem cell23_6075502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6075502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075502 prefixEnd_6075502 := by exact prefixLift 6075502
  have htrace : WordTrace (prefixWord ++ tailWord_6075502) baseStart_6075502 baseEnd_6075502 := by
    simpa [prefixWord, tailWord_6075502, baseEnd_6075502] using wordTrace_append hprefix tailTrace_6075502
  have hstable : (prefixWord ++ tailWord_6075502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075502).length < 2 ^ (prefixWord ++ tailWord_6075502).sum := by decide
  have hdescent : baseEnd_6075502 < baseStart_6075502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075546 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6075546 : Nat := 118140960795 + 6075546 * 2 ^ 59
def prefixEnd_6075546 : Nat := 4983230072969 + 3 ^ 40 * 6075546 * 2
def baseEnd_6075546 : Nat := 3119675336501191632034079

theorem tailTrace_6075546 : CollatzResearch.WordTrace tailWord_6075546 prefixEnd_6075546 3119675336501191632034079 := by
  unfold tailWord_6075546
  simp only [CollatzResearch.WordTrace]
  refine ⟨55398341811835484373177623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147728911498227958328473661 55398341811835484373177623)
  ·
    refine ⟨83097512717753226559766435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55398341811835484373177623 83097512717753226559766435)
    ·
      refine ⟨124646269076629839839649653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83097512717753226559766435 124646269076629839839649653)
      ·
        refine ⟨11685587725934047484967155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124646269076629839839649653 11685587725934047484967155)
        ·
          refine ⟨17528381588901071227450733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685587725934047484967155 17528381588901071227450733)
          ·
            refine ⟨6573143095837901710294025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17528381588901071227450733 6573143095837901710294025)
            ·
              refine ⟨4929857321878426282720519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573143095837901710294025 4929857321878426282720519)
              ·
                refine ⟨7394785982817639424080779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929857321878426282720519 7394785982817639424080779)
                ·
                  refine ⟨11092178974226459136121169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7394785982817639424080779 11092178974226459136121169)
                  ·
                    refine ⟨8319134230669844352090877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11092178974226459136121169 8319134230669844352090877)
                    ·
                      refine ⟨3119675336501191632034079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319134230669844352090877 3119675336501191632034079)
                      ·
                        rfl

theorem cell23_6075546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6075546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075546 prefixEnd_6075546 := by exact prefixLift 6075546
  have htrace : WordTrace (prefixWord ++ tailWord_6075546) baseStart_6075546 baseEnd_6075546 := by
    simpa [prefixWord, tailWord_6075546, baseEnd_6075546] using wordTrace_append hprefix tailTrace_6075546
  have hstable : (prefixWord ++ tailWord_6075546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075546).length < 2 ^ (prefixWord ++ tailWord_6075546).sum := by decide
  have hdescent : baseEnd_6075546 < baseStart_6075546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075559 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6075559 : Nat := 118140960795 + 6075559 * 2 ^ 59
def prefixEnd_6075559 : Nat := 4983230072969 + 3 ^ 40 * 6075559 * 2
def baseEnd_6075559 : Nat := 3119682011749700081171519

theorem tailTrace_6075559 : CollatzResearch.WordTrace tailWord_6075559 prefixEnd_6075559 3119682011749700081171519 := by
  unfold tailWord_6075559
  simp only [CollatzResearch.WordTrace]
  refine ⟨221593841396294840712933731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147729227597529893808622487 221593841396294840712933731)
  ·
    refine ⟨332390762094442261069400597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221593841396294840712933731 332390762094442261069400597)
    ·
      refine ⟨15580816973176980987628153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332390762094442261069400597 15580816973176980987628153)
      ·
        refine ⟨11685612729882735740721115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15580816973176980987628153 11685612729882735740721115)
        ·
          refine ⟨17528419094824103611081673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685612729882735740721115 17528419094824103611081673)
          ·
            refine ⟨13146314321118077708311255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17528419094824103611081673 13146314321118077708311255)
            ·
              refine ⟨19719471481677116562466883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13146314321118077708311255 19719471481677116562466883)
              ·
                refine ⟨29579207222515674843700325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19719471481677116562466883 29579207222515674843700325)
                ·
                  refine ⟨5546101354221689033193811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29579207222515674843700325 5546101354221689033193811)
                  ·
                    refine ⟨8319152031332533549790717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546101354221689033193811 8319152031332533549790717)
                    ·
                      refine ⟨3119682011749700081171519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319152031332533549790717 3119682011749700081171519)
                      ·
                        rfl

theorem cell23_6075559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6075559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075559 prefixEnd_6075559 := by exact prefixLift 6075559
  have htrace : WordTrace (prefixWord ++ tailWord_6075559) baseStart_6075559 baseEnd_6075559 := by
    simpa [prefixWord, tailWord_6075559, baseEnd_6075559] using wordTrace_append hprefix tailTrace_6075559
  have hstable : (prefixWord ++ tailWord_6075559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075559).length < 2 ^ (prefixWord ++ tailWord_6075559).sum := by decide
  have hdescent : baseEnd_6075559 < baseStart_6075559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075568 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_6075568 : Nat := 118140960795 + 6075568 * 2 ^ 59
def prefixEnd_6075568 : Nat := 4983230072969 + 3 ^ 40 * 6075568 * 2
def baseEnd_6075568 : Nat := 3119686633075590545958977

theorem tailTrace_6075568 : CollatzResearch.WordTrace tailWord_6075568 prefixEnd_6075568 3119686633075590545958977 := by
  unfold tailWord_6075568
  simp only [CollatzResearch.WordTrace]
  refine ⟨110797084826631117625005679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147729446435508156833340905 110797084826631117625005679)
  ·
    refine ⟨166195627239946676437508519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110797084826631117625005679 166195627239946676437508519)
    ·
      refine ⟨249293440859920014656262779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166195627239946676437508519 249293440859920014656262779)
      ·
        refine ⟨373940161289880021984394169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249293440859920014656262779 373940161289880021984394169)
        ·
          refine ⟨280455120967410016488295627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373940161289880021984394169 280455120967410016488295627)
          ·
            refine ⟨420682681451115024732443441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280455120967410016488295627 420682681451115024732443441)
            ·
              refine ⟨315512011088336268549332581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420682681451115024732443441 315512011088336268549332581)
              ·
                refine ⟨59158502079063050352999859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315512011088336268549332581 59158502079063050352999859)
                ·
                  refine ⟨88737753118594575529499789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59158502079063050352999859 88737753118594575529499789)
                  ·
                    refine ⟨33276657419472965823562421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88737753118594575529499789 33276657419472965823562421)
                    ·
                      refine ⟨3119686633075590545958977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33276657419472965823562421 3119686633075590545958977)
                      ·
                        rfl

theorem cell23_6075568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_6075568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075568 prefixEnd_6075568 := by exact prefixLift 6075568
  have htrace : WordTrace (prefixWord ++ tailWord_6075568) baseStart_6075568 baseEnd_6075568 := by
    simpa [prefixWord, tailWord_6075568, baseEnd_6075568] using wordTrace_append hprefix tailTrace_6075568
  have hstable : (prefixWord ++ tailWord_6075568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075568).length < 2 ^ (prefixWord ++ tailWord_6075568).sum := by decide
  have hdescent : baseEnd_6075568 < baseStart_6075568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075615 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_6075615 : Nat := 118140960795 + 6075615 * 2 ^ 59
def prefixEnd_6075615 : Nat := 4983230072969 + 3 ^ 40 * 6075615 * 2
def baseEnd_6075615 : Nat := 3119710766666351862071261

theorem tailTrace_6075615 : CollatzResearch.WordTrace tailWord_6075615 prefixEnd_6075615 3119710766666351862071261 := by
  unfold tailWord_6075615
  simp only [CollatzResearch.WordTrace]
  refine ⟨221595883884091962276972299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147730589256061308184648199 221595883884091962276972299)
  ·
    refine ⟨332393825826137943415458449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221595883884091962276972299 332393825826137943415458449)
    ·
      refine ⟨249295369369603457561593837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332393825826137943415458449 249295369369603457561593837)
      ·
        refine ⟨93485763513601296585597689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249295369369603457561593837 93485763513601296585597689)
        ·
          refine ⟨70114322635200972439198267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93485763513601296585597689 70114322635200972439198267)
          ·
            refine ⟨105171483952801458658797401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70114322635200972439198267 105171483952801458658797401)
            ·
              refine ⟨78878612964601093994098051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105171483952801458658797401 78878612964601093994098051)
              ·
                refine ⟨118317919446901640991147077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78878612964601093994098051 118317919446901640991147077)
                ·
                  refine ⟨22184609896294057685840077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118317919446901640991147077 22184609896294057685840077)
                  ·
                    refine ⟨8319228711110271632190029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22184609896294057685840077 8319228711110271632190029)
                    ·
                      refine ⟨3119710766666351862071261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319228711110271632190029 3119710766666351862071261)
                      ·
                        rfl

theorem cell23_6075615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_6075615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075615 prefixEnd_6075615 := by exact prefixLift 6075615
  have htrace : WordTrace (prefixWord ++ tailWord_6075615) baseStart_6075615 baseEnd_6075615 := by
    simpa [prefixWord, tailWord_6075615, baseEnd_6075615] using wordTrace_append hprefix tailTrace_6075615
  have hstable : (prefixWord ++ tailWord_6075615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075615).length < 2 ^ (prefixWord ++ tailWord_6075615).sum := by decide
  have hdescent : baseEnd_6075615 < baseStart_6075615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075652 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_6075652 : Nat := 118140960795 + 6075652 * 2 ^ 59
def prefixEnd_6075652 : Nat := 4983230072969 + 3 ^ 40 * 6075652 * 2
def baseEnd_6075652 : Nat := 1039909921816856072436197

theorem tailTrace_6075652 : CollatzResearch.WordTrace tailWord_6075652 prefixEnd_6075652 1039909921816856072436197 := by
  unfold tailWord_6075652
  simp only [CollatzResearch.WordTrace]
  refine ⟨110798616692478958798034605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147731488923305278397379473 110798616692478958798034605)
  ·
    refine ⟨41549481259679609549262977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110798616692478958798034605 41549481259679609549262977)
    ·
      refine ⟨31162110944759707161947233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41549481259679609549262977 31162110944759707161947233)
      ·
        refine ⟨23371583208569780371460425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31162110944759707161947233 23371583208569780371460425)
        ·
          refine ⟨17528687406427335278595319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23371583208569780371460425 17528687406427335278595319)
          ·
            refine ⟨26293031109641002917892979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17528687406427335278595319 26293031109641002917892979)
            ·
              refine ⟨39439546664461504376839469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26293031109641002917892979 39439546664461504376839469)
              ·
                refine ⟨14789829999173064141314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39439546664461504376839469 14789829999173064141314801)
                ·
                  refine ⟨11092372499379798105986101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14789829999173064141314801 11092372499379798105986101)
                  ·
                    refine ⟨1039909921816856072436197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11092372499379798105986101 1039909921816856072436197)
                    ·
                      rfl

theorem cell23_6075652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_6075652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075652 prefixEnd_6075652 := by exact prefixLift 6075652
  have htrace : WordTrace (prefixWord ++ tailWord_6075652) baseStart_6075652 baseEnd_6075652 := by
    simpa [prefixWord, tailWord_6075652, baseEnd_6075652] using wordTrace_append hprefix tailTrace_6075652
  have hstable : (prefixWord ++ tailWord_6075652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075652).length < 2 ^ (prefixWord ++ tailWord_6075652).sum := by decide
  have hdescent : baseEnd_6075652 < baseStart_6075652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075672 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6075672 : Nat := 118140960795 + 6075672 * 2 ^ 59
def prefixEnd_6075672 : Nat := 4983230072969 + 3 ^ 40 * 6075672 * 2
def baseEnd_6075672 : Nat := 3119740035063658139058499

theorem tailTrace_6075672 : CollatzResearch.WordTrace tailWord_6075672 prefixEnd_6075672 3119740035063658139058499 := by
  unfold tailWord_6075672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110798981422442730505898635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147731975229923640674531513 110798981422442730505898635)
  ·
    refine ⟨166198472133664095758847953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110798981422442730505898635 166198472133664095758847953)
    ·
      refine ⟨124648854100248071819135965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166198472133664095758847953 124648854100248071819135965)
      ·
        refine ⟨46743320287593026932175987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124648854100248071819135965 46743320287593026932175987)
        ·
          refine ⟨70114980431389540398263981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46743320287593026932175987 70114980431389540398263981)
          ·
            refine ⟨26293117661771077649348993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70114980431389540398263981 26293117661771077649348993)
            ·
              refine ⟨19719838246328308237011745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26293117661771077649348993 19719838246328308237011745)
              ·
                refine ⟨14789878684746231177758809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19719838246328308237011745 14789878684746231177758809)
                ·
                  refine ⟨11092409013559673383319107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14789878684746231177758809 11092409013559673383319107)
                  ·
                    refine ⟨16638613520339510074978661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11092409013559673383319107 16638613520339510074978661)
                    ·
                      refine ⟨3119740035063658139058499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16638613520339510074978661 3119740035063658139058499)
                      ·
                        rfl

theorem cell23_6075672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6075672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075672 prefixEnd_6075672 := by exact prefixLift 6075672
  have htrace : WordTrace (prefixWord ++ tailWord_6075672) baseStart_6075672 baseEnd_6075672 := by
    simpa [prefixWord, tailWord_6075672, baseEnd_6075672] using wordTrace_append hprefix tailTrace_6075672
  have hstable : (prefixWord ++ tailWord_6075672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075672).length < 2 ^ (prefixWord ++ tailWord_6075672).sum := by decide
  have hdescent : baseEnd_6075672 < baseStart_6075672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075675 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3]
def baseStart_6075675 : Nat := 118140960795 + 6075675 * 2 ^ 59
def prefixEnd_6075675 : Nat := 4983230072969 + 3 ^ 40 * 6075675 * 2
def baseEnd_6075675 : Nat := 3119741575505621627320985

theorem tailTrace_6075675 : CollatzResearch.WordTrace tailWord_6075675 prefixEnd_6075675 3119741575505621627320985 := by
  unfold tailWord_6075675
  simp only [CollatzResearch.WordTrace]
  refine ⟨221598072263874592524156479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147732048175916395016104319 221598072263874592524156479)
  ·
    refine ⟨332397108395811888786234719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221598072263874592524156479 332397108395811888786234719)
    ·
      refine ⟨498595662593717833179352079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332397108395811888786234719 498595662593717833179352079)
      ·
        refine ⟨747893493890576749769028119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498595662593717833179352079 747893493890576749769028119)
        ·
          refine ⟨1121840240835865124653542179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747893493890576749769028119 1121840240835865124653542179)
          ·
            refine ⟨1682760361253797686980313269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121840240835865124653542179 1682760361253797686980313269)
            ·
              refine ⟨157758783867543533154404369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1682760361253797686980313269 157758783867543533154404369)
              ·
                refine ⟨118319087900657649865803277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157758783867543533154404369 118319087900657649865803277)
                ·
                  refine ⟨44369657962746618699676229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118319087900657649865803277 44369657962746618699676229)
                  ·
                    refine ⟨8319310868014991006189293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44369657962746618699676229 8319310868014991006189293)
                    ·
                      refine ⟨3119741575505621627320985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319310868014991006189293 3119741575505621627320985)
                      ·
                        rfl

theorem cell23_6075675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].length) (baseStart_6075675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075675 prefixEnd_6075675 := by exact prefixLift 6075675
  have htrace : WordTrace (prefixWord ++ tailWord_6075675) baseStart_6075675 baseEnd_6075675 := by
    simpa [prefixWord, tailWord_6075675, baseEnd_6075675] using wordTrace_append hprefix tailTrace_6075675
  have hstable : (prefixWord ++ tailWord_6075675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075675).length < 2 ^ (prefixWord ++ tailWord_6075675).sum := by decide
  have hdescent : baseEnd_6075675 < baseStart_6075675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075772 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_6075772 : Nat := 118140960795 + 6075772 * 2 ^ 59
def prefixEnd_6075772 : Nat := 4983230072969 + 3 ^ 40 * 6075772 * 2
def baseEnd_6075772 : Nat := 1039930461043035915936013

theorem tailTrace_6075772 : CollatzResearch.WordTrace tailWord_6075772 prefixEnd_6075772 1039930461043035915936013 := by
  unfold tailWord_6075772
  simp only [CollatzResearch.WordTrace]
  refine ⟨110800805072261589045218785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147734406763015452060291713 110800805072261589045218785)
  ·
    refine ⟨83100603804196191783914089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110800805072261589045218785 83100603804196191783914089)
    ·
      refine ⟨62325452853147143837935567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83100603804196191783914089 62325452853147143837935567)
      ·
        refine ⟨93488179279720715756903351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62325452853147143837935567 93488179279720715756903351)
        ·
          refine ⟨140232268919581073635355027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93488179279720715756903351 140232268919581073635355027)
          ·
            refine ⟨210348403379371610453032541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140232268919581073635355027 210348403379371610453032541)
            ·
              refine ⟨78880651267264353919887203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210348403379371610453032541 78880651267264353919887203)
              ·
                refine ⟨118320976900896530879830805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78880651267264353919887203 118320976900896530879830805)
                ·
                  refine ⟨5546295792229524884992069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118320976900896530879830805 5546295792229524884992069)
                  ·
                    refine ⟨1039930461043035915936013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546295792229524884992069 1039930461043035915936013)
                    ·
                      rfl

theorem cell23_6075772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_6075772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075772 prefixEnd_6075772 := by exact prefixLift 6075772
  have htrace : WordTrace (prefixWord ++ tailWord_6075772) baseStart_6075772 baseEnd_6075772 := by
    simpa [prefixWord, tailWord_6075772, baseEnd_6075772] using wordTrace_append hprefix tailTrace_6075772
  have hstable : (prefixWord ++ tailWord_6075772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075772).length < 2 ^ (prefixWord ++ tailWord_6075772).sum := by decide
  have hdescent : baseEnd_6075772 < baseStart_6075772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075775 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_6075775 : Nat := 118140960795 + 6075775 * 2 ^ 59
def prefixEnd_6075775 : Nat := 4983230072969 + 3 ^ 40 * 6075775 * 2
def baseEnd_6075775 : Nat := 3119792923571071236070525

theorem tailTrace_6075775 : CollatzResearch.WordTrace tailWord_6075775 prefixEnd_6075775 3119792923571071236070525 := by
  unfold tailWord_6075775
  simp only [CollatzResearch.WordTrace]
  refine ⟨221601719563512309602796779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147734479709008206401864519 221601719563512309602796779)
  ·
    refine ⟨332402579345268464404195169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221601719563512309602796779 332402579345268464404195169)
    ·
      refine ⟨249301934508951348303146377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332402579345268464404195169 249301934508951348303146377)
      ·
        refine ⟨186976450881713511227359783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249301934508951348303146377 186976450881713511227359783)
        ·
          refine ⟨280464676322570266841039675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186976450881713511227359783 280464676322570266841039675)
          ·
            refine ⟨420697014483855400261559513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280464676322570266841039675 420697014483855400261559513)
            ·
              refine ⟨315522760862891550196169635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420697014483855400261559513 315522760862891550196169635)
              ·
                refine ⟨473284141294337325294254453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315522760862891550196169635 473284141294337325294254453)
                ·
                  refine ⟨44370388246344124246336355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473284141294337325294254453 44370388246344124246336355)
                  ·
                    refine ⟨66555582369516186369504533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44370388246344124246336355 66555582369516186369504533)
                    ·
                      refine ⟨3119792923571071236070525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66555582369516186369504533 3119792923571071236070525)
                      ·
                        rfl

theorem cell23_6075775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_6075775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075775 prefixEnd_6075775 := by exact prefixLift 6075775
  have htrace : WordTrace (prefixWord ++ tailWord_6075775) baseStart_6075775 baseEnd_6075775 := by
    simpa [prefixWord, tailWord_6075775, baseEnd_6075775] using wordTrace_append hprefix tailTrace_6075775
  have hstable : (prefixWord ++ tailWord_6075775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075775).length < 2 ^ (prefixWord ++ tailWord_6075775).sum := by decide
  have hdescent : baseEnd_6075775 < baseStart_6075775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075779 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 4]
def baseStart_6075779 : Nat := 118140960795 + 6075779 * 2 ^ 59
def prefixEnd_6075779 : Nat := 4983230072969 + 3 ^ 40 * 6075779 * 2
def baseEnd_6075779 : Nat := 3119794977493689220420507

theorem tailTrace_6075779 : CollatzResearch.WordTrace tailWord_6075779 prefixEnd_6075779 3119794977493689220420507 := by
  unfold tailWord_6075779
  simp only [CollatzResearch.WordTrace]
  refine ⟨221601865455497818285942391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147734576970331878857294927 221601865455497818285942391)
  ·
    refine ⟨332402798183246727428913587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221601865455497818285942391 332402798183246727428913587)
    ·
      refine ⟨498604197274870091143370381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332402798183246727428913587 498604197274870091143370381)
      ·
        refine ⟨186976573978076284178763893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498604197274870091143370381 186976573978076284178763893)
        ·
          refine ⟨17529053810444651641759115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186976573978076284178763893 17529053810444651641759115)
          ·
            refine ⟨26293580715666977462638673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17529053810444651641759115 26293580715666977462638673)
            ·
              refine ⟨19720185536750233096979005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26293580715666977462638673 19720185536750233096979005)
              ·
                refine ⟨7395069576281337411367127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19720185536750233096979005 7395069576281337411367127)
                ·
                  refine ⟨11092604364422006117050691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395069576281337411367127 11092604364422006117050691)
                  ·
                    refine ⟨16638906546633009175576037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11092604364422006117050691 16638906546633009175576037)
                    ·
                      refine ⟨3119794977493689220420507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16638906546633009175576037 3119794977493689220420507)
                      ·
                        rfl

theorem cell23_6075779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_6075779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075779 prefixEnd_6075779 := by exact prefixLift 6075779
  have htrace : WordTrace (prefixWord ++ tailWord_6075779) baseStart_6075779 baseEnd_6075779 := by
    simpa [prefixWord, tailWord_6075779, baseEnd_6075779] using wordTrace_append hprefix tailTrace_6075779
  have hstable : (prefixWord ++ tailWord_6075779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075779).length < 2 ^ (prefixWord ++ tailWord_6075779).sum := by decide
  have hdescent : baseEnd_6075779 < baseStart_6075779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075790 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6075790 : Nat := 118140960795 + 6075790 * 2 ^ 59
def prefixEnd_6075790 : Nat := 4983230072969 + 3 ^ 40 * 6075790 * 2
def baseEnd_6075790 : Nat := 3119800625780888677382957

theorem tailTrace_6075790 : CollatzResearch.WordTrace tailWord_6075790 prefixEnd_6075790 3119800625780888677382957 := by
  unfold tailWord_6075790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27700283332307245895574103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147734844438971978109728549 27700283332307245895574103)
  ·
    refine ⟨41550424998460868843361155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27700283332307245895574103 41550424998460868843361155)
    ·
      refine ⟨62325637497691303265041733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41550424998460868843361155 62325637497691303265041733)
      ·
        refine ⟨11686057030817119362195325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62325637497691303265041733 11686057030817119362195325)
        ·
          refine ⟨4382271386556419760823247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11686057030817119362195325 4382271386556419760823247)
          ·
            refine ⟨6573407079834629641234871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382271386556419760823247 6573407079834629641234871)
            ·
              refine ⟨9860110619751944461852307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6573407079834629641234871 9860110619751944461852307)
              ·
                refine ⟨14790165929627916692778461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860110619751944461852307 14790165929627916692778461)
                ·
                  refine ⟨5546312223610468759791923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14790165929627916692778461 5546312223610468759791923)
                  ·
                    refine ⟨8319468335415703139687885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546312223610468759791923 8319468335415703139687885)
                    ·
                      refine ⟨3119800625780888677382957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319468335415703139687885 3119800625780888677382957)
                      ·
                        rfl

theorem cell23_6075790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6075790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075790 prefixEnd_6075790 := by exact prefixLift 6075790
  have htrace : WordTrace (prefixWord ++ tailWord_6075790) baseStart_6075790 baseEnd_6075790 := by
    simpa [prefixWord, tailWord_6075790, baseEnd_6075790] using wordTrace_append hprefix tailTrace_6075790
  have hstable : (prefixWord ++ tailWord_6075790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075790).length < 2 ^ (prefixWord ++ tailWord_6075790).sum := by decide
  have hdescent : baseEnd_6075790 < baseStart_6075790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075802 : List Nat := [3, 1, 1, 4, 1, 1, 4, 8]
def baseStart_6075802 : Nat := 118140960795 + 6075802 * 2 ^ 59
def prefixEnd_6075802 : Nat := 4983230072969 + 3 ^ 40 * 6075802 * 2
def baseEnd_6075802 : Nat := 115548399538842319645663

theorem tailTrace_6075802 : CollatzResearch.WordTrace tailWord_6075802 prefixEnd_6075802 115548399538842319645663 := by
  unfold tailWord_6075802
  simp only [CollatzResearch.WordTrace]
  refine ⟨55400676083603623303507415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147735136222942995476019773 55400676083603623303507415)
  ·
    refine ⟨83101014125405434955261123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55400676083603623303507415 83101014125405434955261123)
    ·
      refine ⟨124651521188108152432891685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83101014125405434955261123 124651521188108152432891685)
      ·
        refine ⟨23372160222770278581167191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124651521188108152432891685 23372160222770278581167191)
        ·
          refine ⟨35058240334155417871750787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23372160222770278581167191 35058240334155417871750787)
          ·
            refine ⟨52587360501233126807626181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35058240334155417871750787 52587360501233126807626181)
            ·
              refine ⟨9860130093981211276429909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52587360501233126807626181 9860130093981211276429909)
              ·
                refine ⟨115548399538842319645663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9860130093981211276429909 115548399538842319645663)
                ·
                  rfl

theorem cell23_6075802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_6075802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075802 prefixEnd_6075802 := by exact prefixLift 6075802
  have htrace : WordTrace (prefixWord ++ tailWord_6075802) baseStart_6075802 baseEnd_6075802 := by
    simpa [prefixWord, tailWord_6075802, baseEnd_6075802] using wordTrace_append hprefix tailTrace_6075802
  have hstable : (prefixWord ++ tailWord_6075802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075802).length < 2 ^ (prefixWord ++ tailWord_6075802).sum := by decide
  have hdescent : baseEnd_6075802 < baseStart_6075802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075829 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_6075829 : Nat := 118140960795 + 6075829 * 2 ^ 59
def prefixEnd_6075829 : Nat := 4983230072969 + 3 ^ 40 * 6075829 * 2
def baseEnd_6075829 : Nat := 3119820651526414024795277

theorem tailTrace_6075829 : CollatzResearch.WordTrace tailWord_6075829 prefixEnd_6075829 3119820651526414024795277 := by
  unfold tailWord_6075829
  simp only [CollatzResearch.WordTrace]
  refine ⟨221603689105316676825262541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147735792736877784550175027 221603689105316676825262541)
  ·
    refine ⟨83101383414493753809473453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221603689105316676825262541 83101383414493753809473453)
    ·
      refine ⟨31163018780435157678552545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83101383414493753809473453 31163018780435157678552545)
      ·
        refine ⟨23372264085326368258914409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31163018780435157678552545 23372264085326368258914409)
        ·
          refine ⟨17529198063994776194185807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23372264085326368258914409 17529198063994776194185807)
          ·
            refine ⟨26293797095992164291278711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17529198063994776194185807 26293797095992164291278711)
            ·
              refine ⟨39440695643988246436918067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26293797095992164291278711 39440695643988246436918067)
              ·
                refine ⟨59161043465982369655377101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39440695643988246436918067 59161043465982369655377101)
                ·
                  refine ⟨22185391299743388620766413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59161043465982369655377101 22185391299743388620766413)
                  ·
                    refine ⟨8319521737403770732787405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22185391299743388620766413 8319521737403770732787405)
                    ·
                      refine ⟨3119820651526414024795277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319521737403770732787405 3119820651526414024795277)
                      ·
                        rfl

theorem cell23_6075829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_6075829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075829 prefixEnd_6075829 := by exact prefixLift 6075829
  have htrace : WordTrace (prefixWord ++ tailWord_6075829) baseStart_6075829 baseEnd_6075829 := by
    simpa [prefixWord, tailWord_6075829, baseEnd_6075829] using wordTrace_append hprefix tailTrace_6075829
  have hstable : (prefixWord ++ tailWord_6075829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075829).length < 2 ^ (prefixWord ++ tailWord_6075829).sum := by decide
  have hdescent : baseEnd_6075829 < baseStart_6075829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075833 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6075833 : Nat := 118140960795 + 6075833 * 2 ^ 59
def prefixEnd_6075833 : Nat := 4983230072969 + 3 ^ 40 * 6075833 * 2
def baseEnd_6075833 : Nat := 3119822705449032009145259

theorem tailTrace_6075833 : CollatzResearch.WordTrace tailWord_6075833 prefixEnd_6075833 3119822705449032009145259 := by
  unfold tailWord_6075833
  simp only [CollatzResearch.WordTrace]
  refine ⟨221603834997302185508408153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147735889998201457005605435 221603834997302185508408153)
  ·
    refine ⟨166202876247976639131306115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221603834997302185508408153 166202876247976639131306115)
    ·
      refine ⟨249304314371964958696959173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166202876247976639131306115 249304314371964958696959173)
      ·
        refine ⟨46744558944743429755679845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249304314371964958696959173 46744558944743429755679845)
        ·
          refine ⟨8764604802139393079189971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46744558944743429755679845 8764604802139393079189971)
          ·
            refine ⟨13146907203209089618784957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764604802139393079189971 13146907203209089618784957)
            ·
              refine ⟨4930090201203408607044359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13146907203209089618784957 4930090201203408607044359)
              ·
                refine ⟨7395135301805112910566539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930090201203408607044359 7395135301805112910566539)
                ·
                  refine ⟨11092702952707669365849809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395135301805112910566539 11092702952707669365849809)
                  ·
                    refine ⟨8319527214530752024387357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11092702952707669365849809 8319527214530752024387357)
                    ·
                      refine ⟨3119822705449032009145259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319527214530752024387357 3119822705449032009145259)
                      ·
                        rfl

theorem cell23_6075833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6075833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075833 prefixEnd_6075833 := by exact prefixLift 6075833
  have htrace : WordTrace (prefixWord ++ tailWord_6075833) baseStart_6075833 baseEnd_6075833 := by
    simpa [prefixWord, tailWord_6075833, baseEnd_6075833] using wordTrace_append hprefix tailTrace_6075833
  have hstable : (prefixWord ++ tailWord_6075833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075833).length < 2 ^ (prefixWord ++ tailWord_6075833).sum := by decide
  have hdescent : baseEnd_6075833 < baseStart_6075833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075872 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_6075872 : Nat := 118140960795 + 6075872 * 2 ^ 59
def prefixEnd_6075872 : Nat := 4983230072969 + 3 ^ 40 * 6075872 * 2
def baseEnd_6075872 : Nat := 3119842731194557356557579

theorem tailTrace_6075872 : CollatzResearch.WordTrace tailWord_6075872 prefixEnd_6075872 3119842731194557356557579 := by
  unfold tailWord_6075872
  simp only [CollatzResearch.WordTrace]
  refine ⟨110802628722080447584538935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147736838296107263446051913 110802628722080447584538935)
  ·
    refine ⟨166203943083120671376808403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110802628722080447584538935 166203943083120671376808403)
    ·
      refine ⟨249305914624681007065212605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166203943083120671376808403 249305914624681007065212605)
      ·
        refine ⟨93489717984255377649454727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249305914624681007065212605 93489717984255377649454727)
        ·
          refine ⟨140234576976383066474182091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93489717984255377649454727 140234576976383066474182091)
          ·
            refine ⟨210351865464574599711273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140234576976383066474182091 210351865464574599711273137)
            ·
              refine ⟨157763899098430949783454853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210351865464574599711273137 157763899098430949783454853)
              ·
                refine ⟨29580731080955803084397785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157763899098430949783454853 29580731080955803084397785)
                ·
                  refine ⟨22185548310716852313298339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29580731080955803084397785 22185548310716852313298339)
                  ·
                    refine ⟨33278322466075278469947509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22185548310716852313298339 33278322466075278469947509)
                    ·
                      refine ⟨3119842731194557356557579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33278322466075278469947509 3119842731194557356557579)
                      ·
                        rfl

theorem cell23_6075872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_6075872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075872 prefixEnd_6075872 := by exact prefixLift 6075872
  have htrace : WordTrace (prefixWord ++ tailWord_6075872) baseStart_6075872 baseEnd_6075872 := by
    simpa [prefixWord, tailWord_6075872, baseEnd_6075872] using wordTrace_append hprefix tailTrace_6075872
  have hstable : (prefixWord ++ tailWord_6075872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075872).length < 2 ^ (prefixWord ++ tailWord_6075872).sum := by decide
  have hdescent : baseEnd_6075872 < baseStart_6075872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075886 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_6075886 : Nat := 118140960795 + 6075886 * 2 ^ 59
def prefixEnd_6075886 : Nat := 4983230072969 + 3 ^ 40 * 6075886 * 2
def baseEnd_6075886 : Nat := 3119849919923720301782515

theorem tailTrace_6075886 : CollatzResearch.WordTrace tailWord_6075886 prefixEnd_6075886 3119849919923720301782515 := by
  unfold tailWord_6075886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27700721008263771945010939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147737178710740117040058341 27700721008263771945010939)
  ·
    refine ⟨41551081512395657917516409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27700721008263771945010939 41551081512395657917516409)
    ·
      refine ⟨31163311134296743438137307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41551081512395657917516409 31163311134296743438137307)
      ·
        refine ⟨46744966701445115157205961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31163311134296743438137307 46744966701445115157205961)
        ·
          refine ⟨35058725026083836367904471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46744966701445115157205961 35058725026083836367904471)
          ·
            refine ⟨52588087539125754551856707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35058725026083836367904471 52588087539125754551856707)
            ·
              refine ⟨78882131308688631827785061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52588087539125754551856707 78882131308688631827785061)
              ·
                refine ⟨14790399620379118467709699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78882131308688631827785061 14790399620379118467709699)
                ·
                  refine ⟨22185599430568677701564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14790399620379118467709699 22185599430568677701564549)
                  ·
                    refine ⟨4159799893231627069043353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22185599430568677701564549 4159799893231627069043353)
                    ·
                      refine ⟨3119849919923720301782515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159799893231627069043353 3119849919923720301782515)
                      ·
                        rfl

theorem cell23_6075886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_6075886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075886 prefixEnd_6075886 := by exact prefixLift 6075886
  have htrace : WordTrace (prefixWord ++ tailWord_6075886) baseStart_6075886 baseEnd_6075886 := by
    simpa [prefixWord, tailWord_6075886, baseEnd_6075886] using wordTrace_append hprefix tailTrace_6075886
  have hstable : (prefixWord ++ tailWord_6075886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075886).length < 2 ^ (prefixWord ++ tailWord_6075886).sum := by decide
  have hdescent : baseEnd_6075886 < baseStart_6075886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075890 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6075890 : Nat := 118140960795 + 6075890 * 2 ^ 59
def prefixEnd_6075890 : Nat := 4983230072969 + 3 ^ 40 * 6075890 * 2
def baseEnd_6075890 : Nat := 3119851973846338286132497

theorem tailTrace_6075890 : CollatzResearch.WordTrace tailWord_6075890 prefixEnd_6075890 3119851973846338286132497 := by
  unfold tailWord_6075890
  simp only [CollatzResearch.WordTrace]
  refine ⟨55401478489523921060808281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147737275972063789495488749 55401478489523921060808281)
  ·
    refine ⟨41551108867142940795606211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55401478489523921060808281 41551108867142940795606211)
    ·
      refine ⟨62326663300714411193409317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41551108867142940795606211 62326663300714411193409317)
      ·
        refine ⟨11686249368883952098764247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62326663300714411193409317 11686249368883952098764247)
        ·
          refine ⟨17529374053325928148146371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686249368883952098764247 17529374053325928148146371)
          ·
            refine ⟨26294061079988892222219557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17529374053325928148146371 26294061079988892222219557)
            ·
              refine ⟨4930136452497917291666167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26294061079988892222219557 4930136452497917291666167)
              ·
                refine ⟨7395204678746875937499251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930136452497917291666167 7395204678746875937499251)
                ·
                  refine ⟨11092807018120313906248877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395204678746875937499251 11092807018120313906248877)
                  ·
                    refine ⟨4159802631795117714843329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11092807018120313906248877 4159802631795117714843329)
                    ·
                      refine ⟨3119851973846338286132497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159802631795117714843329 3119851973846338286132497)
                      ·
                        rfl

theorem cell23_6075890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6075890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075890 prefixEnd_6075890 := by exact prefixLift 6075890
  have htrace : WordTrace (prefixWord ++ tailWord_6075890) baseStart_6075890 baseEnd_6075890 := by
    simpa [prefixWord, tailWord_6075890, baseEnd_6075890] using wordTrace_append hprefix tailTrace_6075890
  have hstable : (prefixWord ++ tailWord_6075890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075890).length < 2 ^ (prefixWord ++ tailWord_6075890).sum := by decide
  have hdescent : baseEnd_6075890 < baseStart_6075890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075959 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_6075959 : Nat := 118140960795 + 6075959 * 2 ^ 59
def prefixEnd_6075959 : Nat := 4983230072969 + 3 ^ 40 * 6075959 * 2
def baseEnd_6075959 : Nat := 3119887404011498516169679

theorem tailTrace_6075959 : CollatzResearch.WordTrace tailWord_6075959 prefixEnd_6075959 3119887404011498516169679 := by
  unfold tailWord_6075959
  simp only [CollatzResearch.WordTrace]
  refine ⟨221608430594845709027494931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147738953729897139351663287 221608430594845709027494931)
  ·
    refine ⟨332412645892268563541242397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221608430594845709027494931 332412645892268563541242397)
    ·
      refine ⟨124654742209600711327965899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332412645892268563541242397 124654742209600711327965899)
      ·
        refine ⟨186982113314401066991948849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124654742209600711327965899 186982113314401066991948849)
        ·
          refine ⟨140236584985800800243961637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186982113314401066991948849 140236584985800800243961637)
          ·
            refine ⟨26294359684837650045742807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140236584985800800243961637 26294359684837650045742807)
            ·
              refine ⟨39441539527256475068614211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26294359684837650045742807 39441539527256475068614211)
              ·
                refine ⟨59162309290884712602921317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39441539527256475068614211 59162309290884712602921317)
                ·
                  refine ⟨11092932992040883613047747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59162309290884712602921317 11092932992040883613047747)
                  ·
                    refine ⟨16639399488061325419571621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11092932992040883613047747 16639399488061325419571621)
                    ·
                      refine ⟨3119887404011498516169679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16639399488061325419571621 3119887404011498516169679)
                      ·
                        rfl

theorem cell23_6075959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_6075959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075959 prefixEnd_6075959 := by exact prefixLift 6075959
  have htrace : WordTrace (prefixWord ++ tailWord_6075959) baseStart_6075959 baseEnd_6075959 := by
    simpa [prefixWord, tailWord_6075959, baseEnd_6075959] using wordTrace_append hprefix tailTrace_6075959
  have hstable : (prefixWord ++ tailWord_6075959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075959).length < 2 ^ (prefixWord ++ tailWord_6075959).sum := by decide
  have hdescent : baseEnd_6075959 < baseStart_6075959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6075979 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3]
def baseStart_6075979 : Nat := 118140960795 + 6075979 * 2 ^ 59
def prefixEnd_6075979 : Nat := 4983230072969 + 3 ^ 40 * 6075979 * 2
def baseEnd_6075979 : Nat := 3119897673624588437919587

theorem tailTrace_6075979 : CollatzResearch.WordTrace tailWord_6075979 prefixEnd_6075979 3119897673624588437919587 := by
  unfold tailWord_6075979
  simp only [CollatzResearch.WordTrace]
  refine ⟨221609160054773252443222991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147739440036515501628815327 221609160054773252443222991)
  ·
    refine ⟨332413740082159878664834487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221609160054773252443222991 332413740082159878664834487)
    ·
      refine ⟨498620610123239817997251731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332413740082159878664834487 498620610123239817997251731)
      ·
        refine ⟨747930915184859726995877597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498620610123239817997251731 747930915184859726995877597)
        ·
          refine ⟨280474093194322397623454099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747930915184859726995877597 280474093194322397623454099)
          ·
            refine ⟨420711139791483596435181149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280474093194322397623454099 420711139791483596435181149)
            ·
              refine ⟨157766677421806348663192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420711139791483596435181149 157766677421806348663192931)
              ·
                refine ⟨236650016132709522994789397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157766677421806348663192931 236650016132709522994789397)
                ·
                  refine ⟨11092969506220758890380753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236650016132709522994789397 11092969506220758890380753)
                  ·
                    refine ⟨8319727129665569167785565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11092969506220758890380753 8319727129665569167785565)
                    ·
                      refine ⟨3119897673624588437919587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319727129665569167785565 3119897673624588437919587)
                      ·
                        rfl

theorem cell23_6075979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].length) (baseStart_6075979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6075979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6075979 prefixEnd_6075979 := by exact prefixLift 6075979
  have htrace : WordTrace (prefixWord ++ tailWord_6075979) baseStart_6075979 baseEnd_6075979 := by
    simpa [prefixWord, tailWord_6075979, baseEnd_6075979] using wordTrace_append hprefix tailTrace_6075979
  have hstable : (prefixWord ++ tailWord_6075979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6075979).length < 2 ^ (prefixWord ++ tailWord_6075979).sum := by decide
  have hdescent : baseEnd_6075979 < baseStart_6075979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6075979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076016 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 6]
def baseStart_6076016 : Nat := 118140960795 + 6076016 * 2 ^ 59
def prefixEnd_6076016 : Nat := 4983230072969 + 3 ^ 40 * 6076016 * 2
def baseEnd_6076016 : Nat := 346657408045422754795213

theorem tailTrace_6076016 : CollatzResearch.WordTrace tailWord_6076016 prefixEnd_6076016 346657408045422754795213 := by
  unfold tailWord_6076016
  simp only [CollatzResearch.WordTrace]
  refine ⟨110805254777819603881159951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147740339703759471841546601 110805254777819603881159951)
  ·
    refine ⟨166207882166729405821739927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110805254777819603881159951 166207882166729405821739927)
    ·
      refine ⟨249311823250094108732609891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166207882166729405821739927 249311823250094108732609891)
      ·
        refine ⟨373967734875141163098914837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249311823250094108732609891 373967734875141163098914837)
        ·
          refine ⟨17529737572272242020261633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 373967734875141163098914837 17529737572272242020261633)
          ·
            refine ⟨13147303179204181515196225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17529737572272242020261633 13147303179204181515196225)
            ·
              refine ⟨9860477384403136136397169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13147303179204181515196225 9860477384403136136397169)
              ·
                refine ⟨7395358038302352102297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860477384403136136397169 7395358038302352102297877)
                ·
                  refine ⟨346657408045422754795213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7395358038302352102297877 346657408045422754795213)
                  ·
                    rfl

theorem cell23_6076016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_6076016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076016 prefixEnd_6076016 := by exact prefixLift 6076016
  have htrace : WordTrace (prefixWord ++ tailWord_6076016) baseStart_6076016 baseEnd_6076016 := by
    simpa [prefixWord, tailWord_6076016, baseEnd_6076016] using wordTrace_append hprefix tailTrace_6076016
  have hstable : (prefixWord ++ tailWord_6076016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076016).length < 2 ^ (prefixWord ++ tailWord_6076016).sum := by decide
  have hdescent : baseEnd_6076016 < baseStart_6076016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076046 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_6076046 : Nat := 118140960795 + 6076046 * 2 ^ 59
def prefixEnd_6076046 : Nat := 4983230072969 + 3 ^ 40 * 6076046 * 2
def baseEnd_6076046 : Nat := 1039977358942813225260593

theorem tailTrace_6076046 : CollatzResearch.WordTrace tailWord_6076046 prefixEnd_6076046 1039977358942813225260593 := by
  unfold tailWord_6076046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27701450468191315360738999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147741069163687015257274661 27701450468191315360738999)
  ·
    refine ⟨41552175702286973041108499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27701450468191315360738999 41552175702286973041108499)
    ·
      refine ⟨62328263553430459561662749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41552175702286973041108499 62328263553430459561662749)
      ·
        refine ⟨23373098832536422335623531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62328263553430459561662749 23373098832536422335623531)
        ·
          refine ⟨35059648248804633503435297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23373098832536422335623531 35059648248804633503435297)
          ·
            refine ⟨26294736186603475127576473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35059648248804633503435297 26294736186603475127576473)
            ·
              refine ⟨19721052139952606345682355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26294736186603475127576473 19721052139952606345682355)
              ·
                refine ⟨29581578209928909518523533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19721052139952606345682355 29581578209928909518523533)
                ·
                  refine ⟨11093091828723341069446325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29581578209928909518523533 11093091828723341069446325)
                  ·
                    refine ⟨1039977358942813225260593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11093091828723341069446325 1039977358942813225260593)
                    ·
                      rfl

theorem cell23_6076046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_6076046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076046 prefixEnd_6076046 := by exact prefixLift 6076046
  have htrace : WordTrace (prefixWord ++ tailWord_6076046) baseStart_6076046 baseEnd_6076046 := by
    simpa [prefixWord, tailWord_6076046, baseEnd_6076046] using wordTrace_append hprefix tailTrace_6076046
  have hstable : (prefixWord ++ tailWord_6076046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076046).length < 2 ^ (prefixWord ++ tailWord_6076046).sum := by decide
  have hdescent : baseEnd_6076046 < baseStart_6076046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076079 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_6076079 : Nat := 118140960795 + 6076079 * 2 ^ 59
def prefixEnd_6076079 : Nat := 4983230072969 + 3 ^ 40 * 6076079 * 2
def baseEnd_6076079 : Nat := 3119949021690038046669127

theorem tailTrace_6076079 : CollatzResearch.WordTrace tailWord_6076079 prefixEnd_6076079 3119949021690038046669127 := by
  unfold tailWord_6076079
  simp only [CollatzResearch.WordTrace]
  refine ⟨221612807354410969521863291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147741871569607313014575527 221612807354410969521863291)
  ·
    refine ⟨332419211031616454282794937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221612807354410969521863291 332419211031616454282794937)
    ·
      refine ⟨249314408273712340712096203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332419211031616454282794937 249314408273712340712096203)
      ·
        refine ⟨373971612410568511068144305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249314408273712340712096203 373971612410568511068144305)
        ·
          refine ⟨280478709307926383301108229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373971612410568511068144305 280478709307926383301108229)
          ·
            refine ⟨52589757995236196868957793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280478709307926383301108229 52589757995236196868957793)
            ·
              refine ⟨39442318496427147651718345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52589757995236196868957793 39442318496427147651718345)
              ·
                refine ⟨29581738872320360738788759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39442318496427147651718345 29581738872320360738788759)
                ·
                  refine ⟨44372608308480541108183139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29581738872320360738788759 44372608308480541108183139)
                  ·
                    refine ⟨66558912462720811662274709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44372608308480541108183139 66558912462720811662274709)
                    ·
                      refine ⟨3119949021690038046669127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66558912462720811662274709 3119949021690038046669127)
                      ·
                        rfl

theorem cell23_6076079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_6076079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076079 prefixEnd_6076079 := by exact prefixLift 6076079
  have htrace : WordTrace (prefixWord ++ tailWord_6076079) baseStart_6076079 baseEnd_6076079 := by
    simpa [prefixWord, tailWord_6076079, baseEnd_6076079] using wordTrace_append hprefix tailTrace_6076079
  have hstable : (prefixWord ++ tailWord_6076079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076079).length < 2 ^ (prefixWord ++ tailWord_6076079).sum := by decide
  have hdescent : baseEnd_6076079 < baseStart_6076079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076100 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6076100 : Nat := 118140960795 + 6076100 * 2 ^ 59
def prefixEnd_6076100 : Nat := 4983230072969 + 3 ^ 40 * 6076100 * 2
def baseEnd_6076100 : Nat := 3119959804783782464506531

theorem tailTrace_6076100 : CollatzResearch.WordTrace tailWord_6076100 prefixEnd_6076100 3119959804783782464506531 := by
  unfold tailWord_6076100
  simp only [CollatzResearch.WordTrace]
  refine ⟨110806786643667445054188877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147742382191556593405585169 110806786643667445054188877)
  ·
    refine ⟨41552544991375291895320829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110806786643667445054188877 41552544991375291895320829)
    ·
      refine ⟨15582204371765734460745311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41552544991375291895320829 15582204371765734460745311)
      ·
        refine ⟨23373306557648601691117967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15582204371765734460745311 23373306557648601691117967)
        ·
          refine ⟨35059959836472902536676951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23373306557648601691117967 35059959836472902536676951)
          ·
            refine ⟨52589939754709353805015427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35059959836472902536676951 52589939754709353805015427)
            ·
              refine ⟨78884909632064030707523141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52589939754709353805015427 78884909632064030707523141)
              ·
                refine ⟨14790920556012005757660589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78884909632064030707523141 14790920556012005757660589)
                ·
                  refine ⟨5546595208504502159122721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14790920556012005757660589 5546595208504502159122721)
                  ·
                    refine ⟨4159946406378376619342041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5546595208504502159122721 4159946406378376619342041)
                    ·
                      refine ⟨3119959804783782464506531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159946406378376619342041 3119959804783782464506531)
                      ·
                        rfl

theorem cell23_6076100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6076100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076100 prefixEnd_6076100 := by exact prefixLift 6076100
  have htrace : WordTrace (prefixWord ++ tailWord_6076100) baseStart_6076100 baseEnd_6076100 := by
    simpa [prefixWord, tailWord_6076100, baseEnd_6076100] using wordTrace_append hprefix tailTrace_6076100
  have hstable : (prefixWord ++ tailWord_6076100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076100).length < 2 ^ (prefixWord ++ tailWord_6076100).sum := by decide
  have hdescent : baseEnd_6076100 < baseStart_6076100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076103 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_6076103 : Nat := 118140960795 + 6076103 * 2 ^ 59
def prefixEnd_6076103 : Nat := 4983230072969 + 3 ^ 40 * 6076103 * 2
def baseEnd_6076103 : Nat := 3119961345225745952769017

theorem tailTrace_6076103 : CollatzResearch.WordTrace tailWord_6076103 prefixEnd_6076103 3119961345225745952769017 := by
  unfold tailWord_6076103
  simp only [CollatzResearch.WordTrace]
  refine ⟨221613682706324021620736963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147742455137549347747157975 221613682706324021620736963)
  ·
    refine ⟨332420524059486032431105445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221613682706324021620736963 332420524059486032431105445)
    ·
      refine ⟨62328848261153631080832271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332420524059486032431105445 62328848261153631080832271)
      ·
        refine ⟨93493272391730446621248407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62328848261153631080832271 93493272391730446621248407)
        ·
          refine ⟨140239908587595669931872611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93493272391730446621248407 140239908587595669931872611)
          ·
            refine ⟨210359862881393504897808917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140239908587595669931872611 210359862881393504897808917)
            ·
              refine ⟨9860618572565320542084793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210359862881393504897808917 9860618572565320542084793)
              ·
                refine ⟨7395463929423990406563595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860618572565320542084793 7395463929423990406563595)
                ·
                  refine ⟨11093195894135985609845393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395463929423990406563595 11093195894135985609845393)
                  ·
                    refine ⟨8319896920601989207384045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11093195894135985609845393 8319896920601989207384045)
                    ·
                      refine ⟨3119961345225745952769017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319896920601989207384045 3119961345225745952769017)
                      ·
                        rfl

theorem cell23_6076103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_6076103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076103 prefixEnd_6076103 := by exact prefixLift 6076103
  have htrace : WordTrace (prefixWord ++ tailWord_6076103) baseStart_6076103 baseEnd_6076103 := by
    simpa [prefixWord, tailWord_6076103, baseEnd_6076103] using wordTrace_append hprefix tailTrace_6076103
  have hstable : (prefixWord ++ tailWord_6076103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076103).length < 2 ^ (prefixWord ++ tailWord_6076103).sum := by decide
  have hdescent : baseEnd_6076103 < baseStart_6076103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076106 : List Nat := [3, 1, 2, 1, 5, 1, 1, 9]
def baseStart_6076106 : Nat := 118140960795 + 6076106 * 2 ^ 59
def prefixEnd_6076106 : Nat := 4983230072969 + 3 ^ 40 * 6076106 * 2
def baseEnd_6076106 : Nat := 115554180950655905223389

theorem tailTrace_6076106 : CollatzResearch.WordTrace tailWord_6076106 prefixEnd_6076106 115554180950655905223389 := by
  unfold tailWord_6076106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55403448031328288283274043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147742528083542102088730781 55403448031328288283274043)
  ·
    refine ⟨83105172046992432424911065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55403448031328288283274043 83105172046992432424911065)
    ·
      refine ⟨62328879035244324318683299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83105172046992432424911065 62328879035244324318683299)
      ·
        refine ⟨93493318552866486478024949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62328879035244324318683299 93493318552866486478024949)
        ·
          refine ⟨8764998614331233107314839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93493318552866486478024949 8764998614331233107314839)
          ·
            refine ⟨13147497921496849660972259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764998614331233107314839 13147497921496849660972259)
            ·
              refine ⟨19721246882245274491458389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13147497921496849660972259 19721246882245274491458389)
              ·
                refine ⟨115554180950655905223389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19721246882245274491458389 115554180950655905223389)
                ·
                  rfl

theorem cell23_6076106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_6076106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076106 prefixEnd_6076106 := by exact prefixLift 6076106
  have htrace : WordTrace (prefixWord ++ tailWord_6076106) baseStart_6076106 baseEnd_6076106 := by
    simpa [prefixWord, tailWord_6076106, baseEnd_6076106] using wordTrace_append hprefix tailTrace_6076106
  have hstable : (prefixWord ++ tailWord_6076106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076106).length < 2 ^ (prefixWord ++ tailWord_6076106).sum := by decide
  have hdescent : baseEnd_6076106 < baseStart_6076106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076133 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6076133 : Nat := 118140960795 + 6076133 * 2 ^ 59
def prefixEnd_6076133 : Nat := 4983230072969 + 3 ^ 40 * 6076133 * 2
def baseEnd_6076133 : Nat := 3119976749645380835393879

theorem tailTrace_6076133 : CollatzResearch.WordTrace tailWord_6076133 prefixEnd_6076133 3119976749645380835393879 := by
  unfold tailWord_6076133
  simp only [CollatzResearch.WordTrace]
  refine ⟨221614776896215336744329053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147743184597476891162886035 221614776896215336744329053)
  ·
    refine ⟨83105541336080751279123395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221614776896215336744329053 83105541336080751279123395)
    ·
      refine ⟨124658312004121126918685093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83105541336080751279123395 124658312004121126918685093)
      ·
        refine ⟨23373433500772711297253455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124658312004121126918685093 23373433500772711297253455)
        ·
          refine ⟨35060150251159066945880183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23373433500772711297253455 35060150251159066945880183)
          ·
            refine ⟨52590225376738600418820275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35060150251159066945880183 52590225376738600418820275)
            ·
              refine ⟨78885338065107900628230413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52590225376738600418820275 78885338065107900628230413)
              ·
                refine ⟨29582001774415462735586405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78885338065107900628230413 29582001774415462735586405)
                ·
                  refine ⟨5546625332702899262922451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29582001774415462735586405 5546625332702899262922451)
                  ·
                    refine ⟨8319937999054348894383677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546625332702899262922451 8319937999054348894383677)
                    ·
                      refine ⟨3119976749645380835393879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8319937999054348894383677 3119976749645380835393879)
                      ·
                        rfl

theorem cell23_6076133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6076133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076133 prefixEnd_6076133 := by exact prefixLift 6076133
  have htrace : WordTrace (prefixWord ++ tailWord_6076133) baseStart_6076133 baseEnd_6076133 := by
    simpa [prefixWord, tailWord_6076133, baseEnd_6076133] using wordTrace_append hprefix tailTrace_6076133
  have hstable : (prefixWord ++ tailWord_6076133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076133).length < 2 ^ (prefixWord ++ tailWord_6076133).sum := by decide
  have hdescent : baseEnd_6076133 < baseStart_6076133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076143 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 3, 3, 2]
def baseStart_6076143 : Nat := 118140960795 + 6076143 * 2 ^ 59
def prefixEnd_6076143 : Nat := 4983230072969 + 3 ^ 40 * 6076143 * 2
def baseEnd_6076143 : Nat := 3119981884451925796268833

theorem tailTrace_6076143 : CollatzResearch.WordTrace tailWord_6076143 prefixEnd_6076143 3119981884451925796268833 := by
  unfold tailWord_6076143
  simp only [CollatzResearch.WordTrace]
  refine ⟨221615141626179108452193083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147743427750786072301462055 221615141626179108452193083)
  ·
    refine ⟨332422712439268662678289625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221615141626179108452193083 332422712439268662678289625)
    ·
      refine ⟨249317034329451497008717219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332422712439268662678289625 249317034329451497008717219)
      ·
        refine ⟨373975551494177245513075829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249317034329451497008717219 373975551494177245513075829)
        ·
          refine ⟨35060207952579116766850859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373975551494177245513075829 35060207952579116766850859)
          ·
            refine ⟨52590311928868675150276289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35060207952579116766850859 52590311928868675150276289)
            ·
              refine ⟨39442733946651506362707217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52590311928868675150276289 39442733946651506362707217)
              ·
                refine ⟨29582050459988629772030413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39442733946651506362707217 29582050459988629772030413)
                ·
                  refine ⟨11093268922495736164511405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29582050459988629772030413 11093268922495736164511405)
                  ·
                    refine ⟨4159975845935901061691777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11093268922495736164511405 4159975845935901061691777)
                    ·
                      refine ⟨3119981884451925796268833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4159975845935901061691777 3119981884451925796268833)
                      ·
                        rfl

theorem cell23_6076143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3, 2].length) (baseStart_6076143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076143 prefixEnd_6076143 := by exact prefixLift 6076143
  have htrace : WordTrace (prefixWord ++ tailWord_6076143) baseStart_6076143 baseEnd_6076143 := by
    simpa [prefixWord, tailWord_6076143, baseEnd_6076143] using wordTrace_append hprefix tailTrace_6076143
  have hstable : (prefixWord ++ tailWord_6076143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076143).length < 2 ^ (prefixWord ++ tailWord_6076143).sum := by decide
  have hdescent : baseEnd_6076143 < baseStart_6076143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076179 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 11]
def baseStart_6076179 : Nat := 118140960795 + 6076179 * 2 ^ 59
def prefixEnd_6076179 : Nat := 4983230072969 + 3 ^ 40 * 6076179 * 2
def baseEnd_6076179 : Nat := 346666707750609739490963

theorem tailTrace_6076179 : CollatzResearch.WordTrace tailWord_6076179 prefixEnd_6076179 346666707750609739490963 := by
  unfold tailWord_6076179
  simp only [CollatzResearch.WordTrace]
  refine ⟨221616454654048686600503591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147744303102699124400335727 221616454654048686600503591)
  ·
    refine ⟨332424681981073029900755387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221616454654048686600503591 332424681981073029900755387)
    ·
      refine ⟨498637022971609544851133081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332424681981073029900755387 498637022971609544851133081)
      ·
        refine ⟨373977767228707158638349811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498637022971609544851133081 373977767228707158638349811)
        ·
          refine ⟨560966650843060737957524717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373977767228707158638349811 560966650843060737957524717)
          ·
            refine ⟨210362494066147776734071769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560966650843060737957524717 210362494066147776734071769)
            ·
              refine ⟨157771870549610832550553827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210362494066147776734071769 157771870549610832550553827)
              ·
                refine ⟨236657805824416248825830741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157771870549610832550553827 236657805824416248825830741)
                ·
                  refine ⟨346666707750609739490963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 236657805824416248825830741 346666707750609739490963)
                  ·
                    rfl

theorem cell23_6076179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 11].length) (baseStart_6076179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076179 prefixEnd_6076179 := by exact prefixLift 6076179
  have htrace : WordTrace (prefixWord ++ tailWord_6076179) baseStart_6076179 baseEnd_6076179 := by
    simpa [prefixWord, tailWord_6076179, baseEnd_6076179] using wordTrace_append hprefix tailTrace_6076179
  have hstable : (prefixWord ++ tailWord_6076179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076179).length < 2 ^ (prefixWord ++ tailWord_6076179).sum := by decide
  have hdescent : baseEnd_6076179 < baseStart_6076179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076213 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 7]
def baseStart_6076213 : Nat := 118140960795 + 6076213 * 2 ^ 59
def prefixEnd_6076213 : Nat := 4983230072969 + 3 ^ 40 * 6076213 * 2
def baseEnd_6076213 : Nat := 346668647566415613599279

theorem tailTrace_6076213 : CollatzResearch.WordTrace tailWord_6076213 prefixEnd_6076213 346668647566415613599279 := by
  unfold tailWord_6076213
  simp only [CollatzResearch.WordTrace]
  refine ⟨221617694735925510407241293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147745129823950340271494195 221617694735925510407241293)
  ·
    refine ⟨83106635525972066402715485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221617694735925510407241293 83106635525972066402715485)
    ·
      refine ⟨31164988322239524901018307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83106635525972066402715485 31164988322239524901018307)
      ·
        refine ⟨46747482483359287351527461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31164988322239524901018307 46747482483359287351527461)
        ·
          refine ⟨8765152965629866378411399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46747482483359287351527461 8765152965629866378411399)
          ·
            refine ⟨13147729448444799567617099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765152965629866378411399 13147729448444799567617099)
            ·
              refine ⟨19721594172667199351425649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13147729448444799567617099 19721594172667199351425649)
              ·
                refine ⟨14791195629500399513569237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19721594172667199351425649 14791195629500399513569237)
                ·
                  refine ⟨346668647566415613599279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14791195629500399513569237 346668647566415613599279)
                  ·
                    rfl

theorem cell23_6076213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_6076213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076213 prefixEnd_6076213 := by exact prefixLift 6076213
  have htrace : WordTrace (prefixWord ++ tailWord_6076213) baseStart_6076213 baseEnd_6076213 := by
    simpa [prefixWord, tailWord_6076213, baseEnd_6076213] using wordTrace_append hprefix tailTrace_6076213
  have hstable : (prefixWord ++ tailWord_6076213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076213).length < 2 ^ (prefixWord ++ tailWord_6076213).sum := by decide
  have hdescent : baseEnd_6076213 < baseStart_6076213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076273 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_6076273 : Nat := 118140960795 + 6076273 * 2 ^ 59
def prefixEnd_6076273 : Nat := 4983230072969 + 3 ^ 40 * 6076273 * 2
def baseEnd_6076273 : Nat := 1040016212312336762547745

theorem tailTrace_6076273 : CollatzResearch.WordTrace tailWord_6076273 prefixEnd_6076273 1040016212312336762547745 := by
  unfold tailWord_6076273
  simp only [CollatzResearch.WordTrace]
  refine ⟨221619883115708140654425473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147746588743805427102950315 221619883115708140654425473)
  ·
    refine ⟨166214912336781105490819105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221619883115708140654425473 166214912336781105490819105)
    ·
      refine ⟨124661184252585829118114329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166214912336781105490819105 124661184252585829118114329)
      ·
        refine ⟨93495888189439371838585747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124661184252585829118114329 93495888189439371838585747)
        ·
          refine ⟨140243832284159057757878621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93495888189439371838585747 140243832284159057757878621)
          ·
            refine ⟨52591437106559646659204483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140243832284159057757878621 52591437106559646659204483)
            ·
              refine ⟨78887155659839469988806725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52591437106559646659204483 78887155659839469988806725)
              ·
                refine ⟨14791341686219900622901261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78887155659839469988806725 14791341686219900622901261)
                ·
                  refine ⟨5546753132332462733587973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14791341686219900622901261 5546753132332462733587973)
                  ·
                    refine ⟨1040016212312336762547745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546753132332462733587973 1040016212312336762547745)
                    ·
                      rfl

theorem cell23_6076273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_6076273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076273 prefixEnd_6076273 := by exact prefixLift 6076273
  have htrace : WordTrace (prefixWord ++ tailWord_6076273) baseStart_6076273 baseEnd_6076273 := by
    simpa [prefixWord, tailWord_6076273, baseEnd_6076273] using wordTrace_append hprefix tailTrace_6076273
  have hstable : (prefixWord ++ tailWord_6076273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076273).length < 2 ^ (prefixWord ++ tailWord_6076273).sum := by decide
  have hdescent : baseEnd_6076273 < baseStart_6076273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076283 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3]
def baseStart_6076283 : Nat := 118140960795 + 6076283 * 2 ^ 59
def prefixEnd_6076283 : Nat := 4983230072969 + 3 ^ 40 * 6076283 * 2
def baseEnd_6076283 : Nat := 3120053771743555248518189

theorem tailTrace_6076283 : CollatzResearch.WordTrace tailWord_6076283 prefixEnd_6076283 3120053771743555248518189 := by
  unfold tailWord_6076283
  simp only [CollatzResearch.WordTrace]
  refine ⟨221620247845671912362289503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147746831897114608241526335 221620247845671912362289503)
  ·
    refine ⟨332430371768507868543434255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221620247845671912362289503 332430371768507868543434255)
    ·
      refine ⟨498645557652761802815151383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332430371768507868543434255 498645557652761802815151383)
      ·
        refine ⟨747968336479142704222727075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498645557652761802815151383 747968336479142704222727075)
        ·
          refine ⟨1121952504718714056334090613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747968336479142704222727075 1121952504718714056334090613)
          ·
            refine ⟨105183047317379442781320995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1121952504718714056334090613 105183047317379442781320995)
            ·
              refine ⟨157774570976069164171981493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105183047317379442781320995 157774570976069164171981493)
              ·
                refine ⟨14791366029006484141123265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157774570976069164171981493 14791366029006484141123265)
                ·
                  refine ⟨11093524521754863105842449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14791366029006484141123265 11093524521754863105842449)
                  ·
                    refine ⟨8320143391316147329381837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11093524521754863105842449 8320143391316147329381837)
                    ·
                      refine ⟨3120053771743555248518189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320143391316147329381837 3120053771743555248518189)
                      ·
                        rfl

theorem cell23_6076283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].length) (baseStart_6076283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076283 prefixEnd_6076283 := by exact prefixLift 6076283
  have htrace : WordTrace (prefixWord ++ tailWord_6076283) baseStart_6076283 baseEnd_6076283 := by
    simpa [prefixWord, tailWord_6076283, baseEnd_6076283] using wordTrace_append hprefix tailTrace_6076283
  have hstable : (prefixWord ++ tailWord_6076283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076283).length < 2 ^ (prefixWord ++ tailWord_6076283).sum := by decide
  have hdescent : baseEnd_6076283 < baseStart_6076283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076364 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6076364 : Nat := 118140960795 + 6076364 * 2 ^ 59
def prefixEnd_6076364 : Nat := 4983230072969 + 3 ^ 40 * 6076364 * 2
def baseEnd_6076364 : Nat := 3120095363676569431605317

theorem tailTrace_6076364 : CollatzResearch.WordTrace tailWord_6076364 prefixEnd_6076364 3120095363676569431605317 := by
  unfold tailWord_6076364
  simp only [CollatzResearch.WordTrace]
  refine ⟨110811601079189231597994073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147748801438918975463992097 110811601079189231597994073)
  ·
    refine ⟨83108700809391923698495555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110811601079189231597994073 83108700809391923698495555)
    ·
      refine ⟨124663051214087885547743333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83108700809391923698495555 124663051214087885547743333)
      ·
        refine ⟨23374322102641478540201875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124663051214087885547743333 23374322102641478540201875)
        ·
          refine ⟨35061483153962217810302813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23374322102641478540201875 35061483153962217810302813)
          ·
            refine ⟨13148056182735831678863555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35061483153962217810302813 13148056182735831678863555)
            ·
              refine ⟨19722084274103747518295333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148056182735831678863555 19722084274103747518295333)
              ·
                refine ⟨3697890801394452659680375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19722084274103747518295333 3697890801394452659680375)
                ·
                  refine ⟨5546836202091678989520563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697890801394452659680375 5546836202091678989520563)
                  ·
                    refine ⟨8320254303137518484280845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546836202091678989520563 8320254303137518484280845)
                    ·
                      refine ⟨3120095363676569431605317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320254303137518484280845 3120095363676569431605317)
                      ·
                        rfl

theorem cell23_6076364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6076364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076364 prefixEnd_6076364 := by exact prefixLift 6076364
  have htrace : WordTrace (prefixWord ++ tailWord_6076364) baseStart_6076364 baseEnd_6076364 := by
    simpa [prefixWord, tailWord_6076364, baseEnd_6076364] using wordTrace_append hprefix tailTrace_6076364
  have hstable : (prefixWord ++ tailWord_6076364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076364).length < 2 ^ (prefixWord ++ tailWord_6076364).sum := by decide
  have hdescent : baseEnd_6076364 < baseStart_6076364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076387 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6076387 : Nat := 118140960795 + 6076387 * 2 ^ 59
def prefixEnd_6076387 : Nat := 4983230072969 + 3 ^ 40 * 6076387 * 2
def baseEnd_6076387 : Nat := 3120107173731622841617711

theorem tailTrace_6076387 : CollatzResearch.WordTrace tailWord_6076387 prefixEnd_6076387 3120107173731622841617711 := by
  unfold tailWord_6076387
  simp only [CollatzResearch.WordTrace]
  refine ⟨221624041037295138124075415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147749360691530092082716943 221624041037295138124075415)
  ·
    refine ⟨332436061555942707186113123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221624041037295138124075415 332436061555942707186113123)
    ·
      refine ⟨498654092333914060779169685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332436061555942707186113123 498654092333914060779169685)
      ·
        refine ⟨23374410578152221599023579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 498654092333914060779169685 23374410578152221599023579)
        ·
          refine ⟨35061615867228332398535369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23374410578152221599023579 35061615867228332398535369)
          ·
            refine ⟨26296211900421249298901527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35061615867228332398535369 26296211900421249298901527)
            ·
              refine ⟨39444317850631873948352291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26296211900421249298901527 39444317850631873948352291)
              ·
                refine ⟨59166476775947810922528437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39444317850631873948352291 59166476775947810922528437)
                ·
                  refine ⟨5546857197745107273987041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59166476775947810922528437 5546857197745107273987041)
                  ·
                    refine ⟨4160142898308830455490281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5546857197745107273987041 4160142898308830455490281)
                    ·
                      refine ⟨3120107173731622841617711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160142898308830455490281 3120107173731622841617711)
                      ·
                        rfl

theorem cell23_6076387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6076387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076387 prefixEnd_6076387 := by exact prefixLift 6076387
  have htrace : WordTrace (prefixWord ++ tailWord_6076387) baseStart_6076387 baseEnd_6076387 := by
    simpa [prefixWord, tailWord_6076387, baseEnd_6076387] using wordTrace_append hprefix tailTrace_6076387
  have hstable : (prefixWord ++ tailWord_6076387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076387).length < 2 ^ (prefixWord ++ tailWord_6076387).sum := by decide
  have hdescent : baseEnd_6076387 < baseStart_6076387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076391 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6076391 : Nat := 118140960795 + 6076391 * 2 ^ 59
def prefixEnd_6076391 : Nat := 4983230072969 + 3 ^ 40 * 6076391 * 2
def baseEnd_6076391 : Nat := 3120109227654240825967693

theorem tailTrace_6076391 : CollatzResearch.WordTrace tailWord_6076391 prefixEnd_6076391 3120109227654240825967693 := by
  unfold tailWord_6076391
  simp only [CollatzResearch.WordTrace]
  refine ⟨221624186929280646807221027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147749457952853764538147351 221624186929280646807221027)
  ·
    refine ⟨332436280393920970210831541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221624186929280646807221027 332436280393920970210831541)
    ·
      refine ⟨31165901286930090957265457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332436280393920970210831541 31165901286930090957265457)
      ·
        refine ⟨23374425965197568217949093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31165901286930090957265457 23374425965197568217949093)
        ·
          refine ⟨4382704868474544040865455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23374425965197568217949093 4382704868474544040865455)
          ·
            refine ⟨6574057302711816061298183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382704868474544040865455 6574057302711816061298183)
            ·
              refine ⟨9861085954067724091947275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574057302711816061298183 9861085954067724091947275)
              ·
                refine ⟨14791628931101586137920913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861085954067724091947275 14791628931101586137920913)
                ·
                  refine ⟨11093721698326189603440685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14791628931101586137920913 11093721698326189603440685)
                  ·
                    refine ⟨4160145636872321101290257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11093721698326189603440685 4160145636872321101290257)
                    ·
                      refine ⟨3120109227654240825967693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160145636872321101290257 3120109227654240825967693)
                      ·
                        rfl

theorem cell23_6076391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6076391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076391 prefixEnd_6076391 := by exact prefixLift 6076391
  have htrace : WordTrace (prefixWord ++ tailWord_6076391) baseStart_6076391 baseEnd_6076391 := by
    simpa [prefixWord, tailWord_6076391, baseEnd_6076391] using wordTrace_append hprefix tailTrace_6076391
  have hstable : (prefixWord ++ tailWord_6076391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076391).length < 2 ^ (prefixWord ++ tailWord_6076391).sum := by decide
  have hdescent : baseEnd_6076391 < baseStart_6076391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076414 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6076414 : Nat := 118140960795 + 6076414 * 2 ^ 59
def prefixEnd_6076414 : Nat := 4983230072969 + 3 ^ 40 * 6076414 * 2
def baseEnd_6076414 : Nat := 1040040345903098078660029

theorem tailTrace_6076414 : CollatzResearch.WordTrace tailWord_6076414 prefixEnd_6076414 1040040345903098078660029 := by
  unfold tailWord_6076414
  simp only [CollatzResearch.WordTrace]
  refine ⟨27703128226024665216913537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147750017205464881156872197 27703128226024665216913537)
  ·
    refine ⟨20777346169518498912685153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27703128226024665216913537 20777346169518498912685153)
    ·
      refine ⟨15583009627138874184513865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20777346169518498912685153 15583009627138874184513865)
      ·
        refine ⟨11687257220354155638385399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15583009627138874184513865 11687257220354155638385399)
        ·
          refine ⟨17530885830531233457578099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11687257220354155638385399 17530885830531233457578099)
          ·
            refine ⟨26296328745796850186367149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17530885830531233457578099 26296328745796850186367149)
            ·
              refine ⟨9861123279673818819887681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26296328745796850186367149 9861123279673818819887681)
              ·
                refine ⟨7395842459755364114915761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9861123279673818819887681 7395842459755364114915761)
                ·
                  refine ⟨5546881844816523086186821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395842459755364114915761 5546881844816523086186821)
                  ·
                    refine ⟨1040040345903098078660029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546881844816523086186821 1040040345903098078660029)
                    ·
                      rfl

theorem cell23_6076414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6076414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076414 prefixEnd_6076414 := by exact prefixLift 6076414
  have htrace : WordTrace (prefixWord ++ tailWord_6076414) baseStart_6076414 baseEnd_6076414 := by
    simpa [prefixWord, tailWord_6076414, baseEnd_6076414] using wordTrace_append hprefix tailTrace_6076414
  have hstable : (prefixWord ++ tailWord_6076414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076414).length < 2 ^ (prefixWord ++ tailWord_6076414).sum := by decide
  have hdescent : baseEnd_6076414 < baseStart_6076414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076455 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6076455 : Nat := 118140960795 + 6076455 * 2 ^ 59
def prefixEnd_6076455 : Nat := 4983230072969 + 3 ^ 40 * 6076455 * 2
def baseEnd_6076455 : Nat := 3120142090416128575567399

theorem tailTrace_6076455 : CollatzResearch.WordTrace tailWord_6076455 prefixEnd_6076455 3120142090416128575567399 := by
  unfold tailWord_6076455
  simp only [CollatzResearch.WordTrace]
  refine ⟨221626521201048785737550819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147751014134032523825033879 221626521201048785737550819)
  ·
    refine ⟨332439781801573178606326229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221626521201048785737550819 332439781801573178606326229)
    ·
      refine ⟨7791557385974371373585771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 332439781801573178606326229 7791557385974371373585771)
      ·
        refine ⟨11687336078961557060378657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791557385974371373585771 11687336078961557060378657)
        ·
          refine ⟨8765502059221167795283993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11687336078961557060378657 8765502059221167795283993)
          ·
            refine ⟨6574126544415875846462995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765502059221167795283993 6574126544415875846462995)
            ·
              refine ⟨9861189816623813769694493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574126544415875846462995 9861189816623813769694493)
              ·
                refine ⟨3697946181233930163635435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9861189816623813769694493 3697946181233930163635435)
                ·
                  refine ⟨5546919271850895245453153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697946181233930163635435 5546919271850895245453153)
                  ·
                    refine ⟨4160189453888171434089865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5546919271850895245453153 4160189453888171434089865)
                    ·
                      refine ⟨3120142090416128575567399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160189453888171434089865 3120142090416128575567399)
                      ·
                        rfl

theorem cell23_6076455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6076455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076455 prefixEnd_6076455 := by exact prefixLift 6076455
  have htrace : WordTrace (prefixWord ++ tailWord_6076455) baseStart_6076455 baseEnd_6076455 := by
    simpa [prefixWord, tailWord_6076455, baseEnd_6076455] using wordTrace_append hprefix tailTrace_6076455
  have hstable : (prefixWord ++ tailWord_6076455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076455).length < 2 ^ (prefixWord ++ tailWord_6076455).sum := by decide
  have hdescent : baseEnd_6076455 < baseStart_6076455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076483 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 7]
def baseStart_6076483 : Nat := 118140960795 + 6076483 * 2 ^ 59
def prefixEnd_6076483 : Nat := 4983230072969 + 3 ^ 40 * 6076483 * 2
def baseEnd_6076483 : Nat := 346684051986050496224141

theorem tailTrace_6076483 : CollatzResearch.WordTrace tailWord_6076483 prefixEnd_6076483 346684051986050496224141 := by
  unfold tailWord_6076483
  simp only [CollatzResearch.WordTrace]
  refine ⟨221627542444947346519570103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147751694963298231013046735 221627542444947346519570103)
  ·
    refine ⟨332441313667421019779355155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221627542444947346519570103 332441313667421019779355155)
    ·
      refine ⟨498661970501131529669032733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332441313667421019779355155 498661970501131529669032733)
      ·
        refine ⟨186998238937924323625887275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498661970501131529669032733 186998238937924323625887275)
        ·
          refine ⟨280497358406886485438830913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186998238937924323625887275 280497358406886485438830913)
          ·
            refine ⟨210373018805164864079123185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280497358406886485438830913 210373018805164864079123185)
            ·
              refine ⟨157779764103873648059342389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210373018805164864079123185 157779764103873648059342389)
              ·
                refine ⟨14791852884738154505563349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157779764103873648059342389 14791852884738154505563349)
                ·
                  refine ⟨346684051986050496224141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14791852884738154505563349 346684051986050496224141)
                  ·
                    rfl

theorem cell23_6076483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 7].length) (baseStart_6076483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076483 prefixEnd_6076483 := by exact prefixLift 6076483
  have htrace : WordTrace (prefixWord ++ tailWord_6076483) baseStart_6076483 baseEnd_6076483 := by
    simpa [prefixWord, tailWord_6076483, baseEnd_6076483] using wordTrace_append hprefix tailTrace_6076483
  have hstable : (prefixWord ++ tailWord_6076483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076483).length < 2 ^ (prefixWord ++ tailWord_6076483).sum := by decide
  have hdescent : baseEnd_6076483 < baseStart_6076483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076498 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_6076498 : Nat := 118140960795 + 6076498 * 2 ^ 59
def prefixEnd_6076498 : Nat := 4983230072969 + 3 ^ 40 * 6076498 * 2
def baseEnd_6076498 : Nat := 3120164170084271907329701

theorem tailTrace_6076498 : CollatzResearch.WordTrace tailWord_6076498 prefixEnd_6076498 3120164170084271907329701 := by
  unfold tailWord_6076498
  simp only [CollatzResearch.WordTrace]
  refine ⟨55407022384973251020341537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147752059693262002720910765 55407022384973251020341537)
  ·
    refine ⟨41555266788729938265256153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55407022384973251020341537 41555266788729938265256153)
    ·
      refine ⟨31166450091547453698942115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41555266788729938265256153 31166450091547453698942115)
      ·
        refine ⟨46749675137321180548413173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31166450091547453698942115 46749675137321180548413173)
        ·
          refine ⟨4382782044123860676413735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46749675137321180548413173 4382782044123860676413735)
          ·
            refine ⟨6574173066185791014620603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382782044123860676413735 6574173066185791014620603)
            ·
              refine ⟨9861259599278686521930905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574173066185791014620603 9861259599278686521930905)
              ·
                refine ⟨7395944699459014891448179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9861259599278686521930905 7395944699459014891448179)
                ·
                  refine ⟨11093917049188522337172269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395944699459014891448179 11093917049188522337172269)
                  ·
                    refine ⟨4160218893445695876439601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11093917049188522337172269 4160218893445695876439601)
                    ·
                      refine ⟨3120164170084271907329701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160218893445695876439601 3120164170084271907329701)
                      ·
                        rfl

theorem cell23_6076498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_6076498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076498 prefixEnd_6076498 := by exact prefixLift 6076498
  have htrace : WordTrace (prefixWord ++ tailWord_6076498) baseStart_6076498 baseEnd_6076498 := by
    simpa [prefixWord, tailWord_6076498, baseEnd_6076498] using wordTrace_append hprefix tailTrace_6076498
  have hstable : (prefixWord ++ tailWord_6076498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076498).length < 2 ^ (prefixWord ++ tailWord_6076498).sum := by decide
  have hdescent : baseEnd_6076498 < baseStart_6076498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076534 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6076534 : Nat := 118140960795 + 6076534 * 2 ^ 59
def prefixEnd_6076534 : Nat := 4983230072969 + 3 ^ 40 * 6076534 * 2
def baseEnd_6076534 : Nat := 346686961709759307386615

theorem tailTrace_6076534 : CollatzResearch.WordTrace tailWord_6076534 prefixEnd_6076534 346686961709759307386615 := by
  unfold tailWord_6076534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851837660485161389354791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147752935045175054819784437 13851837660485161389354791)
  ·
    refine ⟨20777756490727742084032187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13851837660485161389354791 20777756490727742084032187)
    ·
      refine ⟨31166634736091613126048281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20777756490727742084032187 31166634736091613126048281)
      ·
        refine ⟨23374976052068709844536211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31166634736091613126048281 23374976052068709844536211)
        ·
          refine ⟨35062464078103064766804317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23374976052068709844536211 35062464078103064766804317)
          ·
            refine ⟨13148424029288649287551619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35062464078103064766804317 13148424029288649287551619)
            ·
              refine ⟨19722636043932973931327429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148424029288649287551619 19722636043932973931327429)
              ·
                refine ⟨3697994258237432612123893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19722636043932973931327429 3697994258237432612123893)
                ·
                  refine ⟨346686961709759307386615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697994258237432612123893 346686961709759307386615)
                  ·
                    rfl

theorem cell23_6076534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6076534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076534 prefixEnd_6076534 := by exact prefixLift 6076534
  have htrace : WordTrace (prefixWord ++ tailWord_6076534) baseStart_6076534 baseEnd_6076534 := by
    simpa [prefixWord, tailWord_6076534, baseEnd_6076534] using wordTrace_append hprefix tailTrace_6076534
  have hstable : (prefixWord ++ tailWord_6076534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076534).length < 2 ^ (prefixWord ++ tailWord_6076534).sum := by decide
  have hdescent : baseEnd_6076534 < baseStart_6076534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076537 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 5, 2]
def baseStart_6076537 : Nat := 118140960795 + 6076537 * 2 ^ 59
def prefixEnd_6076537 : Nat := 4983230072969 + 3 ^ 40 * 6076537 * 2
def baseEnd_6076537 : Nat := 3120184195829797254742021

theorem tailTrace_6076537 : CollatzResearch.WordTrace tailWord_6076537 prefixEnd_6076537 3120184195829797254742021 := by
  unfold tailWord_6076537
  simp only [CollatzResearch.WordTrace]
  refine ⟨221629511986751713742035865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147753007991167809161357243 221629511986751713742035865)
  ·
    refine ⟨166222133990063785306526899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221629511986751713742035865 166222133990063785306526899)
    ·
      refine ⟨249333200985095677959790349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166222133990063785306526899 249333200985095677959790349)
      ·
        refine ⟨93499950369410879234921381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249333200985095677959790349 93499950369410879234921381)
        ·
          refine ⟨17531240694264539856547759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93499950369410879234921381 17531240694264539856547759)
          ·
            refine ⟨26296861041396809784821639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17531240694264539856547759 26296861041396809784821639)
            ·
              refine ⟨39445291562095214677232459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26296861041396809784821639 39445291562095214677232459)
              ·
                refine ⟨59167937343142822015848689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39445291562095214677232459 59167937343142822015848689)
                ·
                  refine ⟨44375953007357116511886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59167937343142822015848689 44375953007357116511886517)
                  ·
                    refine ⟨4160245594439729672989361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44375953007357116511886517 4160245594439729672989361)
                    ·
                      refine ⟨3120184195829797254742021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160245594439729672989361 3120184195829797254742021)
                      ·
                        rfl

theorem cell23_6076537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_6076537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076537 prefixEnd_6076537 := by exact prefixLift 6076537
  have htrace : WordTrace (prefixWord ++ tailWord_6076537) baseStart_6076537 baseEnd_6076537 := by
    simpa [prefixWord, tailWord_6076537, baseEnd_6076537] using wordTrace_append hprefix tailTrace_6076537
  have hstable : (prefixWord ++ tailWord_6076537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076537).length < 2 ^ (prefixWord ++ tailWord_6076537).sum := by decide
  have hdescent : baseEnd_6076537 < baseStart_6076537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076540 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_6076540 : Nat := 118140960795 + 6076540 * 2 ^ 59
def prefixEnd_6076540 : Nat := 4983230072969 + 3 ^ 40 * 6076540 * 2
def baseEnd_6076540 : Nat := 3120185736271760743004507

theorem tailTrace_6076540 : CollatzResearch.WordTrace tailWord_6076540 prefixEnd_6076540 3120185736271760743004507 := by
  unfold tailWord_6076540
  simp only [CollatzResearch.WordTrace]
  refine ⟨110814810702870422627197537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147753080937160563502930049 110814810702870422627197537)
  ·
    refine ⟨83111108027152816970398153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110814810702870422627197537 83111108027152816970398153)
    ·
      refine ⟨62333331020364612727798615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83111108027152816970398153 62333331020364612727798615)
      ·
        refine ⟨93499996530546919091697923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62333331020364612727798615 93499996530546919091697923)
        ·
          refine ⟨140249994795820378637546885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93499996530546919091697923 140249994795820378637546885)
          ·
            refine ⟨26296874024216320994540041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140249994795820378637546885 26296874024216320994540041)
            ·
              refine ⟨19722655518162240745905031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26296874024216320994540041 19722655518162240745905031)
              ·
                refine ⟨29583983277243361118857547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19722655518162240745905031 29583983277243361118857547)
                ·
                  refine ⟨44375974915865041678286321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29583983277243361118857547 44375974915865041678286321)
                  ·
                    refine ⟨33281981186898781258714741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44375974915865041678286321 33281981186898781258714741)
                    ·
                      refine ⟨3120185736271760743004507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33281981186898781258714741 3120185736271760743004507)
                      ·
                        rfl

theorem cell23_6076540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_6076540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076540 prefixEnd_6076540 := by exact prefixLift 6076540
  have htrace : WordTrace (prefixWord ++ tailWord_6076540) baseStart_6076540 baseEnd_6076540 := by
    simpa [prefixWord, tailWord_6076540, baseEnd_6076540] using wordTrace_append hprefix tailTrace_6076540
  have hstable : (prefixWord ++ tailWord_6076540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076540).length < 2 ^ (prefixWord ++ tailWord_6076540).sum := by decide
  have hdescent : baseEnd_6076540 < baseStart_6076540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076564 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6076564 : Nat := 118140960795 + 6076564 * 2 ^ 59
def prefixEnd_6076564 : Nat := 4983230072969 + 3 ^ 40 * 6076564 * 2
def baseEnd_6076564 : Nat := 1040066019935822883034799

theorem tailTrace_6076564 : CollatzResearch.WordTrace tailWord_6076564 prefixEnd_6076564 1040066019935822883034799 := by
  unfold tailWord_6076564
  simp only [CollatzResearch.WordTrace]
  refine ⟨110815248378826948676634373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147753664505102598235512497 110815248378826948676634373)
  ·
    refine ⟨20777859071030052876868945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110815248378826948676634373 20777859071030052876868945)
    ·
      refine ⟨15583394303272539657651709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20777859071030052876868945 15583394303272539657651709)
      ·
        refine ⟨5843772863727202371619391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15583394303272539657651709 5843772863727202371619391)
        ·
          refine ⟨8765659295590803557429087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843772863727202371619391 8765659295590803557429087)
          ·
            refine ⟨13148488943386205336143631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765659295590803557429087 13148488943386205336143631)
            ·
              refine ⟨19722733415079308004215447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148488943386205336143631 19722733415079308004215447)
              ·
                refine ⟨29584100122618962006323171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19722733415079308004215447 29584100122618962006323171)
                ·
                  refine ⟨44376150183928443009484757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29584100122618962006323171 44376150183928443009484757)
                  ·
                    refine ⟨1040066019935822883034799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44376150183928443009484757 1040066019935822883034799)
                    ·
                      rfl

theorem cell23_6076564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6076564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076564 prefixEnd_6076564 := by exact prefixLift 6076564
  have htrace : WordTrace (prefixWord ++ tailWord_6076564) baseStart_6076564 baseEnd_6076564 := by
    simpa [prefixWord, tailWord_6076564, baseEnd_6076564] using wordTrace_append hprefix tailTrace_6076564
  have hstable : (prefixWord ++ tailWord_6076564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076564).length < 2 ^ (prefixWord ++ tailWord_6076564).sum := by decide
  have hdescent : baseEnd_6076564 < baseStart_6076564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076566 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6076566 : Nat := 118140960795 + 6076566 * 2 ^ 59
def prefixEnd_6076566 : Nat := 4983230072969 + 3 ^ 40 * 6076566 * 2
def baseEnd_6076566 : Nat := 3120199086768777641279389

theorem tailTrace_6076566 : CollatzResearch.WordTrace tailWord_6076566 prefixEnd_6076566 3120199086768777641279389 := by
  unfold tailWord_6076566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851910606477915730927597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147753713135764434463227701 13851910606477915730927597)
  ·
    refine ⟨5194466477429218399097849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13851910606477915730927597 5194466477429218399097849)
    ·
      refine ⟨3895849858071913799323387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5194466477429218399097849 3895849858071913799323387)
      ·
        refine ⟨5843774787107870698985081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895849858071913799323387 5843774787107870698985081)
        ·
          refine ⟨4382831090330903024238811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5843774787107870698985081 4382831090330903024238811)
          ·
            refine ⟨6574246635496354536358217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382831090330903024238811 6574246635496354536358217)
            ·
              refine ⟨4930684976622265902268663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574246635496354536358217 4930684976622265902268663)
              ·
                refine ⟨7396027464933398853402995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930684976622265902268663 7396027464933398853402995)
                ·
                  refine ⟨11094041197400098280104493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7396027464933398853402995 11094041197400098280104493)
                  ·
                    refine ⟨4160265449025036855039185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11094041197400098280104493 4160265449025036855039185)
                    ·
                      refine ⟨3120199086768777641279389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160265449025036855039185 3120199086768777641279389)
                      ·
                        rfl

theorem cell23_6076566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6076566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076566 prefixEnd_6076566 := by exact prefixLift 6076566
  have htrace : WordTrace (prefixWord ++ tailWord_6076566) baseStart_6076566 baseEnd_6076566 := by
    simpa [prefixWord, tailWord_6076566, baseEnd_6076566] using wordTrace_append hprefix tailTrace_6076566
  have hstable : (prefixWord ++ tailWord_6076566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076566).length < 2 ^ (prefixWord ++ tailWord_6076566).sum := by decide
  have hdescent : baseEnd_6076566 < baseStart_6076566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076567 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_6076567 : Nat := 118140960795 + 6076567 * 2 ^ 59
def prefixEnd_6076567 : Nat := 4983230072969 + 3 ^ 40 * 6076567 * 2
def baseEnd_6076567 : Nat := 3120199600249432137366883

theorem tailTrace_6076567 : CollatzResearch.WordTrace tailWord_6076567 prefixEnd_6076567 3120199600249432137366883 := by
  unfold tailWord_6076567
  simp only [CollatzResearch.WordTrace]
  refine ⟨221630606176643028865627955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147753737451095352577085303 221630606176643028865627955)
  ·
    refine ⟨332445909264964543298441933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221630606176643028865627955 332445909264964543298441933)
    ·
      refine ⟨124667215974361703736915725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332445909264964543298441933 124667215974361703736915725)
      ·
        refine ⟨46750205990385638901343397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124667215974361703736915725 46750205990385638901343397)
        ·
          refine ⟨8765663623197307294001887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46750205990385638901343397 8765663623197307294001887)
          ·
            refine ⟨13148495434795960941002831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765663623197307294001887 13148495434795960941002831)
            ·
              refine ⟨19722743152193941411504247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148495434795960941002831 19722743152193941411504247)
              ·
                refine ⟨29584114728290912117256371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19722743152193941411504247 29584114728290912117256371)
                ·
                  refine ⟨44376172092436368175884557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29584114728290912117256371 44376172092436368175884557)
                  ·
                    refine ⟨16641064534663638065956709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44376172092436368175884557 16641064534663638065956709)
                    ·
                      refine ⟨3120199600249432137366883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16641064534663638065956709 3120199600249432137366883)
                      ·
                        rfl

theorem cell23_6076567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_6076567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076567 prefixEnd_6076567 := by exact prefixLift 6076567
  have htrace : WordTrace (prefixWord ++ tailWord_6076567) baseStart_6076567 baseEnd_6076567 := by
    simpa [prefixWord, tailWord_6076567, baseEnd_6076567] using wordTrace_append hprefix tailTrace_6076567
  have hstable : (prefixWord ++ tailWord_6076567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076567).length < 2 ^ (prefixWord ++ tailWord_6076567).sum := by decide
  have hdescent : baseEnd_6076567 < baseStart_6076567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076594 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_6076594 : Nat := 118140960795 + 6076594 * 2 ^ 59
def prefixEnd_6076594 : Nat := 4983230072969 + 3 ^ 40 * 6076594 * 2
def baseEnd_6076594 : Nat := 1040071154742367843909753

theorem tailTrace_6076594 : CollatzResearch.WordTrace tailWord_6076594 prefixEnd_6076594 1040071154742367843909753 := by
  unfold tailWord_6076594
  simp only [CollatzResearch.WordTrace]
  refine ⟨55407897736886303119215209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147754393965030141651240557 55407897736886303119215209)
  ·
    refine ⟨41555923302664727339411407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55407897736886303119215209 41555923302664727339411407)
    ·
      refine ⟨62333884953997091009117111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41555923302664727339411407 62333884953997091009117111)
      ·
        refine ⟨93500827430995636513675667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62333884953997091009117111 93500827430995636513675667)
        ·
          refine ⟨140251241146493454770513501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93500827430995636513675667 140251241146493454770513501)
          ·
            refine ⟨52594215429935045538942563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140251241146493454770513501 52594215429935045538942563)
            ·
              refine ⟨78891323144902568308413845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52594215429935045538942563 78891323144902568308413845)
              ·
                refine ⟨3698030772417307889456899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78891323144902568308413845 3698030772417307889456899)
                ·
                  refine ⟨5547046158625961834185349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698030772417307889456899 5547046158625961834185349)
                  ·
                    refine ⟨1040071154742367843909753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547046158625961834185349 1040071154742367843909753)
                    ·
                      rfl

theorem cell23_6076594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_6076594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076594 prefixEnd_6076594 := by exact prefixLift 6076594
  have htrace : WordTrace (prefixWord ++ tailWord_6076594) baseStart_6076594 baseEnd_6076594 := by
    simpa [prefixWord, tailWord_6076594, baseEnd_6076594] using wordTrace_append hprefix tailTrace_6076594
  have hstable : (prefixWord ++ tailWord_6076594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076594).length < 2 ^ (prefixWord ++ tailWord_6076594).sum := by decide
  have hdescent : baseEnd_6076594 < baseStart_6076594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076617 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_6076617 : Nat := 118140960795 + 6076617 * 2 ^ 59
def prefixEnd_6076617 : Nat := 4983230072969 + 3 ^ 40 * 6076617 * 2
def baseEnd_6076617 : Nat := 3120225274282156941741653

theorem tailTrace_6076617 : CollatzResearch.WordTrace tailWord_6076617 prefixEnd_6076617 3120225274282156941741653 := by
  unfold tailWord_6076617
  simp only [CollatzResearch.WordTrace]
  refine ⟨221632429826461887404948105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147754953217641258269965403 221632429826461887404948105)
  ·
    refine ⟨166224322369846415553711079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221632429826461887404948105 166224322369846415553711079)
    ·
      refine ⟨249336483554769623330566619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166224322369846415553711079 249336483554769623330566619)
      ·
        refine ⟨374004725332154434995849929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249336483554769623330566619 374004725332154434995849929)
        ·
          refine ⟨280503543999115826246887447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374004725332154434995849929 280503543999115826246887447)
          ·
            refine ⟨420755315998673739370331171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280503543999115826246887447 420755315998673739370331171)
            ·
              refine ⟨631132973998010609055496757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420755315998673739370331171 631132973998010609055496757)
              ·
                refine ⟨59168716312313494598952821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 631132973998010609055496757 59168716312313494598952821)
                ·
                  refine ⟨5547067154279390118651827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59168716312313494598952821 5547067154279390118651827)
                  ·
                    refine ⟨8320600731419085177977741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547067154279390118651827 8320600731419085177977741)
                    ·
                      refine ⟨3120225274282156941741653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320600731419085177977741 3120225274282156941741653)
                      ·
                        rfl

theorem cell23_6076617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_6076617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076617 prefixEnd_6076617 := by exact prefixLift 6076617
  have htrace : WordTrace (prefixWord ++ tailWord_6076617) baseStart_6076617 baseEnd_6076617 := by
    simpa [prefixWord, tailWord_6076617, baseEnd_6076617] using wordTrace_append hprefix tailTrace_6076617
  have hstable : (prefixWord ++ tailWord_6076617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076617).length < 2 ^ (prefixWord ++ tailWord_6076617).sum := by decide
  have hdescent : baseEnd_6076617 < baseStart_6076617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076702 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6076702 : Nat := 118140960795 + 6076702 * 2 ^ 59
def prefixEnd_6076702 : Nat := 4983230072969 + 3 ^ 40 * 6076702 * 2
def baseEnd_6076702 : Nat := 3120268920137789109178763

theorem tailTrace_6076702 : CollatzResearch.WordTrace tailWord_6076702 prefixEnd_6076702 3120268920137789109178763 := by
  unfold tailWord_6076702
  simp only [CollatzResearch.WordTrace]
  refine ⟨27704441253894243365224045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147757020020769297947861573 27704441253894243365224045)
  ·
    refine ⟨10389165470210341261959017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27704441253894243365224045 10389165470210341261959017)
    ·
      refine ⟨7791874102657755946469263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10389165470210341261959017 7791874102657755946469263)
      ·
        refine ⟨11687811153986633919703895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791874102657755946469263 11687811153986633919703895)
        ·
          refine ⟨17531716730979950879555843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11687811153986633919703895 17531716730979950879555843)
          ·
            refine ⟨26297575096469926319333765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17531716730979950879555843 26297575096469926319333765)
            ·
              refine ⟨4930795330588111184875081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26297575096469926319333765 4930795330588111184875081)
              ·
                refine ⟨3698096497941083388656311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4930795330588111184875081 3698096497941083388656311)
                ·
                  refine ⟨5547144746911625082984467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698096497941083388656311 5547144746911625082984467)
                  ·
                    refine ⟨8320717120367437624476701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547144746911625082984467 8320717120367437624476701)
                    ·
                      refine ⟨3120268920137789109178763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320717120367437624476701 3120268920137789109178763)
                      ·
                        rfl

theorem cell23_6076702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6076702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076702 prefixEnd_6076702 := by exact prefixLift 6076702
  have htrace : WordTrace (prefixWord ++ tailWord_6076702) baseStart_6076702 baseEnd_6076702 := by
    simpa [prefixWord, tailWord_6076702, baseEnd_6076702] using wordTrace_append hprefix tailTrace_6076702
  have hstable : (prefixWord ++ tailWord_6076702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076702).length < 2 ^ (prefixWord ++ tailWord_6076702).sum := by decide
  have hdescent : baseEnd_6076702 < baseStart_6076702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076707 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3]
def baseStart_6076707 : Nat := 118140960795 + 6076707 * 2 ^ 59
def prefixEnd_6076707 : Nat := 4983230072969 + 3 ^ 40 * 6076707 * 2
def baseEnd_6076707 : Nat := 3120271487541061589616239

theorem tailTrace_6076707 : CollatzResearch.WordTrace tailWord_6076707 prefixEnd_6076707 3120271487541061589616239 := by
  unfold tailWord_6076707
  simp only [CollatzResearch.WordTrace]
  refine ⟨221635712396135832775724375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147757141597423888517149583 221635712396135832775724375)
  ·
    refine ⟨332453568594203749163586563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221635712396135832775724375 332453568594203749163586563)
    ·
      refine ⟨498680352891305623745379845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332453568594203749163586563 498680352891305623745379845)
      ·
        refine ⟨93502566167119804452258721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498680352891305623745379845 93502566167119804452258721)
        ·
          refine ⟨70126924625339853339194041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93502566167119804452258721 70126924625339853339194041)
          ·
            refine ⟨52595193469004890004395531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70126924625339853339194041 52595193469004890004395531)
            ·
              refine ⟨78892790203507335006593297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52595193469004890004395531 78892790203507335006593297)
              ·
                refine ⟨59169592652630501254944973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78892790203507335006593297 59169592652630501254944973)
                ·
                  refine ⟨22188597244736437970604365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59169592652630501254944973 22188597244736437970604365)
                  ·
                    refine ⟨8320723966776164238976637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22188597244736437970604365 8320723966776164238976637)
                    ·
                      refine ⟨3120271487541061589616239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320723966776164238976637 3120271487541061589616239)
                      ·
                        rfl

theorem cell23_6076707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_6076707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076707 prefixEnd_6076707 := by exact prefixLift 6076707
  have htrace : WordTrace (prefixWord ++ tailWord_6076707) baseStart_6076707 baseEnd_6076707 := by
    simpa [prefixWord, tailWord_6076707, baseEnd_6076707] using wordTrace_append hprefix tailTrace_6076707
  have hstable : (prefixWord ++ tailWord_6076707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076707).length < 2 ^ (prefixWord ++ tailWord_6076707).sum := by decide
  have hdescent : baseEnd_6076707 < baseStart_6076707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076767 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_6076767 : Nat := 118140960795 + 6076767 * 2 ^ 59
def prefixEnd_6076767 : Nat := 4983230072969 + 3 ^ 40 * 6076767 * 2
def baseEnd_6076767 : Nat := 3120302296380331354865963

theorem tailTrace_6076767 : CollatzResearch.WordTrace tailWord_6076767 prefixEnd_6076767 3120302296380331354865963 := by
  unfold tailWord_6076767
  simp only [CollatzResearch.WordTrace]
  refine ⟨221637900775918463022908555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147758600517278975348605703 221637900775918463022908555)
  ·
    refine ⟨332456851163877694534362833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221637900775918463022908555 332456851163877694534362833)
    ·
      refine ⟨249342638372908270900772125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332456851163877694534362833 249342638372908270900772125)
      ·
        refine ⟨93503489389840601587789547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249342638372908270900772125 93503489389840601587789547)
        ·
          refine ⟨140255234084760902381684321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93503489389840601587789547 140255234084760902381684321)
          ·
            refine ⟨105191425563570676786263241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140255234084760902381684321 105191425563570676786263241)
            ·
              refine ⟨78893569172678007589697431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105191425563570676786263241 78893569172678007589697431)
              ·
                refine ⟨118340353759017011384546147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78893569172678007589697431 118340353759017011384546147)
                ·
                  refine ⟨177510530638525517076819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118340353759017011384546147 177510530638525517076819221)
                  ·
                    refine ⟨8320806123680883612975901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177510530638525517076819221 8320806123680883612975901)
                    ·
                      refine ⟨3120302296380331354865963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8320806123680883612975901 3120302296380331354865963)
                      ·
                        rfl

theorem cell23_6076767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_6076767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076767 prefixEnd_6076767 := by exact prefixLift 6076767
  have htrace : WordTrace (prefixWord ++ tailWord_6076767) baseStart_6076767 baseEnd_6076767 := by
    simpa [prefixWord, tailWord_6076767, baseEnd_6076767] using wordTrace_append hprefix tailTrace_6076767
  have hstable : (prefixWord ++ tailWord_6076767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076767).length < 2 ^ (prefixWord ++ tailWord_6076767).sum := by decide
  have hdescent : baseEnd_6076767 < baseStart_6076767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076777 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_6076777 : Nat := 118140960795 + 6076777 * 2 ^ 59
def prefixEnd_6076777 : Nat := 4983230072969 + 3 ^ 40 * 6076777 * 2
def baseEnd_6076777 : Nat := 3120307431186876315740917

theorem tailTrace_6076777 : CollatzResearch.WordTrace tailWord_6076777 prefixEnd_6076777 3120307431186876315740917 := by
  unfold tailWord_6076777
  simp only [CollatzResearch.WordTrace]
  refine ⟨221638265505882234730772585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147758843670588156487181723 221638265505882234730772585)
  ·
    refine ⟨166228699129411676048079439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221638265505882234730772585 166228699129411676048079439)
    ·
      refine ⟨249343048694117514072119159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166228699129411676048079439 249343048694117514072119159)
      ·
        refine ⟨374014573041176271108178739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249343048694117514072119159 374014573041176271108178739)
        ·
          refine ⟨561021859561764406662268109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374014573041176271108178739 561021859561764406662268109)
          ·
            refine ⟨210383197335661652498350541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561021859561764406662268109 210383197335661652498350541)
            ·
              refine ⟨78893699000873119686881453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210383197335661652498350541 78893699000873119686881453)
              ·
                refine ⟨29585137125327419882580545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78893699000873119686881453 29585137125327419882580545)
                ·
                  refine ⟨22188852843995564911935409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29585137125327419882580545 22188852843995564911935409)
                  ·
                    refine ⟨16641639632996673683951557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22188852843995564911935409 16641639632996673683951557)
                    ·
                      refine ⟨3120307431186876315740917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16641639632996673683951557 3120307431186876315740917)
                      ·
                        rfl

theorem cell23_6076777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_6076777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076777 prefixEnd_6076777 := by exact prefixLift 6076777
  have htrace : WordTrace (prefixWord ++ tailWord_6076777) baseStart_6076777 baseEnd_6076777 := by
    simpa [prefixWord, tailWord_6076777, baseEnd_6076777] using wordTrace_append hprefix tailTrace_6076777
  have hstable : (prefixWord ++ tailWord_6076777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076777).length < 2 ^ (prefixWord ++ tailWord_6076777).sum := by decide
  have hdescent : baseEnd_6076777 < baseStart_6076777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076834 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6076834 : Nat := 118140960795 + 6076834 * 2 ^ 59
def prefixEnd_6076834 : Nat := 4983230072969 + 3 ^ 40 * 6076834 * 2
def baseEnd_6076834 : Nat := 1040112233194727530909385

theorem tailTrace_6076834 : CollatzResearch.WordTrace tailWord_6076834 prefixEnd_6076834 1040112233194727530909385 := by
  unfold tailWord_6076834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55410086116668933366399389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147760229644450488977065037 55410086116668933366399389)
  ·
    refine ⟨20778782293750850012399771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55410086116668933366399389 20778782293750850012399771)
    ·
      refine ⟨31168173440626275018599657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20778782293750850012399771 31168173440626275018599657)
      ·
        refine ⟨23376130080469706263949743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31168173440626275018599657 23376130080469706263949743)
        ·
          refine ⟨35064195120704559395924615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23376130080469706263949743 35064195120704559395924615)
          ·
            refine ⟨52596292681056839093886923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35064195120704559395924615 52596292681056839093886923)
            ·
              refine ⟨78894439021585258640830385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52596292681056839093886923 78894439021585258640830385)
              ·
                refine ⟨59170829266188943980622789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78894439021585258640830385 59170829266188943980622789)
                ·
                  refine ⟨11094530487410426996366773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59170829266188943980622789 11094530487410426996366773)
                  ·
                    refine ⟨1040112233194727530909385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11094530487410426996366773 1040112233194727530909385)
                    ·
                      rfl

theorem cell23_6076834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6076834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076834 prefixEnd_6076834 := by exact prefixLift 6076834
  have htrace : WordTrace (prefixWord ++ tailWord_6076834) baseStart_6076834 baseEnd_6076834 := by
    simpa [prefixWord, tailWord_6076834, baseEnd_6076834] using wordTrace_append hprefix tailTrace_6076834
  have hstable : (prefixWord ++ tailWord_6076834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076834).length < 2 ^ (prefixWord ++ tailWord_6076834).sum := by decide
  have hdescent : baseEnd_6076834 < baseStart_6076834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076867 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_6076867 : Nat := 118140960795 + 6076867 * 2 ^ 59
def prefixEnd_6076867 : Nat := 4983230072969 + 3 ^ 40 * 6076867 * 2
def baseEnd_6076867 : Nat := 3120353644445780963615503

theorem tailTrace_6076867 : CollatzResearch.WordTrace tailWord_6076867 prefixEnd_6076867 3120353644445780963615503 := by
  unfold tailWord_6076867
  simp only [CollatzResearch.WordTrace]
  refine ⟨221641548075556180101548855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147761032050370786734365903 221641548075556180101548855)
  ·
    refine ⟨332462322113334270152323283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221641548075556180101548855 332462322113334270152323283)
    ·
      refine ⟨498693483170001405228484925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332462322113334270152323283 498693483170001405228484925)
      ·
        refine ⟨187010056188750526960681847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498693483170001405228484925 187010056188750526960681847)
        ·
          refine ⟨280515084283125790441022771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187010056188750526960681847 280515084283125790441022771)
          ·
            refine ⟨420772626424688685661534157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280515084283125790441022771 420772626424688685661534157)
            ·
              refine ⟨157789734909258257123075309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420772626424688685661534157 157789734909258257123075309)
              ·
                refine ⟨59171150590971846421153241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157789734909258257123075309 59171150590971846421153241)
                ·
                  refine ⟨44378362943228884815864931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59171150590971846421153241 44378362943228884815864931)
                  ·
                    refine ⟨66567544414843327223797397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44378362943228884815864931 66567544414843327223797397)
                    ·
                      refine ⟨3120353644445780963615503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66567544414843327223797397 3120353644445780963615503)
                      ·
                        rfl

theorem cell23_6076867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_6076867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076867 prefixEnd_6076867 := by exact prefixLift 6076867
  have htrace : WordTrace (prefixWord ++ tailWord_6076867) baseStart_6076867 baseEnd_6076867 := by
    simpa [prefixWord, tailWord_6076867, baseEnd_6076867] using wordTrace_append hprefix tailTrace_6076867
  have hstable : (prefixWord ++ tailWord_6076867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076867).length < 2 ^ (prefixWord ++ tailWord_6076867).sum := by decide
  have hdescent : baseEnd_6076867 < baseStart_6076867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076931 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 4, 3, 2]
def baseStart_6076931 : Nat := 118140960795 + 6076931 * 2 ^ 59
def prefixEnd_6076931 : Nat := 4983230072969 + 3 ^ 40 * 6076931 * 2
def baseEnd_6076931 : Nat := 3120386507207668713215209

theorem tailTrace_6076931 : CollatzResearch.WordTrace tailWord_6076931 prefixEnd_6076931 3120386507207668713215209 := by
  unfold tailWord_6076931
  simp only [CollatzResearch.WordTrace]
  refine ⟨221643882347324319031878647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147762588231549546021252431 221643882347324319031878647)
  ·
    refine ⟨332465823520986478547817971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221643882347324319031878647 332465823520986478547817971)
    ·
      refine ⟨498698735281479717821726957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332465823520986478547817971 498698735281479717821726957)
      ·
        refine ⟨187012025730554894183147609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498698735281479717821726957 187012025730554894183147609)
        ·
          refine ⟨140259019297916170637360707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187012025730554894183147609 140259019297916170637360707)
          ·
            refine ⟨210388528946874255956041061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140259019297916170637360707 210388528946874255956041061)
            ·
              refine ⟨39447849177538922991757699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210388528946874255956041061 39447849177538922991757699)
              ·
                refine ⟨59171773766308384487636549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39447849177538922991757699 59171773766308384487636549)
                ·
                  refine ⟨11094707581182822091431853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59171773766308384487636549 11094707581182822091431853)
                  ·
                    refine ⟨4160515342943558284286945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11094707581182822091431853 4160515342943558284286945)
                    ·
                      refine ⟨3120386507207668713215209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160515342943558284286945 3120386507207668713215209)
                      ·
                        rfl

theorem cell23_6076931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_6076931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076931 prefixEnd_6076931 := by exact prefixLift 6076931
  have htrace : WordTrace (prefixWord ++ tailWord_6076931) baseStart_6076931 baseEnd_6076931 := by
    simpa [prefixWord, tailWord_6076931, baseEnd_6076931] using wordTrace_append hprefix tailTrace_6076931
  have hstable : (prefixWord ++ tailWord_6076931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076931).length < 2 ^ (prefixWord ++ tailWord_6076931).sum := by decide
  have hdescent : baseEnd_6076931 < baseStart_6076931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076938 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_6076938 : Nat := 118140960795 + 6076938 * 2 ^ 59
def prefixEnd_6076938 : Nat := 4983230072969 + 3 ^ 40 * 6076938 * 2
def baseEnd_6076938 : Nat := 3120390101572250185827677

theorem tailTrace_6076938 : CollatzResearch.WordTrace tailWord_6076938 prefixEnd_6076938 3120390101572250185827677 := by
  unfold tailWord_6076938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55411034414574739806845867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147762758438865972818255645 55411034414574739806845867)
  ·
    refine ⟨83116551621862109710268801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55411034414574739806845867 83116551621862109710268801)
    ·
      refine ⟨62337413716396582282701601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83116551621862109710268801 62337413716396582282701601)
      ·
        refine ⟨46753060287297436712026201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62337413716396582282701601 46753060287297436712026201)
        ·
          refine ⟨35064795215473077534019651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46753060287297436712026201 35064795215473077534019651)
          ·
            refine ⟨52597192823209616301029477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35064795215473077534019651 52597192823209616301029477)
            ·
              refine ⟨9861973654351803056443027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52597192823209616301029477 9861973654351803056443027)
              ·
                refine ⟨14792960481527704584664541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861973654351803056443027 14792960481527704584664541)
                ·
                  refine ⟨5547360180572889219249203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14792960481527704584664541 5547360180572889219249203)
                  ·
                    refine ⟨8321040270859333828873805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547360180572889219249203 8321040270859333828873805)
                    ·
                      refine ⟨3120390101572250185827677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321040270859333828873805 3120390101572250185827677)
                      ·
                        rfl

theorem cell23_6076938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_6076938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076938 prefixEnd_6076938 := by exact prefixLift 6076938
  have htrace : WordTrace (prefixWord ++ tailWord_6076938) baseStart_6076938 baseEnd_6076938 := by
    simpa [prefixWord, tailWord_6076938, baseEnd_6076938] using wordTrace_append hprefix tailTrace_6076938
  have hstable : (prefixWord ++ tailWord_6076938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076938).length < 2 ^ (prefixWord ++ tailWord_6076938).sum := by decide
  have hdescent : baseEnd_6076938 < baseStart_6076938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076961 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6076961 : Nat := 118140960795 + 6076961 * 2 ^ 59
def prefixEnd_6076961 : Nat := 4983230072969 + 3 ^ 40 * 6076961 * 2
def baseEnd_6076961 : Nat := 3120401911627303595840071

theorem tailTrace_6076961 : CollatzResearch.WordTrace tailWord_6076961 prefixEnd_6076961 3120401911627303595840071 := by
  unfold tailWord_6076961
  simp only [CollatzResearch.WordTrace]
  refine ⟨221644976537215634155470737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147763317691477089436980491 221644976537215634155470737)
  ·
    refine ⟨166233732402911725616603053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221644976537215634155470737 166233732402911725616603053)
    ·
      refine ⟨62337649651091897106226145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166233732402911725616603053 62337649651091897106226145)
      ·
        refine ⟨46753237238318922829669609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62337649651091897106226145 46753237238318922829669609)
        ·
          refine ⟨35064927928739192122252207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46753237238318922829669609 35064927928739192122252207)
          ·
            refine ⟨52597391893108788183378311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35064927928739192122252207 52597391893108788183378311)
            ·
              refine ⟨78896087839663182275067467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52597391893108788183378311 78896087839663182275067467)
              ·
                refine ⟨118344131759494773412601201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78896087839663182275067467 118344131759494773412601201)
                ·
                  refine ⟨88758098819621080059450901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118344131759494773412601201 88758098819621080059450901)
                  ·
                    refine ⟨4160535882169738127786761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88758098819621080059450901 4160535882169738127786761)
                    ·
                      refine ⟨3120401911627303595840071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160535882169738127786761 3120401911627303595840071)
                      ·
                        rfl

theorem cell23_6076961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6076961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076961 prefixEnd_6076961 := by exact prefixLift 6076961
  have htrace : WordTrace (prefixWord ++ tailWord_6076961) baseStart_6076961 baseEnd_6076961 := by
    simpa [prefixWord, tailWord_6076961, baseEnd_6076961] using wordTrace_append hprefix tailTrace_6076961
  have hstable : (prefixWord ++ tailWord_6076961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076961).length < 2 ^ (prefixWord ++ tailWord_6076961).sum := by decide
  have hdescent : baseEnd_6076961 < baseStart_6076961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076978 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_6076978 : Nat := 118140960795 + 6076978 * 2 ^ 59
def prefixEnd_6076978 : Nat := 4983230072969 + 3 ^ 40 * 6076978 * 2
def baseEnd_6076978 : Nat := 3120410640798430029327493

theorem tailTrace_6076978 : CollatzResearch.WordTrace tailWord_6076978 prefixEnd_6076978 3120410640798430029327493 := by
  unfold tailWord_6076978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55411399144538511514709897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147763731052102697372559725 55411399144538511514709897)
  ·
    refine ⟨41558549358403883636032423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55411399144538511514709897 41558549358403883636032423)
    ·
      refine ⟨62337824037605825454048635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41558549358403883636032423 62337824037605825454048635)
      ·
        refine ⟨93506736056408738181072953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62337824037605825454048635 93506736056408738181072953)
        ·
          refine ⟨70130052042306553635804715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93506736056408738181072953 70130052042306553635804715)
          ·
            refine ⟨105195078063459830453707073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70130052042306553635804715 105195078063459830453707073)
            ·
              refine ⟨78896308547594872840280305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105195078063459830453707073 78896308547594872840280305)
              ·
                refine ⟨59172231410696154630210229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78896308547594872840280305 59172231410696154630210229)
                ·
                  refine ⟨5547396694752764496582209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59172231410696154630210229 5547396694752764496582209)
                  ·
                    refine ⟨4160547521064573372436657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5547396694752764496582209 4160547521064573372436657)
                    ·
                      refine ⟨3120410640798430029327493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160547521064573372436657 3120410640798430029327493)
                      ·
                        rfl

theorem cell23_6076978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_6076978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076978 prefixEnd_6076978 := by exact prefixLift 6076978
  have htrace : WordTrace (prefixWord ++ tailWord_6076978) baseStart_6076978 baseEnd_6076978 := by
    simpa [prefixWord, tailWord_6076978, baseEnd_6076978] using wordTrace_append hprefix tailTrace_6076978
  have hstable : (prefixWord ++ tailWord_6076978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076978).length < 2 ^ (prefixWord ++ tailWord_6076978).sum := by decide
  have hdescent : baseEnd_6076978 < baseStart_6076978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076981 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_6076981 : Nat := 118140960795 + 6076981 * 2 ^ 59
def prefixEnd_6076981 : Nat := 4983230072969 + 3 ^ 40 * 6076981 * 2
def baseEnd_6076981 : Nat := 3120412181240393517589979

theorem tailTrace_6076981 : CollatzResearch.WordTrace tailWord_6076981 prefixEnd_6076981 3120412181240393517589979 := by
  unfold tailWord_6076981
  simp only [CollatzResearch.WordTrace]
  refine ⟨221645705997143177571198797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147763803998095451714132531 221645705997143177571198797)
  ·
    refine ⟨83117139748928691589199549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221645705997143177571198797 83117139748928691589199549)
    ·
      refine ⟨31168927405848259345949831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83117139748928691589199549 31168927405848259345949831)
      ·
        refine ⟨46753391108772389018924747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31168927405848259345949831 46753391108772389018924747)
        ·
          refine ⟨70130086663158583528387121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46753391108772389018924747 70130086663158583528387121)
          ·
            refine ⟨52597564997368937646290341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70130086663158583528387121 52597564997368937646290341)
            ·
              refine ⟨9862043437006675808679439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52597564997368937646290341 9862043437006675808679439)
              ·
                refine ⟨14793065155510013713019159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9862043437006675808679439 14793065155510013713019159)
                ·
                  refine ⟨22189597733265020569528739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14793065155510013713019159 22189597733265020569528739)
                  ·
                    refine ⟨33284396599897530854293109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22189597733265020569528739 33284396599897530854293109)
                    ·
                      refine ⟨3120412181240393517589979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33284396599897530854293109 3120412181240393517589979)
                      ·
                        rfl

theorem cell23_6076981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_6076981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076981 prefixEnd_6076981 := by exact prefixLift 6076981
  have htrace : WordTrace (prefixWord ++ tailWord_6076981) baseStart_6076981 baseEnd_6076981 := by
    simpa [prefixWord, tailWord_6076981, baseEnd_6076981] using wordTrace_append hprefix tailTrace_6076981
  have hstable : (prefixWord ++ tailWord_6076981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076981).length < 2 ^ (prefixWord ++ tailWord_6076981).sum := by decide
  have hdescent : baseEnd_6076981 < baseStart_6076981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6076995 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 1, 2, 2]
def baseStart_6076995 : Nat := 118140960795 + 6076995 * 2 ^ 59
def prefixEnd_6076995 : Nat := 4983230072969 + 3 ^ 40 * 6076995 * 2
def baseEnd_6076995 : Nat := 3120419369969556462814915

theorem tailTrace_6076995 : CollatzResearch.WordTrace tailWord_6076995 prefixEnd_6076995 3120419369969556462814915 := by
  unfold tailWord_6076995
  simp only [CollatzResearch.WordTrace]
  refine ⟨221646216619092457962208439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147764144412728305308138959 221646216619092457962208439)
  ·
    refine ⟨332469324928638686943312659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221646216619092457962208439 332469324928638686943312659)
    ·
      refine ⟨498703987392958030414968989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332469324928638686943312659 498703987392958030414968989)
      ·
        refine ⟨187013995272359261405613371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498703987392958030414968989 187013995272359261405613371)
        ·
          refine ⟨280520992908538892108420057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187013995272359261405613371 280520992908538892108420057)
          ·
            refine ⟨210390744681404169081315043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280520992908538892108420057 210390744681404169081315043)
            ·
              refine ⟨315586117022106253621972565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210390744681404169081315043 315586117022106253621972565)
              ·
                refine ⟨3698274808852807659632491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 315586117022106253621972565 3698274808852807659632491)
                ·
                  refine ⟨5547412213279211489448737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698274808852807659632491 5547412213279211489448737)
                  ·
                    refine ⟨4160559159959408617086553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5547412213279211489448737 4160559159959408617086553)
                    ·
                      refine ⟨3120419369969556462814915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160559159959408617086553 3120419369969556462814915)
                      ·
                        rfl

theorem cell23_6076995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_6076995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6076995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6076995 prefixEnd_6076995 := by exact prefixLift 6076995
  have htrace : WordTrace (prefixWord ++ tailWord_6076995) baseStart_6076995 baseEnd_6076995 := by
    simpa [prefixWord, tailWord_6076995, baseEnd_6076995] using wordTrace_append hprefix tailTrace_6076995
  have hstable : (prefixWord ++ tailWord_6076995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6076995).length < 2 ^ (prefixWord ++ tailWord_6076995).sum := by decide
  have hdescent : baseEnd_6076995 < baseStart_6076995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6076995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077004 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6077004 : Nat := 118140960795 + 6077004 * 2 ^ 59
def prefixEnd_6077004 : Nat := 4983230072969 + 3 ^ 40 * 6077004 * 2
def baseEnd_6077004 : Nat := 3120423991295446927602373

theorem tailTrace_6077004 : CollatzResearch.WordTrace tailWord_6077004 prefixEnd_6077004 3120423991295446927602373 := by
  unfold tailWord_6077004
  simp only [CollatzResearch.WordTrace]
  refine ⟨110823272438029926249643033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147764363250706568332857377 110823272438029926249643033)
  ·
    refine ⟨83117454328522444687232275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110823272438029926249643033 83117454328522444687232275)
    ·
      refine ⟨124676181492783667030848413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83117454328522444687232275 124676181492783667030848413)
      ·
        refine ⟨46753568059793875136568155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124676181492783667030848413 46753568059793875136568155)
        ·
          refine ⟨70130352089690812704852233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46753568059793875136568155 70130352089690812704852233)
          ·
            refine ⟨52597764067268109528639175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70130352089690812704852233 52597764067268109528639175)
            ·
              refine ⟨78896646100902164292958763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52597764067268109528639175 78896646100902164292958763)
              ·
                refine ⟨118344969151353246439438145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78896646100902164292958763 118344969151353246439438145)
                ·
                  refine ⟨88758726863514934829578609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118344969151353246439438145 88758726863514934829578609)
                  ·
                    refine ⟨66569045147636201122183957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88758726863514934829578609 66569045147636201122183957)
                    ·
                      refine ⟨3120423991295446927602373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66569045147636201122183957 3120423991295446927602373)
                      ·
                        rfl

theorem cell23_6077004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6077004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077004 prefixEnd_6077004 := by exact prefixLift 6077004
  have htrace : WordTrace (prefixWord ++ tailWord_6077004) baseStart_6077004 baseEnd_6077004 := by
    simpa [prefixWord, tailWord_6077004, baseEnd_6077004] using wordTrace_append hprefix tailTrace_6077004
  have hstable : (prefixWord ++ tailWord_6077004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077004).length < 2 ^ (prefixWord ++ tailWord_6077004).sum := by decide
  have hdescent : baseEnd_6077004 < baseStart_6077004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077005 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6077005 : Nat := 118140960795 + 6077005 * 2 ^ 59
def prefixEnd_6077005 : Nat := 4983230072969 + 3 ^ 40 * 6077005 * 2
def baseEnd_6077005 : Nat := 1040141501592033807896623

theorem tailTrace_6077005 : CollatzResearch.WordTrace tailWord_6077005 prefixEnd_6077005 1040141501592033807896623 := by
  unfold tailWord_6077005
  simp only [CollatzResearch.WordTrace]
  refine ⟨221646581349056229670072469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147764387566037486446714979 221646581349056229670072469)
  ·
    refine ⟨10389683500737010765784647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221646581349056229670072469 10389683500737010765784647)
    ·
      refine ⟨15584525251105516148676971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10389683500737010765784647 15584525251105516148676971)
      ·
        refine ⟨23376787876658274223015457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15584525251105516148676971 23376787876658274223015457)
        ·
          refine ⟨17532590907493705667261593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23376787876658274223015457 17532590907493705667261593)
          ·
            refine ⟨13149443180620279250446195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17532590907493705667261593 13149443180620279250446195)
            ·
              refine ⟨19724164770930418875669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13149443180620279250446195 19724164770930418875669293)
              ·
                refine ⟨7396561789098907078375985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19724164770930418875669293 7396561789098907078375985)
                ·
                  refine ⟨5547421341824180308781989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7396561789098907078375985 5547421341824180308781989)
                  ·
                    refine ⟨1040141501592033807896623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547421341824180308781989 1040141501592033807896623)
                    ·
                      rfl

theorem cell23_6077005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6077005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077005 prefixEnd_6077005 := by exact prefixLift 6077005
  have htrace : WordTrace (prefixWord ++ tailWord_6077005) baseStart_6077005 baseEnd_6077005 := by
    simpa [prefixWord, tailWord_6077005, baseEnd_6077005] using wordTrace_append hprefix tailTrace_6077005
  have hstable : (prefixWord ++ tailWord_6077005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077005).length < 2 ^ (prefixWord ++ tailWord_6077005).sum := by decide
  have hdescent : baseEnd_6077005 < baseStart_6077005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077022 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6077022 : Nat := 118140960795 + 6077022 * 2 ^ 59
def prefixEnd_6077022 : Nat := 4983230072969 + 3 ^ 40 * 6077022 * 2
def baseEnd_6077022 : Nat := 1040144411315742619059097

theorem tailTrace_6077022 : CollatzResearch.WordTrace tailWord_6077022 prefixEnd_6077022 1040144411315742619059097 := by
  unfold tailWord_6077022
  simp only [CollatzResearch.WordTrace]
  refine ⟨27705900173749330196680165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147764800926663094382294213 27705900173749330196680165)
  ·
    refine ⟨5194856282577999411877531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27705900173749330196680165 5194856282577999411877531)
    ·
      refine ⟨7792284423866999117816297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194856282577999411877531 7792284423866999117816297)
      ·
        refine ⟨5844213317900249338362223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7792284423866999117816297 5844213317900249338362223)
        ·
          refine ⟨8766319976850374007543335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844213317900249338362223 8766319976850374007543335)
          ·
            refine ⟨13149479965275561011315003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766319976850374007543335 13149479965275561011315003)
            ·
              refine ⟨19724219947913341516972505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13149479965275561011315003 19724219947913341516972505)
              ·
                refine ⟨14793164960935006137729379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19724219947913341516972505 14793164960935006137729379)
                ·
                  refine ⟨22189747441402509206594069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14793164960935006137729379 22189747441402509206594069)
                  ·
                    refine ⟨1040144411315742619059097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22189747441402509206594069 1040144411315742619059097)
                    ·
                      rfl

theorem cell23_6077022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6077022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077022 prefixEnd_6077022 := by exact prefixLift 6077022
  have htrace : WordTrace (prefixWord ++ tailWord_6077022) baseStart_6077022 baseEnd_6077022 := by
    simpa [prefixWord, tailWord_6077022, baseEnd_6077022] using wordTrace_append hprefix tailTrace_6077022
  have hstable : (prefixWord ++ tailWord_6077022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077022).length < 2 ^ (prefixWord ++ tailWord_6077022).sum := by decide
  have hdescent : baseEnd_6077022 < baseStart_6077022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077024 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_6077024 : Nat := 118140960795 + 6077024 * 2 ^ 59
def prefixEnd_6077024 : Nat := 4983230072969 + 3 ^ 40 * 6077024 * 2
def baseEnd_6077024 : Nat := 3120434260908536849352281

theorem tailTrace_6077024 : CollatzResearch.WordTrace tailWord_6077024 prefixEnd_6077024 3120434260908536849352281 := by
  unfold tailWord_6077024
  simp only [CollatzResearch.WordTrace]
  refine ⟨110823637167993697957507063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147764849557324930610009417 110823637167993697957507063)
  ·
    refine ⟨166235455751990546936260595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110823637167993697957507063 166235455751990546936260595)
    ·
      refine ⟨249353183627985820404390893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166235455751990546936260595 249353183627985820404390893)
      ·
        refine ⟨93507443860494682651646585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249353183627985820404390893 93507443860494682651646585)
        ·
          refine ⟨70130582895371011988734939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93507443860494682651646585 70130582895371011988734939)
          ·
            refine ⟨105195874343056517983102409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70130582895371011988734939 105195874343056517983102409)
            ·
              refine ⟨78896905757292388487326807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105195874343056517983102409 78896905757292388487326807)
              ·
                refine ⟨118345358635938582730990211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78896905757292388487326807 118345358635938582730990211)
                ·
                  refine ⟨177518037953907874096485317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118345358635938582730990211 177518037953907874096485317)
                  ·
                    refine ⟨33284632116357726393090997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177518037953907874096485317 33284632116357726393090997)
                    ·
                      refine ⟨3120434260908536849352281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33284632116357726393090997 3120434260908536849352281)
                      ·
                        rfl

theorem cell23_6077024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_6077024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077024 prefixEnd_6077024 := by exact prefixLift 6077024
  have htrace : WordTrace (prefixWord ++ tailWord_6077024) baseStart_6077024 baseEnd_6077024 := by
    simpa [prefixWord, tailWord_6077024, baseEnd_6077024] using wordTrace_append hprefix tailTrace_6077024
  have hstable : (prefixWord ++ tailWord_6077024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077024).length < 2 ^ (prefixWord ++ tailWord_6077024).sum := by decide
  have hdescent : baseEnd_6077024 < baseStart_6077024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077032 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6077032 : Nat := 118140960795 + 6077032 * 2 ^ 59
def prefixEnd_6077032 : Nat := 4983230072969 + 3 ^ 40 * 6077032 * 2
def baseEnd_6077032 : Nat := 3120438368753772818052245

theorem tailTrace_6077032 : CollatzResearch.WordTrace tailWord_6077032 prefixEnd_6077032 3120438368753772818052245 := by
  unfold tailWord_6077032
  simp only [CollatzResearch.WordTrace]
  refine ⟨110823783059979206640652675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147765044079972275520870233 110823783059979206640652675)
  ·
    refine ⟨166235674589968809960979013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110823783059979206640652675 166235674589968809960979013)
    ·
      refine ⟨31169188985619151867683565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166235674589968809960979013 31169188985619151867683565)
      ·
        refine ⟨11688445869607181950381337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31169188985619151867683565 11688445869607181950381337)
        ·
          refine ⟨8766334402205386462786003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11688445869607181950381337 8766334402205386462786003)
          ·
            refine ⟨13149501603308079694179005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766334402205386462786003 13149501603308079694179005)
            ·
              refine ⟨4931063101240529885317127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13149501603308079694179005 4931063101240529885317127)
              ·
                refine ⟨7396594651860794827975691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931063101240529885317127 7396594651860794827975691)
                ·
                  refine ⟨11094891977791192241963537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7396594651860794827975691 11094891977791192241963537)
                  ·
                    refine ⟨8321168983343394181472653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11094891977791192241963537 8321168983343394181472653)
                    ·
                      refine ⟨3120438368753772818052245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321168983343394181472653 3120438368753772818052245)
                      ·
                        rfl

theorem cell23_6077032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6077032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077032 prefixEnd_6077032 := by exact prefixLift 6077032
  have htrace : WordTrace (prefixWord ++ tailWord_6077032) baseStart_6077032 baseEnd_6077032 := by
    simpa [prefixWord, tailWord_6077032, baseEnd_6077032] using wordTrace_append hprefix tailTrace_6077032
  have hstable : (prefixWord ++ tailWord_6077032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077032).length < 2 ^ (prefixWord ++ tailWord_6077032).sum := by decide
  have hdescent : baseEnd_6077032 < baseStart_6077032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077061 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_6077061 : Nat := 118140960795 + 6077061 * 2 ^ 59
def prefixEnd_6077061 : Nat := 4983230072969 + 3 ^ 40 * 6077061 * 2
def baseEnd_6077061 : Nat := 1040151086564251068196537

theorem tailTrace_6077061 : CollatzResearch.WordTrace tailWord_6077061 prefixEnd_6077061 1040151086564251068196537 := by
  unfold tailWord_6077061
  simp only [CollatzResearch.WordTrace]
  refine ⟨221648623836853351234111037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147765749224568900822740691 221648623836853351234111037)
  ·
    refine ⟨83118233938820006712791639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221648623836853351234111037 83118233938820006712791639)
    ·
      refine ⟨124677350908230010069187459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83118233938820006712791639 124677350908230010069187459)
      ·
        refine ⟨187016026362345015103781189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124677350908230010069187459 187016026362345015103781189)
        ·
          refine ⟨35065504942939690331958973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187016026362345015103781189 35065504942939690331958973)
          ·
            refine ⟨13149564353602383874484615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35065504942939690331958973 13149564353602383874484615)
            ·
              refine ⟨19724346530403575811726923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13149564353602383874484615 19724346530403575811726923)
              ·
                refine ⟨29586519795605363717590385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19724346530403575811726923 29586519795605363717590385)
                ·
                  refine ⟨22189889846704022788192789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29586519795605363717590385 22189889846704022788192789)
                  ·
                    refine ⟨1040151086564251068196537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22189889846704022788192789 1040151086564251068196537)
                    ·
                      rfl

theorem cell23_6077061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_6077061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077061 prefixEnd_6077061 := by exact prefixLift 6077061
  have htrace : WordTrace (prefixWord ++ tailWord_6077061) baseStart_6077061 baseEnd_6077061 := by
    simpa [prefixWord, tailWord_6077061, baseEnd_6077061] using wordTrace_append hprefix tailTrace_6077061
  have hstable : (prefixWord ++ tailWord_6077061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077061).length < 2 ^ (prefixWord ++ tailWord_6077061).sum := by decide
  have hdescent : baseEnd_6077061 < baseStart_6077061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077089 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6077089 : Nat := 118140960795 + 6077089 * 2 ^ 59
def prefixEnd_6077089 : Nat := 4983230072969 + 3 ^ 40 * 6077089 * 2
def baseEnd_6077089 : Nat := 3120467637151079095039483

theorem tailTrace_6077089 : CollatzResearch.WordTrace tailWord_6077089 prefixEnd_6077089 3120467637151079095039483 := by
  unfold tailWord_6077089
  simp only [CollatzResearch.WordTrace]
  refine ⟨221649645080751912016130321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147766430053834608010753547 221649645080751912016130321)
  ·
    refine ⟨166237233810563934012097741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221649645080751912016130321 166237233810563934012097741)
    ·
      refine ⟨62338962678961475254536653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166237233810563934012097741 62338962678961475254536653)
      ·
        refine ⟨23377111004610553220451245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62338962678961475254536653 23377111004610553220451245)
        ·
          refine ⟨8766416626728957457669217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23377111004610553220451245 8766416626728957457669217)
          ·
            refine ⟨6574812470046718093251913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8766416626728957457669217 6574812470046718093251913)
            ·
              refine ⟨4931109352535038569938935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574812470046718093251913 4931109352535038569938935)
              ·
                refine ⟨7396664028802557854908403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931109352535038569938935 7396664028802557854908403)
                ·
                  refine ⟨11094996043203836782362605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7396664028802557854908403 11094996043203836782362605)
                  ·
                    refine ⟨4160623516201438793385977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11094996043203836782362605 4160623516201438793385977)
                    ·
                      refine ⟨3120467637151079095039483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160623516201438793385977 3120467637151079095039483)
                      ·
                        rfl

theorem cell23_6077089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6077089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077089 prefixEnd_6077089 := by exact prefixLift 6077089
  have htrace : WordTrace (prefixWord ++ tailWord_6077089) baseStart_6077089 baseEnd_6077089 := by
    simpa [prefixWord, tailWord_6077089, baseEnd_6077089] using wordTrace_append hprefix tailTrace_6077089
  have hstable : (prefixWord ++ tailWord_6077089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077089).length < 2 ^ (prefixWord ++ tailWord_6077089).sum := by decide
  have hdescent : baseEnd_6077089 < baseStart_6077089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077118 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_6077118 : Nat := 118140960795 + 6077118 * 2 ^ 59
def prefixEnd_6077118 : Nat := 4983230072969 + 3 ^ 40 * 6077118 * 2
def baseEnd_6077118 : Nat := 3120482528090059481576849

theorem tailTrace_6077118 : CollatzResearch.WordTrace tailWord_6077118 prefixEnd_6077118 3120482528090059481576849 := by
  unfold tailWord_6077118
  simp only [CollatzResearch.WordTrace]
  refine ⟨27706337849705856246117001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147767135198431233312624005 27706337849705856246117001)
  ·
    refine ⟨20779753387279392184587751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27706337849705856246117001 20779753387279392184587751)
    ·
      refine ⟨31169630080919088276881627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20779753387279392184587751 31169630080919088276881627)
      ·
        refine ⟨46754445121378632415322441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31169630080919088276881627 46754445121378632415322441)
        ·
          refine ⟨35065833841033974311491831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46754445121378632415322441 35065833841033974311491831)
          ·
            refine ⟨52598750761550961467237747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35065833841033974311491831 52598750761550961467237747)
            ·
              refine ⟨78898126142326442200856621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52598750761550961467237747 78898126142326442200856621)
              ·
                refine ⟨29586797303372415825321233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78898126142326442200856621 29586797303372415825321233)
                ·
                  refine ⟨22190097977529311868990925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29586797303372415825321233 22190097977529311868990925)
                  ·
                    refine ⟨8321286741573491950871597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22190097977529311868990925 8321286741573491950871597)
                    ·
                      refine ⟨3120482528090059481576849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321286741573491950871597 3120482528090059481576849)
                      ·
                        rfl

theorem cell23_6077118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_6077118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077118 prefixEnd_6077118 := by exact prefixLift 6077118
  have htrace : WordTrace (prefixWord ++ tailWord_6077118) baseStart_6077118 baseEnd_6077118 := by
    simpa [prefixWord, tailWord_6077118, baseEnd_6077118] using wordTrace_append hprefix tailTrace_6077118
  have hstable : (prefixWord ++ tailWord_6077118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077118).length < 2 ^ (prefixWord ++ tailWord_6077118).sum := by decide
  have hdescent : baseEnd_6077118 < baseStart_6077118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077211 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 7, 5]
def baseStart_6077211 : Nat := 118140960795 + 6077211 * 2 ^ 59
def prefixEnd_6077211 : Nat := 4983230072969 + 3 ^ 40 * 6077211 * 2
def baseEnd_6077211 : Nat := 1040176760596975872571307

theorem tailTrace_6077211 : CollatzResearch.WordTrace tailWord_6077211 prefixEnd_6077211 1040176760596975872571307 := by
  unfold tailWord_6077211
  simp only [CollatzResearch.WordTrace]
  refine ⟨221654094786309926852071487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147769396524206617901380991 221654094786309926852071487)
  ·
    refine ⟨332481142179464890278107231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221654094786309926852071487 332481142179464890278107231)
    ·
      refine ⟨498721713269197335417160847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332481142179464890278107231 498721713269197335417160847)
      ·
        refine ⟨748082569903796003125741271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498721713269197335417160847 748082569903796003125741271)
        ·
          refine ⟨1122123854855694004688611907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748082569903796003125741271 1122123854855694004688611907)
          ·
            refine ⟨1683185782283541007032917861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122123854855694004688611907 1683185782283541007032917861)
            ·
              refine ⟨315597334178163938818672099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1683185782283541007032917861 315597334178163938818672099)
              ·
                refine ⟨473396001267245908228008149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315597334178163938818672099 473396001267245908228008149)
                ·
                  refine ⟨11095218779701075974093941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 473396001267245908228008149 11095218779701075974093941)
                  ·
                    refine ⟨1040176760596975872571307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11095218779701075974093941 1040176760596975872571307)
                    ·
                      rfl

theorem cell23_6077211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].length) (baseStart_6077211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077211 prefixEnd_6077211 := by exact prefixLift 6077211
  have htrace : WordTrace (prefixWord ++ tailWord_6077211) baseStart_6077211 baseEnd_6077211 := by
    simpa [prefixWord, tailWord_6077211, baseEnd_6077211] using wordTrace_append hprefix tailTrace_6077211
  have hstable : (prefixWord ++ tailWord_6077211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077211).length < 2 ^ (prefixWord ++ tailWord_6077211).sum := by decide
  have hdescent : baseEnd_6077211 < baseStart_6077211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077231 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_6077231 : Nat := 118140960795 + 6077231 * 2 ^ 59
def prefixEnd_6077231 : Nat := 4983230072969 + 3 ^ 40 * 6077231 * 2
def baseEnd_6077231 : Nat := 3120540551404017539463829

theorem tailTrace_6077231 : CollatzResearch.WordTrace tailWord_6077231 prefixEnd_6077231 3120540551404017539463829 := by
  unfold tailWord_6077231
  simp only [CollatzResearch.WordTrace]
  refine ⟨221654824246237470267799547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147769882830824980178533031 221654824246237470267799547)
  ·
    refine ⟨332482236369356205401699321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221654824246237470267799547 332482236369356205401699321)
    ·
      refine ⟨249361677277017154051274491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332482236369356205401699321 249361677277017154051274491)
      ·
        refine ⟨374042515915525731076911737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249361677277017154051274491 374042515915525731076911737)
        ·
          refine ⟨280531886936644298307683803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374042515915525731076911737 280531886936644298307683803)
          ·
            refine ⟨420797830404966447461525705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280531886936644298307683803 420797830404966447461525705)
            ·
              refine ⟨315598372803724835596144279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420797830404966447461525705 315598372803724835596144279)
              ·
                refine ⟨473397559205587253394216419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315598372803724835596144279 473397559205587253394216419)
                ·
                  refine ⟨710096338808380880091324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473397559205587253394216419 710096338808380880091324629)
                  ·
                    refine ⟨16642882940821426877140421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 710096338808380880091324629 16642882940821426877140421)
                    ·
                      refine ⟨3120540551404017539463829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16642882940821426877140421 3120540551404017539463829)
                      ·
                        rfl

theorem cell23_6077231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_6077231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077231 prefixEnd_6077231 := by exact prefixLift 6077231
  have htrace : WordTrace (prefixWord ++ tailWord_6077231) baseStart_6077231 baseEnd_6077231 := by
    simpa [prefixWord, tailWord_6077231, baseEnd_6077231] using wordTrace_append hprefix tailTrace_6077231
  have hstable : (prefixWord ++ tailWord_6077231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077231).length < 2 ^ (prefixWord ++ tailWord_6077231).sum := by decide
  have hdescent : baseEnd_6077231 < baseStart_6077231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077242 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_6077242 : Nat := 118140960795 + 6077242 * 2 ^ 59
def prefixEnd_6077242 : Nat := 4983230072969 + 3 ^ 40 * 6077242 * 2
def baseEnd_6077242 : Nat := 3120546199691216996426279

theorem tailTrace_6077242 : CollatzResearch.WordTrace tailWord_6077242 prefixEnd_6077242 3120546199691216996426279 := by
  unfold tailWord_6077242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55413806362299404786612495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147770150299465079430966653 55413806362299404786612495)
  ·
    refine ⟨83120709543449107179918743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55413806362299404786612495 83120709543449107179918743)
    ·
      refine ⟨124681064315173660769878115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83120709543449107179918743 124681064315173660769878115)
      ·
        refine ⟨187021596472760491154817173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124681064315173660769878115 187021596472760491154817173)
        ·
          refine ⟨8766637334660648022882055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187021596472760491154817173 8766637334660648022882055)
          ·
            refine ⟨13149956001990972034323083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766637334660648022882055 13149956001990972034323083)
            ·
              refine ⟨19724934002986458051484625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13149956001990972034323083 19724934002986458051484625)
              ·
                refine ⟨14793700502239843538613469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19724934002986458051484625 14793700502239843538613469)
                ·
                  refine ⟨5547637688339941326980051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14793700502239843538613469 5547637688339941326980051)
                  ·
                    refine ⟨8321456532509911990470077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547637688339941326980051 8321456532509911990470077)
                    ·
                      refine ⟨3120546199691216996426279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321456532509911990470077 3120546199691216996426279)
                      ·
                        rfl

theorem cell23_6077242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_6077242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077242 prefixEnd_6077242 := by exact prefixLift 6077242
  have htrace : WordTrace (prefixWord ++ tailWord_6077242) baseStart_6077242 baseEnd_6077242 := by
    simpa [prefixWord, tailWord_6077242, baseEnd_6077242] using wordTrace_append hprefix tailTrace_6077242
  have hstable : (prefixWord ++ tailWord_6077242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077242).length < 2 ^ (prefixWord ++ tailWord_6077242).sum := by decide
  have hdescent : baseEnd_6077242 < baseStart_6077242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077292 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_6077292 : Nat := 118140960795 + 6077292 * 2 ^ 59
def prefixEnd_6077292 : Nat := 4983230072969 + 3 ^ 40 * 6077292 * 2
def baseEnd_6077292 : Nat := 1040190624574647266933683

theorem tailTrace_6077292 : CollatzResearch.WordTrace tailWord_6077292 prefixEnd_6077292 1040190624574647266933683 := by
  unfold tailWord_6077292
  simp only [CollatzResearch.WordTrace]
  refine ⟨110828524549508238842885065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147771366066010985123846753 110828524549508238842885065)
  ·
    refine ⟨83121393412131179132163799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110828524549508238842885065 83121393412131179132163799)
    ·
      refine ⟨124682090118196768698245699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83121393412131179132163799 124682090118196768698245699)
      ·
        refine ⟨187023135177295153047368549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124682090118196768698245699 187023135177295153047368549)
        ·
          refine ⟨35066837845742841196381603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187023135177295153047368549 35066837845742841196381603)
          ·
            refine ⟨52600256768614261794572405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35066837845742841196381603 52600256768614261794572405)
            ·
              refine ⟨4931274072057587043241163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52600256768614261794572405 4931274072057587043241163)
              ·
                refine ⟨7396911108086380564861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931274072057587043241163 7396911108086380564861745)
                ·
                  refine ⟨5547683331064785423646309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7396911108086380564861745 5547683331064785423646309)
                  ·
                    refine ⟨1040190624574647266933683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547683331064785423646309 1040190624574647266933683)
                    ·
                      rfl

theorem cell23_6077292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_6077292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077292 prefixEnd_6077292 := by exact prefixLift 6077292
  have htrace : WordTrace (prefixWord ++ tailWord_6077292) baseStart_6077292 baseEnd_6077292 := by
    simpa [prefixWord, tailWord_6077292, baseEnd_6077292] using wordTrace_append hprefix tailTrace_6077292
  have hstable : (prefixWord ++ tailWord_6077292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077292).length < 2 ^ (prefixWord ++ tailWord_6077292).sum := by decide
  have hdescent : baseEnd_6077292 < baseStart_6077292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077305 : List Nat := [1, 2, 1, 3, 2, 5, 2, 7]
def baseStart_6077305 : Nat := 118140960795 + 6077305 * 2 ^ 59
def prefixEnd_6077305 : Nat := 4983230072969 + 3 ^ 40 * 6077305 * 2
def baseEnd_6077305 : Nat := 115576983295275935182907

theorem tailTrace_6077305 : CollatzResearch.WordTrace tailWord_6077305 prefixEnd_6077305 115576983295275935182907 := by
  unfold tailWord_6077305
  simp only [CollatzResearch.WordTrace]
  refine ⟨221657523247969380905993369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147771682165312920603995579 221657523247969380905993369)
  ·
    refine ⟨166243142435977035679495027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221657523247969380905993369 166243142435977035679495027)
    ·
      refine ⟨249364713653965553519242541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166243142435977035679495027 249364713653965553519242541)
      ·
        refine ⟨93511767620237082569715953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249364713653965553519242541 93511767620237082569715953)
        ·
          refine ⟨70133825715177811927286965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93511767620237082569715953 70133825715177811927286965)
          ·
            refine ⟨6575046160797919868183153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70133825715177811927286965 6575046160797919868183153)
            ·
              refine ⟨4931284620598439901137365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575046160797919868183153 4931284620598439901137365)
              ·
                refine ⟨115576983295275935182907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4931284620598439901137365 115576983295275935182907)
                ·
                  rfl

theorem cell23_6077305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 7].length) (baseStart_6077305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077305 prefixEnd_6077305 := by exact prefixLift 6077305
  have htrace : WordTrace (prefixWord ++ tailWord_6077305) baseStart_6077305 baseEnd_6077305 := by
    simpa [prefixWord, tailWord_6077305, baseEnd_6077305] using wordTrace_append hprefix tailTrace_6077305
  have hstable : (prefixWord ++ tailWord_6077305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077305).length < 2 ^ (prefixWord ++ tailWord_6077305).sum := by decide
  have hdescent : baseEnd_6077305 < baseStart_6077305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077310 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6077310 : Nat := 118140960795 + 6077310 * 2 ^ 59
def prefixEnd_6077310 : Nat := 4983230072969 + 3 ^ 40 * 6077310 * 2
def baseEnd_6077310 : Nat := 3120581116375722730375967

theorem tailTrace_6077310 : CollatzResearch.WordTrace tailWord_6077310 prefixEnd_6077310 3120581116375722730375967 := by
  unfold tailWord_6077310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707213201618908344990673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147771803741967511173283589 27707213201618908344990673)
  ·
    refine ⟨20780409901214181258743005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27707213201618908344990673 20780409901214181258743005)
    ·
      refine ⟨7792653712955317972028627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20780409901214181258743005 7792653712955317972028627)
      ·
        refine ⟨11688980569432976958042941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792653712955317972028627 11688980569432976958042941)
        ·
          refine ⟨4383367713537366359266103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11688980569432976958042941 4383367713537366359266103)
          ·
            refine ⟨6575051570306049538899155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383367713537366359266103 6575051570306049538899155)
            ·
              refine ⟨9862577355459074308348733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575051570306049538899155 9862577355459074308348733)
              ·
                refine ⟨3698466508297152865630775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9862577355459074308348733 3698466508297152865630775)
                ·
                  refine ⟨5547699762445729298446163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698466508297152865630775 5547699762445729298446163)
                  ·
                    refine ⟨8321549643668593947669245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547699762445729298446163 8321549643668593947669245)
                    ·
                      refine ⟨3120581116375722730375967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321549643668593947669245 3120581116375722730375967)
                      ·
                        rfl

theorem cell23_6077310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6077310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077310 prefixEnd_6077310 := by exact prefixLift 6077310
  have htrace : WordTrace (prefixWord ++ tailWord_6077310) baseStart_6077310 baseEnd_6077310 := by
    simpa [prefixWord, tailWord_6077310, baseEnd_6077310] using wordTrace_append hprefix tailTrace_6077310
  have hstable : (prefixWord ++ tailWord_6077310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077310).length < 2 ^ (prefixWord ++ tailWord_6077310).sum := by decide
  have hdescent : baseEnd_6077310 < baseStart_6077310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077315 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 3]
def baseStart_6077315 : Nat := 118140960795 + 6077315 * 2 ^ 59
def prefixEnd_6077315 : Nat := 4983230072969 + 3 ^ 40 * 6077315 * 2
def baseEnd_6077315 : Nat := 3120583683778995210813443

theorem tailTrace_6077315 : CollatzResearch.WordTrace tailWord_6077315 prefixEnd_6077315 3120583683778995210813443 := by
  unfold tailWord_6077315
  simp only [CollatzResearch.WordTrace]
  refine ⟨221657887977933152613857399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147771925318622101742571599 221657887977933152613857399)
  ·
    refine ⟨332486831966899728920786099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221657887977933152613857399 332486831966899728920786099)
    ·
      refine ⟨498730247950349593381179149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332486831966899728920786099 498730247950349593381179149)
      ·
        refine ⟨187023842981381097517942181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498730247950349593381179149 187023842981381097517942181)
        ·
          refine ⟨35066970559008955784614159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187023842981381097517942181 35066970559008955784614159)
          ·
            refine ⟨52600455838513433676921239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35066970559008955784614159 52600455838513433676921239)
            ·
              refine ⟨78900683757770150515381859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52600455838513433676921239 78900683757770150515381859)
              ·
                refine ⟨118351025636655225773072789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78900683757770150515381859 118351025636655225773072789)
                ·
                  refine ⟨5547704326718213708112787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118351025636655225773072789 5547704326718213708112787)
                  ·
                    refine ⟨8321556490077320562169181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547704326718213708112787 8321556490077320562169181)
                    ·
                      refine ⟨3120583683778995210813443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321556490077320562169181 3120583683778995210813443)
                      ·
                        rfl

theorem cell23_6077315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_6077315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077315 prefixEnd_6077315 := by exact prefixLift 6077315
  have htrace : WordTrace (prefixWord ++ tailWord_6077315) baseStart_6077315 baseEnd_6077315 := by
    simpa [prefixWord, tailWord_6077315, baseEnd_6077315] using wordTrace_append hprefix tailTrace_6077315
  have hstable : (prefixWord ++ tailWord_6077315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077315).length < 2 ^ (prefixWord ++ tailWord_6077315).sum := by decide
  have hdescent : baseEnd_6077315 < baseStart_6077315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077332 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6077332 : Nat := 118140960795 + 6077332 * 2 ^ 59
def prefixEnd_6077332 : Nat := 4983230072969 + 3 ^ 40 * 6077332 * 2
def baseEnd_6077332 : Nat := 3120592412950121644300865

theorem tailTrace_6077332 : CollatzResearch.WordTrace tailWord_6077332 prefixEnd_6077332 3120592412950121644300865 := by
  unfold tailWord_6077332
  simp only [CollatzResearch.WordTrace]
  refine ⟨110829254009435782258613125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147772338679247709678150833 110829254009435782258613125)
  ·
    refine ⟨20780485126769209173489961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110829254009435782258613125 20780485126769209173489961)
    ·
      refine ⟨15585363845076906880117471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20780485126769209173489961 15585363845076906880117471)
      ·
        refine ⟨23378045767615360320176207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585363845076906880117471 23378045767615360320176207)
        ·
          refine ⟨35067068651423040480264311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23378045767615360320176207 35067068651423040480264311)
          ·
            refine ⟨52600602977134560720396467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35067068651423040480264311 52600602977134560720396467)
            ·
              refine ⟨78900904465701841080594701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52600602977134560720396467 78900904465701841080594701)
              ·
                refine ⟨29587839174638190405223013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78900904465701841080594701 29587839174638190405223013)
                ·
                  refine ⟨5547719845244660700979315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29587839174638190405223013 5547719845244660700979315)
                  ·
                    refine ⟨8321579767866991051468973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547719845244660700979315 8321579767866991051468973)
                    ·
                      refine ⟨3120592412950121644300865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321579767866991051468973 3120592412950121644300865)
                      ·
                        rfl

theorem cell23_6077332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6077332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077332 prefixEnd_6077332 := by exact prefixLift 6077332
  have htrace : WordTrace (prefixWord ++ tailWord_6077332) baseStart_6077332 baseEnd_6077332 := by
    simpa [prefixWord, tailWord_6077332, baseEnd_6077332] using wordTrace_append hprefix tailTrace_6077332
  have hstable : (prefixWord ++ tailWord_6077332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077332).length < 2 ^ (prefixWord ++ tailWord_6077332).sum := by decide
  have hdescent : baseEnd_6077332 < baseStart_6077332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077348 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_6077348 : Nat := 118140960795 + 6077348 * 2 ^ 59
def prefixEnd_6077348 : Nat := 4983230072969 + 3 ^ 40 * 6077348 * 2
def baseEnd_6077348 : Nat := 1040200209546864527233597

theorem tailTrace_6077348 : CollatzResearch.WordTrace tailWord_6077348 prefixEnd_6077348 1040200209546864527233597 := by
  unfold tailWord_6077348
  simp only [CollatzResearch.WordTrace]
  refine ⟨110829545793406799624904349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147772727724542399499872465 110829545793406799624904349)
  ·
    refine ⟨41561079672527549859339131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110829545793406799624904349 41561079672527549859339131)
    ·
      refine ⟨62341619508791324789008697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41561079672527549859339131 62341619508791324789008697)
      ·
        refine ⟨46756214631593493591756523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62341619508791324789008697 46756214631593493591756523)
        ·
          refine ⟨70134321947390240387634785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46756214631593493591756523 70134321947390240387634785)
          ·
            refine ⟨52600741460542680290726089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70134321947390240387634785 52600741460542680290726089)
            ·
              refine ⟨39450556095407010218044567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52600741460542680290726089 39450556095407010218044567)
              ·
                refine ⟨59175834143110515327066851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39450556095407010218044567 59175834143110515327066851)
                ·
                  refine ⟨88763751214665772990600277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59175834143110515327066851 88763751214665772990600277)
                  ·
                    refine ⟨1040200209546864527233597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88763751214665772990600277 1040200209546864527233597)
                    ·
                      rfl

theorem cell23_6077348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_6077348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077348 prefixEnd_6077348 := by exact prefixLift 6077348
  have htrace : WordTrace (prefixWord ++ tailWord_6077348) baseStart_6077348 baseEnd_6077348 := by
    simpa [prefixWord, tailWord_6077348, baseEnd_6077348] using wordTrace_append hprefix tailTrace_6077348
  have hstable : (prefixWord ++ tailWord_6077348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077348).length < 2 ^ (prefixWord ++ tailWord_6077348).sum := by decide
  have hdescent : baseEnd_6077348 < baseStart_6077348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077425 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_6077425 : Nat := 118140960795 + 6077425 * 2 ^ 59
def prefixEnd_6077425 : Nat := 4983230072969 + 3 ^ 40 * 6077425 * 2
def baseEnd_6077425 : Nat := 1040213388883663260145979

theorem tailTrace_6077425 : CollatzResearch.WordTrace tailWord_6077425 prefixEnd_6077425 1040213388883663260145979 := by
  unfold tailWord_6077425
  simp only [CollatzResearch.WordTrace]
  refine ⟨221661900007534641400361729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147774600005023094266907819 221661900007534641400361729)
  ·
    refine ⟨166246425005650981050271297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221661900007534641400361729 166246425005650981050271297)
    ·
      refine ⟨124684818754238235787703473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166246425005650981050271297 124684818754238235787703473)
      ·
        refine ⟨93513614065678676840777605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124684818754238235787703473 93513614065678676840777605)
        ·
          refine ⟨17533802637314751907645801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93513614065678676840777605 17533802637314751907645801)
          ·
            refine ⟨13150351977986063930734351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17533802637314751907645801 13150351977986063930734351)
            ·
              refine ⟨19725527966979095896101527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150351977986063930734351 19725527966979095896101527)
              ·
                refine ⟨29588291950468643844152291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19725527966979095896101527 29588291950468643844152291)
                ·
                  refine ⟨44382437925702965766228437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29588291950468643844152291 44382437925702965766228437)
                  ·
                    refine ⟨1040213388883663260145979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44382437925702965766228437 1040213388883663260145979)
                    ·
                      rfl

theorem cell23_6077425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_6077425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077425 prefixEnd_6077425 := by exact prefixLift 6077425
  have htrace : WordTrace (prefixWord ++ tailWord_6077425) baseStart_6077425 baseEnd_6077425 := by
    simpa [prefixWord, tailWord_6077425, baseEnd_6077425] using wordTrace_append hprefix tailTrace_6077425
  have hstable : (prefixWord ++ tailWord_6077425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077425).length < 2 ^ (prefixWord ++ tailWord_6077425).sum := by decide
  have hdescent : baseEnd_6077425 < baseStart_6077425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077445 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_6077445 : Nat := 118140960795 + 6077445 * 2 ^ 59
def prefixEnd_6077445 : Nat := 4983230072969 + 3 ^ 40 * 6077445 * 2
def baseEnd_6077445 : Nat := 3120650436264079702187845

theorem tailTrace_6077445 : CollatzResearch.WordTrace tailWord_6077445 prefixEnd_6077445 3120650436264079702187845 := by
  unfold tailWord_6077445
  simp only [CollatzResearch.WordTrace]
  refine ⟨221662629467462184816089789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147775086311641456544059859 221662629467462184816089789)
  ·
    refine ⟨83123486050298319306033671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221662629467462184816089789 83123486050298319306033671)
    ·
      refine ⟨124685229075447478959050507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83123486050298319306033671 124685229075447478959050507)
      ·
        refine ⟨187027843613171218438575761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124685229075447478959050507 187027843613171218438575761)
        ·
          refine ⟨140270882709878413828931821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187027843613171218438575761 140270882709878413828931821)
          ·
            refine ⟨52601581016204405185849433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140270882709878413828931821 52601581016204405185849433)
            ·
              refine ⟨39451185762153303889387075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52601581016204405185849433 39451185762153303889387075)
              ·
                refine ⟨59176778643229955834080613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39451185762153303889387075 59176778643229955834080613)
                ·
                  refine ⟨11095645995605616718890115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59176778643229955834080613 11095645995605616718890115)
                  ·
                    refine ⟨16643468993408425078335173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11095645995605616718890115 16643468993408425078335173)
                    ·
                      refine ⟨3120650436264079702187845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16643468993408425078335173 3120650436264079702187845)
                      ·
                        rfl

theorem cell23_6077445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_6077445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077445 prefixEnd_6077445 := by exact prefixLift 6077445
  have htrace : WordTrace (prefixWord ++ tailWord_6077445) baseStart_6077445 baseEnd_6077445 := by
    simpa [prefixWord, tailWord_6077445, baseEnd_6077445] using wordTrace_append hprefix tailTrace_6077445
  have hstable : (prefixWord ++ tailWord_6077445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077445).length < 2 ^ (prefixWord ++ tailWord_6077445).sum := by decide
  have hdescent : baseEnd_6077445 < baseStart_6077445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077465 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_6077465 : Nat := 118140960795 + 6077465 * 2 ^ 59
def prefixEnd_6077465 : Nat := 4983230072969 + 3 ^ 40 * 6077465 * 2
def baseEnd_6077465 : Nat := 3120660705877169623937753

theorem tailTrace_6077465 : CollatzResearch.WordTrace tailWord_6077465 prefixEnd_6077465 3120660705877169623937753 := by
  unfold tailWord_6077465
  simp only [CollatzResearch.WordTrace]
  refine ⟨221663358927389728231817849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147775572618259818821211899 221663358927389728231817849)
  ·
    refine ⟨166247519195542296173863387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221663358927389728231817849 166247519195542296173863387)
    ·
      refine ⟨249371278793313444260795081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166247519195542296173863387 249371278793313444260795081)
      ·
        refine ⟨187028459094985083195596311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249371278793313444260795081 187028459094985083195596311)
        ·
          refine ⟨280542688642477624793394467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187028459094985083195596311 280542688642477624793394467)
          ·
            refine ⟨420814032963716437190091701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280542688642477624793394467 420814032963716437190091701)
            ·
              refine ⟨39451315590348415986571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420814032963716437190091701 39451315590348415986571097)
              ·
                refine ⟨29588486692761311989928323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39451315590348415986571097 29588486692761311989928323)
                ·
                  refine ⟨44382730039141967984892485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29588486692761311989928323 44382730039141967984892485)
                  ·
                    refine ⟨8321761882339118997167341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44382730039141967984892485 8321761882339118997167341)
                    ·
                      refine ⟨3120660705877169623937753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8321761882339118997167341 3120660705877169623937753)
                      ·
                        rfl

theorem cell23_6077465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_6077465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077465 prefixEnd_6077465 := by exact prefixLift 6077465
  have htrace : WordTrace (prefixWord ++ tailWord_6077465) baseStart_6077465 baseEnd_6077465 := by
    simpa [prefixWord, tailWord_6077465, baseEnd_6077465] using wordTrace_append hprefix tailTrace_6077465
  have hstable : (prefixWord ++ tailWord_6077465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077465).length < 2 ^ (prefixWord ++ tailWord_6077465).sum := by decide
  have hdescent : baseEnd_6077465 < baseStart_6077465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077502 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_6077502 : Nat := 118140960795 + 6077502 * 2 ^ 59
def prefixEnd_6077502 : Nat := 4983230072969 + 3 ^ 40 * 6077502 * 2
def baseEnd_6077502 : Nat := 346742189406820664352787

theorem tailTrace_6077502 : CollatzResearch.WordTrace tailWord_6077502 prefixEnd_6077502 346742189406820664352787 := by
  unfold tailWord_6077502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708088553531960443864345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147776472285503789033943173 27708088553531960443864345)
  ·
    refine ⟨20781066415148970332898259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27708088553531960443864345 20781066415148970332898259)
    ·
      refine ⟨31171599622723455499347389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20781066415148970332898259 31171599622723455499347389)
      ·
        refine ⟨11689349858521295812255271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31171599622723455499347389 11689349858521295812255271)
        ·
          refine ⟨17534024787781943718382907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689349858521295812255271 17534024787781943718382907)
          ·
            refine ⟨26301037181672915577574361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17534024787781943718382907 26301037181672915577574361)
            ·
              refine ⟨19725777886254686683180771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26301037181672915577574361 19725777886254686683180771)
              ·
                refine ⟨29588666829382030024771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19725777886254686683180771 29588666829382030024771157)
                ·
                  refine ⟨346742189406820664352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29588666829382030024771157 346742189406820664352787)
                  ·
                    rfl

theorem cell23_6077502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_6077502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077502 prefixEnd_6077502 := by exact prefixLift 6077502
  have htrace : WordTrace (prefixWord ++ tailWord_6077502) baseStart_6077502 baseEnd_6077502 := by
    simpa [prefixWord, tailWord_6077502, baseEnd_6077502] using wordTrace_append hprefix tailTrace_6077502
  have hstable : (prefixWord ++ tailWord_6077502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077502).length < 2 ^ (prefixWord ++ tailWord_6077502).sum := by decide
  have hdescent : baseEnd_6077502 < baseStart_6077502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077532 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6077532 : Nat := 118140960795 + 6077532 * 2 ^ 59
def prefixEnd_6077532 : Nat := 4983230072969 + 3 ^ 40 * 6077532 * 2
def baseEnd_6077532 : Nat := 1040231703027006953933315

theorem tailTrace_6077532 : CollatzResearch.WordTrace tailWord_6077532 prefixEnd_6077532 1040231703027006953933315 := by
  unfold tailWord_6077532
  simp only [CollatzResearch.WordTrace]
  refine ⟨110832901309073499337253425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147777201745431332449671233 110832901309073499337253425)
  ·
    refine ⟨83124675981805124502940069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110832901309073499337253425 83124675981805124502940069)
    ·
      refine ⟨15585876746588460844301263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83124675981805124502940069 15585876746588460844301263)
      ·
        refine ⟨23378815119882691266451895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585876746588460844301263 23378815119882691266451895)
        ·
          refine ⟨35068222679824036899677843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23378815119882691266451895 35068222679824036899677843)
          ·
            refine ⟨52602334019736055349516765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35068222679824036899677843 52602334019736055349516765)
            ·
              refine ⟨19725875257401020756068787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52602334019736055349516765 19725875257401020756068787)
              ·
                refine ⟨29588812886101531134103181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19725875257401020756068787 29588812886101531134103181)
                ·
                  refine ⟨11095804832288074175288693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29588812886101531134103181 11095804832288074175288693)
                  ·
                    refine ⟨1040231703027006953933315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11095804832288074175288693 1040231703027006953933315)
                    ·
                      rfl

theorem cell23_6077532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6077532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077532 prefixEnd_6077532 := by exact prefixLift 6077532
  have htrace : WordTrace (prefixWord ++ tailWord_6077532) baseStart_6077532 baseEnd_6077532 := by
    simpa [prefixWord, tailWord_6077532, baseEnd_6077532] using wordTrace_append hprefix tailTrace_6077532
  have hstable : (prefixWord ++ tailWord_6077532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077532).length < 2 ^ (prefixWord ++ tailWord_6077532).sum := by decide
  have hdescent : baseEnd_6077532 < baseStart_6077532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077545 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_6077545 : Nat := 118140960795 + 6077545 * 2 ^ 59
def prefixEnd_6077545 : Nat := 4983230072969 + 3 ^ 40 * 6077545 * 2
def baseEnd_6077545 : Nat := 1040233928109843103645795

theorem tailTrace_6077545 : CollatzResearch.WordTrace tailWord_6077545 prefixEnd_6077545 1040233928109843103645795 := by
  unfold tailWord_6077545
  simp only [CollatzResearch.WordTrace]
  refine ⟨221666276767099901894730089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147777517844733267929820059 221666276767099901894730089)
  ·
    refine ⟨166249707575324926421047567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221666276767099901894730089 166249707575324926421047567)
    ·
      refine ⟨249374561362987389631571351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166249707575324926421047567 249374561362987389631571351)
      ·
        refine ⟨374061842044481084447357027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249374561362987389631571351 374061842044481084447357027)
        ·
          refine ⟨561092763066721626671035541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374061842044481084447357027 561092763066721626671035541)
          ·
            refine ⟨26301223268752576250204791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 561092763066721626671035541 26301223268752576250204791)
            ·
              refine ⟨39451834903128864375307187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26301223268752576250204791 39451834903128864375307187)
              ·
                refine ⟨59177752354693296562960781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39451834903128864375307187 59177752354693296562960781)
                ·
                  refine ⟨22191657133009986211110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59177752354693296562960781 22191657133009986211110293)
                  ·
                    refine ⟨1040233928109843103645795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22191657133009986211110293 1040233928109843103645795)
                    ·
                      rfl

theorem cell23_6077545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_6077545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077545 prefixEnd_6077545 := by exact prefixLift 6077545
  have htrace : WordTrace (prefixWord ++ tailWord_6077545) baseStart_6077545 baseEnd_6077545 := by
    simpa [prefixWord, tailWord_6077545, baseEnd_6077545] using wordTrace_append hprefix tailTrace_6077545
  have hstable : (prefixWord ++ tailWord_6077545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077545).length < 2 ^ (prefixWord ++ tailWord_6077545).sum := by decide
  have hdescent : baseEnd_6077545 < baseStart_6077545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077557 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6077557 : Nat := 118140960795 + 6077557 * 2 ^ 59
def prefixEnd_6077557 : Nat := 4983230072969 + 3 ^ 40 * 6077557 * 2
def baseEnd_6077557 : Nat := 1040235982032461087995777

theorem tailTrace_6077557 : CollatzResearch.WordTrace tailWord_6077557 prefixEnd_6077557 1040235982032461087995777 := by
  unfold tailWord_6077557
  simp only [CollatzResearch.WordTrace]
  refine ⟨221666714443056427944166925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147777809628704285296111283 221666714443056427944166925)
  ·
    refine ⟨83125017916146160479062597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221666714443056427944166925 83125017916146160479062597)
    ·
      refine ⟨15585940859277405089824237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83125017916146160479062597 15585940859277405089824237)
      ·
        refine ⟨5844727822229026908684089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15585940859277405089824237 5844727822229026908684089)
        ·
          refine ⟨4383545866671770181513067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5844727822229026908684089 4383545866671770181513067)
          ·
            refine ⟨6575318800007655272269601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383545866671770181513067 6575318800007655272269601)
            ·
              refine ⟨4931489100005741454202201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575318800007655272269601 4931489100005741454202201)
              ·
                refine ⟨3698616825004306090651651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931489100005741454202201 3698616825004306090651651)
                ·
                  refine ⟨5547925237506459135977477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698616825004306090651651 5547925237506459135977477)
                  ·
                    refine ⟨1040235982032461087995777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547925237506459135977477 1040235982032461087995777)
                    ·
                      rfl

theorem cell23_6077557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6077557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077557 prefixEnd_6077557 := by exact prefixLift 6077557
  have htrace : WordTrace (prefixWord ++ tailWord_6077557) baseStart_6077557 baseEnd_6077557 := by
    simpa [prefixWord, tailWord_6077557, baseEnd_6077557] using wordTrace_append hprefix tailTrace_6077557
  have hstable : (prefixWord ++ tailWord_6077557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077557).length < 2 ^ (prefixWord ++ tailWord_6077557).sum := by decide
  have hdescent : baseEnd_6077557 < baseStart_6077557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077586 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6077586 : Nat := 118140960795 + 6077586 * 2 ^ 59
def prefixEnd_6077586 : Nat := 4983230072969 + 3 ^ 40 * 6077586 * 2
def baseEnd_6077586 : Nat := 3120722837036363650524697

theorem tailTrace_6077586 : CollatzResearch.WordTrace tailWord_6077586 prefixEnd_6077586 3120722837036363650524697 := by
  unfold tailWord_6077586
  simp only [CollatzResearch.WordTrace]
  refine ⟨55416943039987841474243153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147778514773300910597981741 55416943039987841474243153)
  ·
    refine ⟨41562707279990881105682365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55416943039987841474243153 41562707279990881105682365)
    ·
      refine ⟨15586015229996580414630887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41562707279990881105682365 15586015229996580414630887)
      ·
        refine ⟨23379022844994870621946331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15586015229996580414630887 23379022844994870621946331)
        ·
          refine ⟨35068534267492305932919497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23379022844994870621946331 35068534267492305932919497)
          ·
            refine ⟨26301400700619229449689623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35068534267492305932919497 26301400700619229449689623)
            ·
              refine ⟨39452101050928844174534435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26301400700619229449689623 39452101050928844174534435)
              ·
                refine ⟨59178151576393266261801653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39452101050928844174534435 59178151576393266261801653)
                ·
                  refine ⟨5547951710286868712043905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59178151576393266261801653 5547951710286868712043905)
                  ·
                    refine ⟨4160963782715151534032929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5547951710286868712043905 4160963782715151534032929)
                    ·
                      refine ⟨3120722837036363650524697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160963782715151534032929 3120722837036363650524697)
                      ·
                        rfl

theorem cell23_6077586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6077586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077586 prefixEnd_6077586 := by exact prefixLift 6077586
  have htrace : WordTrace (prefixWord ++ tailWord_6077586) baseStart_6077586 baseEnd_6077586 := by
    simpa [prefixWord, tailWord_6077586, baseEnd_6077586] using wordTrace_append hprefix tailTrace_6077586
  have hstable : (prefixWord ++ tailWord_6077586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077586).length < 2 ^ (prefixWord ++ tailWord_6077586).sum := by decide
  have hdescent : baseEnd_6077586 < baseStart_6077586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077613 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6077613 : Nat := 118140960795 + 6077613 * 2 ^ 59
def prefixEnd_6077613 : Nat := 4983230072969 + 3 ^ 40 * 6077613 * 2
def baseEnd_6077613 : Nat := 1040245567004678348295691

theorem tailTrace_6077613 : CollatzResearch.WordTrace tailWord_6077613 prefixEnd_6077613 1040245567004678348295691 := by
  unfold tailWord_6077613
  simp only [CollatzResearch.WordTrace]
  refine ⟨221668756930853549508205493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147779171287235699672136995 221668756930853549508205493)
  ·
    refine ⟨20781445962267520266394265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221668756930853549508205493 20781445962267520266394265)
    ·
      refine ⟨15586084471700640199795699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20781445962267520266394265 15586084471700640199795699)
      ·
        refine ⟨23379126707550960299693549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15586084471700640199795699 23379126707550960299693549)
        ·
          refine ⟨8767172515331610112385081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23379126707550960299693549 8767172515331610112385081)
          ·
            refine ⟨6575379386498707584288811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8767172515331610112385081 6575379386498707584288811)
            ·
              refine ⟨9863069079748061376433217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575379386498707584288811 9863069079748061376433217)
              ·
                refine ⟨7397301809811046032324913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9863069079748061376433217 7397301809811046032324913)
                ·
                  refine ⟨5547976357358284524243685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7397301809811046032324913 5547976357358284524243685)
                  ·
                    refine ⟨1040245567004678348295691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5547976357358284524243685 1040245567004678348295691)
                    ·
                      rfl

theorem cell23_6077613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6077613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077613 prefixEnd_6077613 := by exact prefixLift 6077613
  have htrace : WordTrace (prefixWord ++ tailWord_6077613) baseStart_6077613 baseEnd_6077613 := by
    simpa [prefixWord, tailWord_6077613, baseEnd_6077613] using wordTrace_append hprefix tailTrace_6077613
  have hstable : (prefixWord ++ tailWord_6077613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077613).length < 2 ^ (prefixWord ++ tailWord_6077613).sum := by decide
  have hdescent : baseEnd_6077613 < baseStart_6077613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077629 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_6077629 : Nat := 118140960795 + 6077629 * 2 ^ 59
def prefixEnd_6077629 : Nat := 4983230072969 + 3 ^ 40 * 6077629 * 2
def baseEnd_6077629 : Nat := 3120744916704506982286999

theorem tailTrace_6077629 : CollatzResearch.WordTrace tailWord_6077629 prefixEnd_6077629 3120744916704506982286999 := by
  unfold tailWord_6077629
  simp only [CollatzResearch.WordTrace]
  refine ⟨221669340498795584240787941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147779560332530389493858627 221669340498795584240787941)
  ·
    refine ⟨41563001343524172045147739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221669340498795584240787941 41563001343524172045147739)
    ·
      refine ⟨62344502015286258067721609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41563001343524172045147739 62344502015286258067721609)
      ·
        refine ⟨46758376511464693550791207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62344502015286258067721609 46758376511464693550791207)
        ·
          refine ⟨70137564767197040326186811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46758376511464693550791207 70137564767197040326186811)
          ·
            refine ⟨105206347150795560489280217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70137564767197040326186811 105206347150795560489280217)
            ·
              refine ⟨78904760363096670366960163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105206347150795560489280217 78904760363096670366960163)
              ·
                refine ⟨118357140544645005550440245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78904760363096670366960163 118357140544645005550440245)
                ·
                  refine ⟨11095981926060469270353773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118357140544645005550440245 11095981926060469270353773)
                  ·
                    refine ⟨4160993222272675976382665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11095981926060469270353773 4160993222272675976382665)
                    ·
                      refine ⟨3120744916704506982286999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4160993222272675976382665 3120744916704506982286999)
                      ·
                        rfl

theorem cell23_6077629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_6077629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077629 prefixEnd_6077629 := by exact prefixLift 6077629
  have htrace : WordTrace (prefixWord ++ tailWord_6077629) baseStart_6077629 baseEnd_6077629 := by
    simpa [prefixWord, tailWord_6077629, baseEnd_6077629] using wordTrace_append hprefix tailTrace_6077629
  have hstable : (prefixWord ++ tailWord_6077629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077629).length < 2 ^ (prefixWord ++ tailWord_6077629).sum := by decide
  have hdescent : baseEnd_6077629 < baseStart_6077629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077635 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 8]
def baseStart_6077635 : Nat := 118140960795 + 6077635 * 2 ^ 59
def prefixEnd_6077635 : Nat := 4983230072969 + 3 ^ 40 * 6077635 * 2
def baseEnd_6077635 : Nat := 1040249332529477986270657

theorem tailTrace_6077635 : CollatzResearch.WordTrace tailWord_6077635 prefixEnd_6077635 1040249332529477986270657 := by
  unfold tailWord_6077635
  simp only [CollatzResearch.WordTrace]
  refine ⟨221669559336773847265506359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147779706224515898177004239 221669559336773847265506359)
  ·
    refine ⟨332504339005160770898259539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221669559336773847265506359 332504339005160770898259539)
    ·
      refine ⟨498756508507741156347389309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332504339005160770898259539 498756508507741156347389309)
      ·
        refine ⟨187033690690402933630270991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498756508507741156347389309 187033690690402933630270991)
        ·
          refine ⟨280550536035604400445406487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187033690690402933630270991 280550536035604400445406487)
          ·
            refine ⟨420825804053406600668109731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280550536035604400445406487 420825804053406600668109731)
            ·
              refine ⟨631238706080109901002164597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420825804053406600668109731 631238706080109901002164597)
              ·
                refine ⟨59178628695010303218952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 631238706080109901002164597 59178628695010303218952931)
                ·
                  refine ⟨88767943042515454828429397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59178628695010303218952931 88767943042515454828429397)
                  ·
                    refine ⟨1040249332529477986270657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88767943042515454828429397 1040249332529477986270657)
                    ·
                      rfl

theorem cell23_6077635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_6077635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077635 prefixEnd_6077635 := by exact prefixLift 6077635
  have htrace : WordTrace (prefixWord ++ tailWord_6077635) baseStart_6077635 baseEnd_6077635 := by
    simpa [prefixWord, tailWord_6077635, baseEnd_6077635] using wordTrace_append hprefix tailTrace_6077635
  have hstable : (prefixWord ++ tailWord_6077635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077635).length < 2 ^ (prefixWord ++ tailWord_6077635).sum := by decide
  have hdescent : baseEnd_6077635 < baseStart_6077635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077654 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6077654 : Nat := 118140960795 + 6077654 * 2 ^ 59
def prefixEnd_6077654 : Nat := 4983230072969 + 3 ^ 40 * 6077654 * 2
def baseEnd_6077654 : Nat := 3120757753720869384474385

theorem tailTrace_6077654 : CollatzResearch.WordTrace tailWord_6077654 prefixEnd_6077654 3120757753720869384474385 := by
  unfold tailWord_6077654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13854390770231563344403001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147780168215803342340298677 13854390770231563344403001)
  ·
    refine ⟨10390793077673672508302251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13854390770231563344403001 10390793077673672508302251)
    ·
      refine ⟨15586189616510508762453377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390793077673672508302251 15586189616510508762453377)
      ·
        refine ⟨11689642212382881571840033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15586189616510508762453377 11689642212382881571840033)
        ·
          refine ⟨8767231659287161178880025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11689642212382881571840033 8767231659287161178880025)
          ·
            refine ⟨6575423744465370884160019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8767231659287161178880025 6575423744465370884160019)
            ·
              refine ⟨9863135616698056326240029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575423744465370884160019 9863135616698056326240029)
              ·
                refine ⟨3698675856261771122340011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9863135616698056326240029 3698675856261771122340011)
                ·
                  refine ⟨5548013784392656683510017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698675856261771122340011 5548013784392656683510017)
                  ·
                    refine ⟨4161010338294492512632513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548013784392656683510017 4161010338294492512632513)
                    ·
                      refine ⟨3120757753720869384474385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161010338294492512632513 3120757753720869384474385)
                      ·
                        rfl

theorem cell23_6077654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6077654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077654 prefixEnd_6077654 := by exact prefixLift 6077654
  have htrace : WordTrace (prefixWord ++ tailWord_6077654) baseStart_6077654 baseEnd_6077654 := by
    simpa [prefixWord, tailWord_6077654, baseEnd_6077654] using wordTrace_append hprefix tailTrace_6077654
  have hstable : (prefixWord ++ tailWord_6077654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077654).length < 2 ^ (prefixWord ++ tailWord_6077654).sum := by decide
  have hdescent : baseEnd_6077654 < baseStart_6077654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077676 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_6077676 : Nat := 118140960795 + 6077676 * 2 ^ 59
def prefixEnd_6077676 : Nat := 4983230072969 + 3 ^ 40 * 6077676 * 2
def baseEnd_6077676 : Nat := 3120769050295268298399283

theorem tailTrace_6077676 : CollatzResearch.WordTrace tailWord_6077676 prefixEnd_6077676 3120769050295268298399283 := by
  unfold tailWord_6077676
  simp only [CollatzResearch.WordTrace]
  refine ⟨110835527364812655633874441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147780703153083540845165921 110835527364812655633874441)
  ·
    refine ⟨83126645523609491725405831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110835527364812655633874441 83126645523609491725405831)
    ·
      refine ⟨124689968285414237588108747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83126645523609491725405831 124689968285414237588108747)
      ·
        refine ⟨187034952428121356382163121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124689968285414237588108747 187034952428121356382163121)
        ·
          refine ⟨140276214321091017286622341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187034952428121356382163121 140276214321091017286622341)
          ·
            refine ⟨26301790185204565741241689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140276214321091017286622341 26301790185204565741241689)
            ·
              refine ⟨19726342638903424305931267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26301790185204565741241689 19726342638903424305931267)
              ·
                refine ⟨29589513958355136458896901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19726342638903424305931267 29589513958355136458896901)
                ·
                  refine ⟨5548033867191588086043169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29589513958355136458896901 5548033867191588086043169)
                  ·
                    refine ⟨4161025400393691064532377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548033867191588086043169 4161025400393691064532377)
                    ·
                      refine ⟨3120769050295268298399283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161025400393691064532377 3120769050295268298399283)
                      ·
                        rfl

theorem cell23_6077676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_6077676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077676 prefixEnd_6077676 := by exact prefixLift 6077676
  have htrace : WordTrace (prefixWord ++ tailWord_6077676) baseStart_6077676 baseEnd_6077676 := by
    simpa [prefixWord, tailWord_6077676, baseEnd_6077676] using wordTrace_append hprefix tailTrace_6077676
  have hstable : (prefixWord ++ tailWord_6077676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077676).length < 2 ^ (prefixWord ++ tailWord_6077676).sum := by decide
  have hdescent : baseEnd_6077676 < baseStart_6077676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077733 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 5]
def baseStart_6077733 : Nat := 118140960795 + 6077733 * 2 ^ 59
def prefixEnd_6077733 : Nat := 4983230072969 + 3 ^ 40 * 6077733 * 2
def baseEnd_6077733 : Nat := 346755368743619397265169

theorem tailTrace_6077733 : CollatzResearch.WordTrace tailWord_6077733 prefixEnd_6077733 346755368743619397265169 := by
  unfold tailWord_6077733
  simp only [CollatzResearch.WordTrace]
  refine ⟨221673133690418810002573853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147782089126945873335049235 221673133690418810002573853)
  ·
    refine ⟨83127425133907053750965195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221673133690418810002573853 83127425133907053750965195)
    ·
      refine ⟨124691137700860580626447793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83127425133907053750965195 124691137700860580626447793)
      ·
        refine ⟨93518353275645435469835845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124691137700860580626447793 93518353275645435469835845)
        ·
          refine ⟨17534691239183519150594221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93518353275645435469835845 17534691239183519150594221)
          ·
            refine ⟨6575509214693819681472833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17534691239183519150594221 6575509214693819681472833)
            ·
              refine ⟨4931631911020364761104625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575509214693819681472833 4931631911020364761104625)
              ·
                refine ⟨3698723933265273570828469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931631911020364761104625 3698723933265273570828469)
                ·
                  refine ⟨346755368743619397265169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3698723933265273570828469 346755368743619397265169)
                  ·
                    rfl

theorem cell23_6077733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_6077733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077733 prefixEnd_6077733 := by exact prefixLift 6077733
  have htrace : WordTrace (prefixWord ++ tailWord_6077733) baseStart_6077733 baseEnd_6077733 := by
    simpa [prefixWord, tailWord_6077733, baseEnd_6077733] using wordTrace_append hprefix tailTrace_6077733
  have hstable : (prefixWord ++ tailWord_6077733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077733).length < 2 ^ (prefixWord ++ tailWord_6077733).sum := by decide
  have hdescent : baseEnd_6077733 < baseStart_6077733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077736 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6077736 : Nat := 118140960795 + 6077736 * 2 ^ 59
def prefixEnd_6077736 : Nat := 4983230072969 + 3 ^ 40 * 6077736 * 2
def baseEnd_6077736 : Nat := 3120799859134538063649007

theorem tailTrace_6077736 : CollatzResearch.WordTrace tailWord_6077736 prefixEnd_6077736 3120799859134538063649007 := by
  unfold tailWord_6077736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110836621554703970757466531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147782162072938627676622041 110836621554703970757466531)
  ·
    refine ⟨166254932332055956136199797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110836621554703970757466531 166254932332055956136199797)
    ·
      refine ⟨15586399906130245887768731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166254932332055956136199797 15586399906130245887768731)
      ·
        refine ⟨23379599859195368831653097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15586399906130245887768731 23379599859195368831653097)
        ·
          refine ⟨17534699894396526623739823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23379599859195368831653097 17534699894396526623739823)
          ·
            refine ⟨26302049841594789935609735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17534699894396526623739823 26302049841594789935609735)
            ·
              refine ⟨39453074762392184903414603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26302049841594789935609735 39453074762392184903414603)
              ·
                refine ⟨59179612143588277355121905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39453074762392184903414603 59179612143588277355121905)
                ·
                  refine ⟨44384709107691208016341429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59179612143588277355121905 44384709107691208016341429)
                  ·
                    refine ⟨4161066478846050751532009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44384709107691208016341429 4161066478846050751532009)
                    ·
                      refine ⟨3120799859134538063649007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161066478846050751532009 3120799859134538063649007)
                      ·
                        rfl

theorem cell23_6077736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6077736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077736 prefixEnd_6077736 := by exact prefixLift 6077736
  have htrace : WordTrace (prefixWord ++ tailWord_6077736) baseStart_6077736 baseEnd_6077736 := by
    simpa [prefixWord, tailWord_6077736, baseEnd_6077736] using wordTrace_append hprefix tailTrace_6077736
  have hstable : (prefixWord ++ tailWord_6077736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077736).length < 2 ^ (prefixWord ++ tailWord_6077736).sum := by decide
  have hdescent : baseEnd_6077736 < baseStart_6077736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077759 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 5, 4]
def baseStart_6077759 : Nat := 118140960795 + 6077759 * 2 ^ 59
def prefixEnd_6077759 : Nat := 4983230072969 + 3 ^ 40 * 6077759 * 2
def baseEnd_6077759 : Nat := 1040270556396530491220467

theorem tailTrace_6077759 : CollatzResearch.WordTrace tailWord_6077759 prefixEnd_6077759 1040270556396530491220467 := by
  unfold tailWord_6077759
  simp only [CollatzResearch.WordTrace]
  refine ⟨221674081988324616443020331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147782721325549744295346887 221674081988324616443020331)
  ·
    refine ⟨332511122982486924664530497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221674081988324616443020331 332511122982486924664530497)
    ·
      refine ⟨249383342236865193498397873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332511122982486924664530497 249383342236865193498397873)
      ·
        refine ⟨187037506677648895123798405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249383342236865193498397873 187037506677648895123798405)
        ·
          refine ⟨35069532502059167835712201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187037506677648895123798405 35069532502059167835712201)
          ·
            refine ⟨26302149376544375876784151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35069532502059167835712201 26302149376544375876784151)
            ·
              refine ⟨39453224064816563815176227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26302149376544375876784151 39453224064816563815176227)
              ·
                refine ⟨59179836097224845722764341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39453224064816563815176227 59179836097224845722764341)
                ·
                  refine ⟨5548109634114829286509157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59179836097224845722764341 5548109634114829286509157)
                  ·
                    refine ⟨1040270556396530491220467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548109634114829286509157 1040270556396530491220467)
                    ·
                      rfl

theorem cell23_6077759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_6077759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077759 prefixEnd_6077759 := by exact prefixLift 6077759
  have htrace : WordTrace (prefixWord ++ tailWord_6077759) baseStart_6077759 baseEnd_6077759 := by
    simpa [prefixWord, tailWord_6077759, baseEnd_6077759] using wordTrace_append hprefix tailTrace_6077759
  have hstable : (prefixWord ++ tailWord_6077759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077759).length < 2 ^ (prefixWord ++ tailWord_6077759).sum := by decide
  have hdescent : baseEnd_6077759 < baseStart_6077759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077859 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_6077859 : Nat := 118140960795 + 6077859 * 2 ^ 59
def prefixEnd_6077859 : Nat := 4983230072969 + 3 ^ 40 * 6077859 * 2
def baseEnd_6077859 : Nat := 3120863017255041082410941

theorem tailTrace_6077859 : CollatzResearch.WordTrace tailWord_6077859 prefixEnd_6077859 3120863017255041082410941 := by
  unfold tailWord_6077859
  simp only [CollatzResearch.WordTrace]
  refine ⟨221677729287962333521660631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147785152858641555681107087 221677729287962333521660631)
  ·
    refine ⟨332516593931943500282490947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221677729287962333521660631 332516593931943500282490947)
    ·
      refine ⟨498774890897915250423736421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332516593931943500282490947 498774890897915250423736421)
      ·
        refine ⟨93520292043359109454450579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498774890897915250423736421 93520292043359109454450579)
        ·
          refine ⟨140280438065038664181675869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93520292043359109454450579 140280438065038664181675869)
          ·
            refine ⟨52605164274389499068128451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140280438065038664181675869 52605164274389499068128451)
            ·
              refine ⟨78907746411584248602192677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52605164274389499068128451 78907746411584248602192677)
              ·
                refine ⟨14795202452172046612911127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78907746411584248602192677 14795202452172046612911127)
                ·
                  refine ⟨22192803678258069919366691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14795202452172046612911127 22192803678258069919366691)
                  ·
                    refine ⟨33289205517387104879050037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22192803678258069919366691 33289205517387104879050037)
                    ·
                      refine ⟨3120863017255041082410941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33289205517387104879050037 3120863017255041082410941)
                      ·
                        rfl

theorem cell23_6077859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_6077859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077859 prefixEnd_6077859 := by exact prefixLift 6077859
  have htrace : WordTrace (prefixWord ++ tailWord_6077859) baseStart_6077859 baseEnd_6077859 := by
    simpa [prefixWord, tailWord_6077859, baseEnd_6077859] using wordTrace_append hprefix tailTrace_6077859
  have hstable : (prefixWord ++ tailWord_6077859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077859).length < 2 ^ (prefixWord ++ tailWord_6077859).sum := by decide
  have hdescent : baseEnd_6077859 < baseStart_6077859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077873 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6077873 : Nat := 118140960795 + 6077873 * 2 ^ 59
def prefixEnd_6077873 : Nat := 4983230072969 + 3 ^ 40 * 6077873 * 2
def baseEnd_6077873 : Nat := 3120870205984204027635877

theorem tailTrace_6077873 : CollatzResearch.WordTrace tailWord_6077873 prefixEnd_6077873 3120870205984204027635877 := by
  unfold tailWord_6077873
  simp only [CollatzResearch.WordTrace]
  refine ⟨221678239909911613912670273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147785493273274409275113515 221678239909911613912670273)
  ·
    refine ⟨166258679932433710434502705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221678239909911613912670273 166258679932433710434502705)
    ·
      refine ⟨124694009949325282825877029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166258679932433710434502705 124694009949325282825877029)
      ·
        refine ⟨23380126865498490529851943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124694009949325282825877029 23380126865498490529851943)
        ·
          refine ⟨35070190298247735794777915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23380126865498490529851943 35070190298247735794777915)
          ·
            refine ⟨52605285447371603692166873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35070190298247735794777915 52605285447371603692166873)
            ·
              refine ⟨39453964085528702769125155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52605285447371603692166873 39453964085528702769125155)
              ·
                refine ⟨59180946128293054153687733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39453964085528702769125155 59180946128293054153687733)
                ·
                  refine ⟨5548213699527473826908225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59180946128293054153687733 5548213699527473826908225)
                  ·
                    refine ⟨4161160274645605370181169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548213699527473826908225 4161160274645605370181169)
                    ·
                      refine ⟨3120870205984204027635877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161160274645605370181169 3120870205984204027635877)
                      ·
                        rfl

theorem cell23_6077873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6077873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077873 prefixEnd_6077873 := by exact prefixLift 6077873
  have htrace : WordTrace (prefixWord ++ tailWord_6077873) baseStart_6077873 baseEnd_6077873 := by
    simpa [prefixWord, tailWord_6077873, baseEnd_6077873] using wordTrace_append hprefix tailTrace_6077873
  have hstable : (prefixWord ++ tailWord_6077873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077873).length < 2 ^ (prefixWord ++ tailWord_6077873).sum := by decide
  have hdescent : baseEnd_6077873 < baseStart_6077873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077909 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_6077909 : Nat := 118140960795 + 6077909 * 2 ^ 59
def prefixEnd_6077909 : Nat := 4983230072969 + 3 ^ 40 * 6077909 * 2
def baseEnd_6077909 : Nat := 1040296230429255295595237

theorem tailTrace_6077909 : CollatzResearch.WordTrace tailWord_6077909 prefixEnd_6077909 1040296230429255295595237 := by
  unfold tailWord_6077909
  simp only [CollatzResearch.WordTrace]
  refine ⟨221679552937781192060980781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147786368625187461373987187 221679552937781192060980781)
  ·
    refine ⟨83129832351667947022867793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221679552937781192060980781 83129832351667947022867793)
    ·
      refine ⟨62347374263750960267150845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83129832351667947022867793 62347374263750960267150845)
      ·
        refine ⟨23380265348906610100181567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62347374263750960267150845 23380265348906610100181567)
        ·
          refine ⟨35070398023359915150272351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23380265348906610100181567 35070398023359915150272351)
          ·
            refine ⟨52605597035039872725408527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35070398023359915150272351 52605597035039872725408527)
            ·
              refine ⟨78908395552559809088112791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52605597035039872725408527 78908395552559809088112791)
              ·
                refine ⟨118362593328839713632169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78908395552559809088112791 118362593328839713632169187)
                ·
                  refine ⟨177543889993259570448253781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118362593328839713632169187 177543889993259570448253781)
                  ·
                    refine ⟨1040296230429255295595237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177543889993259570448253781 1040296230429255295595237)
                    ·
                      rfl

theorem cell23_6077909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_6077909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077909 prefixEnd_6077909 := by exact prefixLift 6077909
  have htrace : WordTrace (prefixWord ++ tailWord_6077909) baseStart_6077909 baseEnd_6077909 := by
    simpa [prefixWord, tailWord_6077909, baseEnd_6077909] using wordTrace_append hprefix tailTrace_6077909
  have hstable : (prefixWord ++ tailWord_6077909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077909).length < 2 ^ (prefixWord ++ tailWord_6077909).sum := by decide
  have hdescent : baseEnd_6077909 < baseStart_6077909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077923 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6077923 : Nat := 118140960795 + 6077923 * 2 ^ 59
def prefixEnd_6077923 : Nat := 4983230072969 + 3 ^ 40 * 6077923 * 2
def baseEnd_6077923 : Nat := 3120895880016928832010647

theorem tailTrace_6077923 : CollatzResearch.WordTrace tailWord_6077923 prefixEnd_6077923 3120895880016928832010647 := by
  unfold tailWord_6077923
  simp only [CollatzResearch.WordTrace]
  refine ⟨221680063559730472451990423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147786709039820314967993615 221680063559730472451990423)
  ·
    refine ⟨332520095339595708677985635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221680063559730472451990423 332520095339595708677985635)
    ·
      refine ⟨498780143009393563016978453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332520095339595708677985635 498780143009393563016978453)
      ·
        refine ⟨23380319203565323266420865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 498780143009393563016978453 23380319203565323266420865)
        ·
          refine ⟨17535239402673992449815649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23380319203565323266420865 17535239402673992449815649)
          ·
            refine ⟨13151429552005494337361737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17535239402673992449815649 13151429552005494337361737)
            ·
              refine ⟨9863572164004120753021303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13151429552005494337361737 9863572164004120753021303)
              ·
                refine ⟨14795358246006181129531955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9863572164004120753021303 14795358246006181129531955)
                ·
                  refine ⟨22193037369009271694297933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14795358246006181129531955 22193037369009271694297933)
                  ·
                    refine ⟨8322389013378476885361725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22193037369009271694297933 8322389013378476885361725)
                    ·
                      refine ⟨3120895880016928832010647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8322389013378476885361725 3120895880016928832010647)
                      ·
                        rfl

theorem cell23_6077923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6077923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077923 prefixEnd_6077923 := by exact prefixLift 6077923
  have htrace : WordTrace (prefixWord ++ tailWord_6077923) baseStart_6077923 baseEnd_6077923 := by
    simpa [prefixWord, tailWord_6077923, baseEnd_6077923] using wordTrace_append hprefix tailTrace_6077923
  have hstable : (prefixWord ++ tailWord_6077923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077923).length < 2 ^ (prefixWord ++ tailWord_6077923).sum := by decide
  have hdescent : baseEnd_6077923 < baseStart_6077923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6077986 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_6077986 : Nat := 118140960795 + 6077986 * 2 ^ 59
def prefixEnd_6077986 : Nat := 4983230072969 + 3 ^ 40 * 6077986 * 2
def baseEnd_6077986 : Nat := 346769803255351342835873

theorem tailTrace_6077986 : CollatzResearch.WordTrace tailWord_6077986 prefixEnd_6077986 346769803255351342835873 := by
  unfold tailWord_6077986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55420590339625558552883453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147788240905668156141022541 55420590339625558552883453)
  ·
    refine ⟨20782721377359584457331295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55420590339625558552883453 20782721377359584457331295)
    ·
      refine ⟨31174082066039376685996943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20782721377359584457331295 31174082066039376685996943)
      ·
        refine ⟨46761123099059065028995415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31174082066039376685996943 46761123099059065028995415)
        ·
          refine ⟨70141684648588597543493123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46761123099059065028995415 70141684648588597543493123)
          ·
            refine ⟨105212526972882896315239685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70141684648588597543493123 105212526972882896315239685)
            ·
              refine ⟨19727348807415543059107441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105212526972882896315239685 19727348807415543059107441)
              ·
                refine ⟨14795511605561657294330581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19727348807415543059107441 14795511605561657294330581)
                ·
                  refine ⟨346769803255351342835873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14795511605561657294330581 346769803255351342835873)
                  ·
                    rfl

theorem cell23_6077986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_6077986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6077986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6077986 prefixEnd_6077986 := by exact prefixLift 6077986
  have htrace : WordTrace (prefixWord ++ tailWord_6077986) baseStart_6077986 baseEnd_6077986 := by
    simpa [prefixWord, tailWord_6077986, baseEnd_6077986] using wordTrace_append hprefix tailTrace_6077986
  have hstable : (prefixWord ++ tailWord_6077986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6077986).length < 2 ^ (prefixWord ++ tailWord_6077986).sum := by decide
  have hdescent : baseEnd_6077986 < baseStart_6077986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6077986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078003 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 5]
def baseStart_6078003 : Nat := 118140960795 + 6078003 * 2 ^ 59
def prefixEnd_6078003 : Nat := 4983230072969 + 3 ^ 40 * 6078003 * 2
def baseEnd_6078003 : Nat := 346770773163254279890031

theorem tailTrace_6078003 : CollatzResearch.WordTrace tailWord_6078003 prefixEnd_6078003 346770773163254279890031 := by
  unfold tailWord_6078003
  simp only [CollatzResearch.WordTrace]
  refine ⟨221682981399440646114902663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147788654266293764076601775 221682981399440646114902663)
  ·
    refine ⟨332524472099160969172353995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221682981399440646114902663 332524472099160969172353995)
    ·
      refine ⟨498786708148741453758530993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332524472099160969172353995 498786708148741453758530993)
      ·
        refine ⟨374090031111556090318898245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498786708148741453758530993 374090031111556090318898245)
        ·
          refine ⟨70141880833416766934793421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374090031111556090318898245 70141880833416766934793421)
          ·
            refine ⟨26303205312531287600547533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70141880833416766934793421 26303205312531287600547533)
            ·
              refine ⟨9863701992199232850205325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26303205312531287600547533 9863701992199232850205325)
              ·
                refine ⟨3698888247074712318826997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9863701992199232850205325 3698888247074712318826997)
                ·
                  refine ⟨346770773163254279890031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3698888247074712318826997 346770773163254279890031)
                  ·
                    rfl

theorem cell23_6078003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 5].length) (baseStart_6078003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078003 prefixEnd_6078003 := by exact prefixLift 6078003
  have htrace : WordTrace (prefixWord ++ tailWord_6078003) baseStart_6078003 baseEnd_6078003 := by
    simpa [prefixWord, tailWord_6078003, baseEnd_6078003] using wordTrace_append hprefix tailTrace_6078003
  have hstable : (prefixWord ++ tailWord_6078003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078003).length < 2 ^ (prefixWord ++ tailWord_6078003).sum := by decide
  have hdescent : baseEnd_6078003 < baseStart_6078003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_6078019 : Nat := 118140960795 + 6078019 * 2 ^ 59
def prefixEnd_6078019 : Nat := 4983230072969 + 3 ^ 40 * 6078019 * 2
def baseEnd_6078019 : Nat := 3120945174159760456410205

theorem tailTrace_6078019 : CollatzResearch.WordTrace tailWord_6078019 prefixEnd_6078019 3120945174159760456410205 := by
  unfold tailWord_6078019
  simp only [CollatzResearch.WordTrace]
  refine ⟨221683564967382680847485111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147789043311588453898323407 221683564967382680847485111)
  ·
    refine ⟨332525347451074021271227667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221683564967382680847485111 332525347451074021271227667)
    ·
      refine ⟨498788021176611031906841501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332525347451074021271227667 498788021176611031906841501)
      ·
        refine ⟨187045507941229136965065563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498788021176611031906841501 187045507941229136965065563)
        ·
          refine ⟨280568261911843705447598345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187045507941229136965065563 280568261911843705447598345)
          ·
            refine ⟨210426196433882779085698759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280568261911843705447598345 210426196433882779085698759)
            ·
              refine ⟨315639294650824168628548139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210426196433882779085698759 315639294650824168628548139)
              ·
                refine ⟨473458941976236252942822209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315639294650824168628548139 473458941976236252942822209)
                ·
                  refine ⟨355094206482177189707116657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473458941976236252942822209 355094206482177189707116657)
                  ·
                    refine ⟨266320654861632892280337493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355094206482177189707116657 266320654861632892280337493)
                    ·
                      refine ⟨3120945174159760456410205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266320654861632892280337493 3120945174159760456410205)
                      ·
                        rfl

theorem cell23_6078019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_6078019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078019 prefixEnd_6078019 := by exact prefixLift 6078019
  have htrace : WordTrace (prefixWord ++ tailWord_6078019) baseStart_6078019 baseEnd_6078019 := by
    simpa [prefixWord, tailWord_6078019, baseEnd_6078019] using wordTrace_append hprefix tailTrace_6078019
  have hstable : (prefixWord ++ tailWord_6078019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078019).length < 2 ^ (prefixWord ++ tailWord_6078019).sum := by decide
  have hdescent : baseEnd_6078019 < baseStart_6078019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078026 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6078026 : Nat := 118140960795 + 6078026 * 2 ^ 59
def prefixEnd_6078026 : Nat := 4983230072969 + 3 ^ 40 * 6078026 * 2
def baseEnd_6078026 : Nat := 3120948768524341929022673

theorem tailTrace_6078026 : CollatzResearch.WordTrace tailWord_6078026 prefixEnd_6078026 3120948768524341929022673 := by
  unfold tailWord_6078026
  simp only [CollatzResearch.WordTrace]
  refine ⟨55420955069589330260747483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147789213518904880695326621 55420955069589330260747483)
  ·
    refine ⟨83131432604383995391121225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55420955069589330260747483 83131432604383995391121225)
    ·
      refine ⟨62348574453287996543340919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83131432604383995391121225 62348574453287996543340919)
      ·
        refine ⟨93522861679931994815011379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62348574453287996543340919 93522861679931994815011379)
        ·
          refine ⟨140284292519897992222517069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93522861679931994815011379 140284292519897992222517069)
          ·
            refine ⟨52606609694961747083443901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140284292519897992222517069 52606609694961747083443901)
            ·
              refine ⟨19727478635610655156291463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52606609694961747083443901 19727478635610655156291463)
              ·
                refine ⟨29591217953415982734437195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19727478635610655156291463 29591217953415982734437195)
                ·
                  refine ⟨44386826930123974101655793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29591217953415982734437195 44386826930123974101655793)
                  ·
                    refine ⟨33290120197592980576241845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44386826930123974101655793 33290120197592980576241845)
                    ·
                      refine ⟨3120948768524341929022673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33290120197592980576241845 3120948768524341929022673)
                      ·
                        rfl

theorem cell23_6078026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6078026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078026 prefixEnd_6078026 := by exact prefixLift 6078026
  have htrace : WordTrace (prefixWord ++ tailWord_6078026) baseStart_6078026 baseEnd_6078026 := by
    simpa [prefixWord, tailWord_6078026, baseEnd_6078026] using wordTrace_append hprefix tailTrace_6078026
  have hstable : (prefixWord ++ tailWord_6078026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078026).length < 2 ^ (prefixWord ++ tailWord_6078026).sum := by decide
  have hdescent : baseEnd_6078026 < baseStart_6078026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078053 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6078053 : Nat := 118140960795 + 6078053 * 2 ^ 59
def prefixEnd_6078053 : Nat := 4983230072969 + 3 ^ 40 * 6078053 * 2
def baseEnd_6078053 : Nat := 3120962632502013323385049

theorem tailTrace_6078053 : CollatzResearch.WordTrace tailWord_6078053 prefixEnd_6078053 3120962632502013323385049 := by
  unfold tailWord_6078053
  simp only [CollatzResearch.WordTrace]
  refine ⟨221684805049259504654222813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147789870032839669769481875 221684805049259504654222813)
  ·
    refine ⟨83131801893472314245333555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221684805049259504654222813 83131801893472314245333555)
    ·
      refine ⟨124697702840208471368000333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83131801893472314245333555 124697702840208471368000333)
      ·
        refine ⟨46761638565078176763000125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124697702840208471368000333 46761638565078176763000125)
        ·
          refine ⟨17535614461904316286125047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46761638565078176763000125 17535614461904316286125047)
          ·
            refine ⟨26303421692856474429187571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535614461904316286125047 26303421692856474429187571)
            ·
              refine ⟨39455132539284711643781357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26303421692856474429187571 39455132539284711643781357)
              ·
                refine ⟨14795674702231766866418009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39455132539284711643781357 14795674702231766866418009)
                ·
                  refine ⟨11096756026673825149813507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795674702231766866418009 11096756026673825149813507)
                  ·
                    refine ⟨16645134040010737724720261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11096756026673825149813507 16645134040010737724720261)
                    ·
                      refine ⟨3120962632502013323385049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16645134040010737724720261 3120962632502013323385049)
                      ·
                        rfl

theorem cell23_6078053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6078053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078053 prefixEnd_6078053 := by exact prefixLift 6078053
  have htrace : WordTrace (prefixWord ++ tailWord_6078053) baseStart_6078053 baseEnd_6078053 := by
    simpa [prefixWord, tailWord_6078053, baseEnd_6078053] using wordTrace_append hprefix tailTrace_6078053
  have hstable : (prefixWord ++ tailWord_6078053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078053).length < 2 ^ (prefixWord ++ tailWord_6078053).sum := by decide
  have hdescent : baseEnd_6078053 < baseStart_6078053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078070 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6078070 : Nat := 118140960795 + 6078070 * 2 ^ 59
def prefixEnd_6078070 : Nat := 4983230072969 + 3 ^ 40 * 6078070 * 2
def baseEnd_6078070 : Nat := 3120971361673139756872471

theorem tailTrace_6078070 : CollatzResearch.WordTrace tailWord_6078070 prefixEnd_6078070 3120971361673139756872471 := by
  unfold tailWord_6078070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855339068137369784849479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147790283393465277705061109 13855339068137369784849479)
  ·
    refine ⟨20783008602206054677274219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855339068137369784849479 20783008602206054677274219)
    ·
      refine ⟨31174512903309082015911329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20783008602206054677274219 31174512903309082015911329)
      ·
        refine ⟨23380884677481811511933497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31174512903309082015911329 23380884677481811511933497)
        ·
          refine ⟨17535663508111358633950123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23380884677481811511933497 17535663508111358633950123)
          ·
            refine ⟨26303495262167037950925185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535663508111358633950123 26303495262167037950925185)
            ·
              refine ⟨19727621446625278463193889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26303495262167037950925185 19727621446625278463193889)
              ·
                refine ⟨14795716084968958847395417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19727621446625278463193889 14795716084968958847395417)
                ·
                  refine ⟨11096787063726719135546563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795716084968958847395417 11096787063726719135546563)
                  ·
                    refine ⟨16645180595590078703319845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11096787063726719135546563 16645180595590078703319845)
                    ·
                      refine ⟨3120971361673139756872471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16645180595590078703319845 3120971361673139756872471)
                      ·
                        rfl

theorem cell23_6078070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6078070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078070 prefixEnd_6078070 := by exact prefixLift 6078070
  have htrace : WordTrace (prefixWord ++ tailWord_6078070) baseStart_6078070 baseEnd_6078070 := by
    simpa [prefixWord, tailWord_6078070, baseEnd_6078070] using wordTrace_append hprefix tailTrace_6078070
  have hstable : (prefixWord ++ tailWord_6078070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078070).length < 2 ^ (prefixWord ++ tailWord_6078070).sum := by decide
  have hdescent : baseEnd_6078070 < baseStart_6078070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078073 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_6078073 : Nat := 118140960795 + 6078073 * 2 ^ 59
def prefixEnd_6078073 : Nat := 4983230072969 + 3 ^ 40 * 6078073 * 2
def baseEnd_6078073 : Nat := 3120972902115103245134957

theorem tailTrace_6078073 : CollatzResearch.WordTrace tailWord_6078073 prefixEnd_6078073 3120972902115103245134957 := by
  unfold tailWord_6078073
  simp only [CollatzResearch.WordTrace]
  refine ⟨221685534509187048069950873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147790356339458032046633915 221685534509187048069950873)
  ·
    refine ⟨166264150881890286052463155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221685534509187048069950873 166264150881890286052463155)
    ·
      refine ⟨249396226322835429078694733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166264150881890286052463155 249396226322835429078694733)
      ·
        refine ⟨93523584871063285904510525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249396226322835429078694733 93523584871063285904510525)
        ·
          refine ⟨35071344326648732214191447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93523584871063285904510525 35071344326648732214191447)
          ·
            refine ⟨52607016489973098321287171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35071344326648732214191447 52607016489973098321287171)
            ·
              refine ⟨78910524734959647481930757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52607016489973098321287171 78910524734959647481930757)
              ·
                refine ⟨14795723387804933902862017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78910524734959647481930757 14795723387804933902862017)
                ·
                  refine ⟨11096792540853700427146513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795723387804933902862017 11096792540853700427146513)
                  ·
                    refine ⟨8322594405640275320359885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11096792540853700427146513 8322594405640275320359885)
                    ·
                      refine ⟨3120972902115103245134957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8322594405640275320359885 3120972902115103245134957)
                      ·
                        rfl

theorem cell23_6078073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_6078073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078073 prefixEnd_6078073 := by exact prefixLift 6078073
  have htrace : WordTrace (prefixWord ++ tailWord_6078073) baseStart_6078073 baseEnd_6078073 := by
    simpa [prefixWord, tailWord_6078073, baseEnd_6078073] using wordTrace_append hprefix tailTrace_6078073
  have hstable : (prefixWord ++ tailWord_6078073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078073).length < 2 ^ (prefixWord ++ tailWord_6078073).sum := by decide
  have hdescent : baseEnd_6078073 < baseStart_6078073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078080 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 1, 4]
def baseStart_6078080 : Nat := 118140960795 + 6078080 * 2 ^ 59
def prefixEnd_6078080 : Nat := 4983230072969 + 3 ^ 40 * 6078080 * 2
def baseEnd_6078080 : Nat := 1040325498826561572582475

theorem tailTrace_6078080 : CollatzResearch.WordTrace tailWord_6078080 prefixEnd_6078080 1040325498826561572582475 := by
  unfold tailWord_6078080
  simp only [CollatzResearch.WordTrace]
  refine ⟨110842894910080844132727847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147790526546774458843637129 110842894910080844132727847)
  ·
    refine ⟨166264342365121266199091771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110842894910080844132727847 166264342365121266199091771)
    ·
      refine ⟨249396513547681899298637657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166264342365121266199091771 249396513547681899298637657)
      ·
        refine ⟨187047385160761424473978243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249396513547681899298637657 187047385160761424473978243)
        ·
          refine ⟨280571077741142136710967365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187047385160761424473978243 280571077741142136710967365)
          ·
            refine ⟨52607077076464150633306381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280571077741142136710967365 52607077076464150633306381)
            ·
              refine ⟨19727653903674056487489893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52607077076464150633306381 19727653903674056487489893)
              ·
                refine ⟨3698935106938885591404355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19727653903674056487489893 3698935106938885591404355)
                ·
                  refine ⟨5548402660408328387106533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698935106938885591404355 5548402660408328387106533)
                  ·
                    refine ⟨1040325498826561572582475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548402660408328387106533 1040325498826561572582475)
                    ·
                      rfl

theorem cell23_6078080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_6078080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078080 prefixEnd_6078080 := by exact prefixLift 6078080
  have htrace : WordTrace (prefixWord ++ tailWord_6078080) baseStart_6078080 baseEnd_6078080 := by
    simpa [prefixWord, tailWord_6078080, baseEnd_6078080] using wordTrace_append hprefix tailTrace_6078080
  have hstable : (prefixWord ++ tailWord_6078080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078080).length < 2 ^ (prefixWord ++ tailWord_6078080).sum := by decide
  have hdescent : baseEnd_6078080 < baseStart_6078080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078130 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_6078130 : Nat := 118140960795 + 6078130 * 2 ^ 59
def prefixEnd_6078130 : Nat := 4983230072969 + 3 ^ 40 * 6078130 * 2
def baseEnd_6078130 : Nat := 3121002170512409522122195

theorem tailTrace_6078130 : CollatzResearch.WordTrace tailWord_6078130 prefixEnd_6078130 3121002170512409522122195 := by
  unfold tailWord_6078130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55421903367495136701193961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147791742313320364536517229 55421903367495136701193961)
  ·
    refine ⟨41566427525621352525895471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55421903367495136701193961 41566427525621352525895471)
    ·
      refine ⟨62349641288432028788843207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41566427525621352525895471 62349641288432028788843207)
      ·
        refine ⟨93524461932648043183264811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62349641288432028788843207 93524461932648043183264811)
        ·
          refine ⟨140286692898972064774897217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93524461932648043183264811 140286692898972064774897217)
          ·
            refine ⟨105215019674229048581172913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140286692898972064774897217 105215019674229048581172913)
            ·
              refine ⟨78911264755671786435879685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105215019674229048581172913 78911264755671786435879685)
              ·
                refine ⟨14795862141688459956727441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78911264755671786435879685 14795862141688459956727441)
                ·
                  refine ⟨11096896606266344967545581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795862141688459956727441 11096896606266344967545581)
                  ·
                    refine ⟨4161336227349879362829593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11096896606266344967545581 4161336227349879362829593)
                    ·
                      refine ⟨3121002170512409522122195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161336227349879362829593 3121002170512409522122195)
                      ·
                        rfl

theorem cell23_6078130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_6078130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078130 prefixEnd_6078130 := by exact prefixLift 6078130
  have htrace : WordTrace (prefixWord ++ tailWord_6078130) baseStart_6078130 baseEnd_6078130 := by
    simpa [prefixWord, tailWord_6078130, baseEnd_6078130] using wordTrace_append hprefix tailTrace_6078130
  have hstable : (prefixWord ++ tailWord_6078130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078130).length < 2 ^ (prefixWord ++ tailWord_6078130).sum := by decide
  have hdescent : baseEnd_6078130 < baseStart_6078130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078136 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_6078136 : Nat := 118140960795 + 6078136 * 2 ^ 59
def prefixEnd_6078136 : Nat := 4983230072969 + 3 ^ 40 * 6078136 * 2
def baseEnd_6078136 : Nat := 1040335083798778832882389

theorem tailTrace_6078136 : CollatzResearch.WordTrace tailWord_6078136 prefixEnd_6078136 1040335083798778832882389 := by
  unfold tailWord_6078136
  simp only [CollatzResearch.WordTrace]
  refine ⟨110843916153979404914747131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147791888205305873219662841 110843916153979404914747131)
  ·
    refine ⟨166265874230969107372120697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110843916153979404914747131 166265874230969107372120697)
    ·
      refine ⟨124699405673226830529090523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166265874230969107372120697 124699405673226830529090523)
      ·
        refine ⟨187049108509840245793635785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124699405673226830529090523 187049108509840245793635785)
        ·
          refine ⟨140286831382380184345226839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187049108509840245793635785 140286831382380184345226839)
          ·
            refine ⟨210430247073570276517840259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140286831382380184345226839 210430247073570276517840259)
            ·
              refine ⟨315645370610355414776760389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210430247073570276517840259 315645370610355414776760389)
              ·
                refine ⟨59183506989441640270642573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315645370610355414776760389 59183506989441640270642573)
                ·
                  refine ⟨22193815121040615101490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59183506989441640270642573 22193815121040615101490965)
                  ·
                    refine ⟨1040335083798778832882389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22193815121040615101490965 1040335083798778832882389)
                    ·
                      rfl

theorem cell23_6078136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_6078136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078136 prefixEnd_6078136 := by exact prefixLift 6078136
  have htrace : WordTrace (prefixWord ++ tailWord_6078136) baseStart_6078136 baseEnd_6078136 := by
    simpa [prefixWord, tailWord_6078136, baseEnd_6078136] using wordTrace_append hprefix tailTrace_6078136
  have hstable : (prefixWord ++ tailWord_6078136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078136).length < 2 ^ (prefixWord ++ tailWord_6078136).sum := by decide
  have hdescent : baseEnd_6078136 < baseStart_6078136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078137 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6078137 : Nat := 118140960795 + 6078137 * 2 ^ 59
def prefixEnd_6078137 : Nat := 4983230072969 + 3 ^ 40 * 6078137 * 2
def baseEnd_6078137 : Nat := 3121005764876990994734663

theorem tailTrace_6078137 : CollatzResearch.WordTrace tailWord_6078137 prefixEnd_6078137 3121005764876990994734663 := by
  unfold tailWord_6078137
  simp only [CollatzResearch.WordTrace]
  refine ⟨221687868780955187000280665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147791912520636791333520443 221687868780955187000280665)
  ·
    refine ⟨166265901585716390250210499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221687868780955187000280665 166265901585716390250210499)
    ·
      refine ⟨249398852378574585375315749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166265901585716390250210499 249398852378574585375315749)
      ·
        refine ⟨46762284820982734757871703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249398852378574585375315749 46762284820982734757871703)
        ·
          refine ⟨70143427231474102136807555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46762284820982734757871703 70143427231474102136807555)
          ·
            refine ⟨105215140847211153205211333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70143427231474102136807555 105215140847211153205211333)
            ·
              refine ⟨19727838908852091225977125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105215140847211153205211333 19727838908852091225977125)
              ·
                refine ⟨3698969795409767104870711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19727838908852091225977125 3698969795409767104870711)
                ·
                  refine ⟨5548454693114650657306067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698969795409767104870711 5548454693114650657306067)
                  ·
                    refine ⟨8322682039671975985959101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5548454693114650657306067 8322682039671975985959101)
                    ·
                      refine ⟨3121005764876990994734663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8322682039671975985959101 3121005764876990994734663)
                      ·
                        rfl

theorem cell23_6078137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6078137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078137 prefixEnd_6078137 := by exact prefixLift 6078137
  have htrace : WordTrace (prefixWord ++ tailWord_6078137) baseStart_6078137 baseEnd_6078137 := by
    simpa [prefixWord, tailWord_6078137, baseEnd_6078137] using wordTrace_append hprefix tailTrace_6078137
  have hstable : (prefixWord ++ tailWord_6078137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078137).length < 2 ^ (prefixWord ++ tailWord_6078137).sum := by decide
  have hdescent : baseEnd_6078137 < baseStart_6078137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078157 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6078157 : Nat := 118140960795 + 6078157 * 2 ^ 59
def prefixEnd_6078157 : Nat := 4983230072969 + 3 ^ 40 * 6078157 * 2
def baseEnd_6078157 : Nat := 1040338678163360305494857

theorem tailTrace_6078157 : CollatzResearch.WordTrace tailWord_6078157 prefixEnd_6078157 1040338678163360305494857 := by
  unfold tailWord_6078157
  simp only [CollatzResearch.WordTrace]
  refine ⟨221688598240882730416008725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147792398827255153610672483 221688598240882730416008725)
  ·
    refine ⟨10391653042541377988250409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221688598240882730416008725 10391653042541377988250409)
    ·
      refine ⟨7793739781906033491187807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10391653042541377988250409 7793739781906033491187807)
      ·
        refine ⟨11690609672859050236781711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793739781906033491187807 11690609672859050236781711)
        ·
          refine ⟨17535914509288575355172567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11690609672859050236781711 17535914509288575355172567)
          ·
            refine ⟨26303871763932863032758851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535914509288575355172567 26303871763932863032758851)
            ·
              refine ⟨39455807645899294549138277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26303871763932863032758851 39455807645899294549138277)
              ·
                refine ⟨7397963933606117727963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39455807645899294549138277 7397963933606117727963427)
                ·
                  refine ⟨11096945900409176591945141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397963933606117727963427 11096945900409176591945141)
                  ·
                    refine ⟨1040338678163360305494857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11096945900409176591945141 1040338678163360305494857)
                    ·
                      rfl

theorem cell23_6078157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6078157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078157 prefixEnd_6078157 := by exact prefixLift 6078157
  have htrace : WordTrace (prefixWord ++ tailWord_6078157) baseStart_6078157 baseEnd_6078157 := by
    simpa [prefixWord, tailWord_6078157, baseEnd_6078157] using wordTrace_append hprefix tailTrace_6078157
  have hstable : (prefixWord ++ tailWord_6078157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078157).length < 2 ^ (prefixWord ++ tailWord_6078157).sum := by decide
  have hdescent : baseEnd_6078157 < baseStart_6078157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2]
def baseStart_6078160 : Nat := 118140960795 + 6078160 * 2 ^ 59
def prefixEnd_6078160 : Nat := 4983230072969 + 3 ^ 40 * 6078160 * 2
def baseEnd_6078160 : Nat := 3121017574932044404747057

theorem tailTrace_6078160 : CollatzResearch.WordTrace tailWord_6078160 prefixEnd_6078160 3121017574932044404747057 := by
  unfold tailWord_6078160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110844353829935930964183967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147792471773247907952245289 110844353829935930964183967)
  ·
    refine ⟨166266530744903896446275951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110844353829935930964183967 166266530744903896446275951)
    ·
      refine ⟨249399796117355844669413927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166266530744903896446275951 249399796117355844669413927)
      ·
        refine ⟨374099694176033767004120891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249399796117355844669413927 374099694176033767004120891)
        ·
          refine ⟨561149541264050650506181337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374099694176033767004120891 561149541264050650506181337)
          ·
            refine ⟨420862155948037987879636003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561149541264050650506181337 420862155948037987879636003)
            ·
              refine ⟨631293233922056981819454005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420862155948037987879636003 631293233922056981819454005)
              ·
                refine ⟨59183740680192842045573813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 631293233922056981819454005 59183740680192842045573813)
                ·
                  refine ⟨5548475688768078941772545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59183740680192842045573813 5548475688768078941772545)
                  ·
                    refine ⟨4161356766576059206329409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548475688768078941772545 4161356766576059206329409)
                    ·
                      refine ⟨3121017574932044404747057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161356766576059206329409 3121017574932044404747057)
                      ·
                        rfl

theorem cell23_6078160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2].length) (baseStart_6078160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078160 prefixEnd_6078160 := by exact prefixLift 6078160
  have htrace : WordTrace (prefixWord ++ tailWord_6078160) baseStart_6078160 baseEnd_6078160 := by
    simpa [prefixWord, tailWord_6078160, baseEnd_6078160] using wordTrace_append hprefix tailTrace_6078160
  have hstable : (prefixWord ++ tailWord_6078160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078160).length < 2 ^ (prefixWord ++ tailWord_6078160).sum := by decide
  have hdescent : baseEnd_6078160 < baseStart_6078160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078180 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_6078180 : Nat := 118140960795 + 6078180 * 2 ^ 59
def prefixEnd_6078180 : Nat := 4983230072969 + 3 ^ 40 * 6078180 * 2
def baseEnd_6078180 : Nat := 3121027844545134326496965

theorem tailTrace_6078180 : CollatzResearch.WordTrace tailWord_6078180 prefixEnd_6078180 3121027844545134326496965 := by
  unfold tailWord_6078180
  simp only [CollatzResearch.WordTrace]
  refine ⟨110844718559899702672047997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147792958079866270229397329 110844718559899702672047997)
  ·
    refine ⟨41566769459962388502017999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110844718559899702672047997 41566769459962388502017999)
    ·
      refine ⟨62350154189943582753026999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41566769459962388502017999 62350154189943582753026999)
      ·
        refine ⟨93525231284915374129540499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62350154189943582753026999 93525231284915374129540499)
        ·
          refine ⟨140287846927373061194310749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93525231284915374129540499 140287846927373061194310749)
          ·
            refine ⟨52607942597764897947866531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140287846927373061194310749 52607942597764897947866531)
            ·
              refine ⟨78911913896647346921799797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52607942597764897947866531 78911913896647346921799797)
              ·
                refine ⟨7397991927810688773918731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78911913896647346921799797 7397991927810688773918731)
                ·
                  refine ⟨11096987891716033160878097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397991927810688773918731 11096987891716033160878097)
                  ·
                    refine ⟨8322740918787024870658573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11096987891716033160878097 8322740918787024870658573)
                    ·
                      refine ⟨3121027844545134326496965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8322740918787024870658573 3121027844545134326496965)
                      ·
                        rfl

theorem cell23_6078180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_6078180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078180 prefixEnd_6078180 := by exact prefixLift 6078180
  have htrace : WordTrace (prefixWord ++ tailWord_6078180) baseStart_6078180 baseEnd_6078180 := by
    simpa [prefixWord, tailWord_6078180, baseEnd_6078180] using wordTrace_append hprefix tailTrace_6078180
  have hstable : (prefixWord ++ tailWord_6078180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078180).length < 2 ^ (prefixWord ++ tailWord_6078180).sum := by decide
  have hdescent : baseEnd_6078180 < baseStart_6078180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078221 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6078221 : Nat := 118140960795 + 6078221 * 2 ^ 59
def prefixEnd_6078221 : Nat := 4983230072969 + 3 ^ 40 * 6078221 * 2
def baseEnd_6078221 : Nat := 1040349632417322888694759

theorem tailTrace_6078221 : CollatzResearch.WordTrace tailWord_6078221 prefixEnd_6078221 1040349632417322888694759 := by
  unfold tailWord_6078221
  simp only [CollatzResearch.WordTrace]
  refine ⟨221690932512650869346338517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147793955008433912897559011 221690932512650869346338517)
  ·
    refine ⟨5195881230765254750304809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 221690932512650869346338517 5195881230765254750304809)
    ·
      refine ⟨3896910923073941062728607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5195881230765254750304809 3896910923073941062728607)
      ·
        refine ⟨5845366384610911594092911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896910923073941062728607 5845366384610911594092911)
        ·
          refine ⟨8768049576916367391139367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845366384610911594092911 8768049576916367391139367)
          ·
            refine ⟨13152074365374551086709051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768049576916367391139367 13152074365374551086709051)
            ·
              refine ⟨19728111548061826630063577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13152074365374551086709051 19728111548061826630063577)
              ·
                refine ⟨14796083661046369972547683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19728111548061826630063577 14796083661046369972547683)
                ·
                  refine ⟨22194125491569554958821525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14796083661046369972547683 22194125491569554958821525)
                  ·
                    refine ⟨1040349632417322888694759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22194125491569554958821525 1040349632417322888694759)
                    ·
                      rfl

theorem cell23_6078221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6078221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078221 prefixEnd_6078221 := by exact prefixLift 6078221
  have htrace : WordTrace (prefixWord ++ tailWord_6078221) baseStart_6078221 baseEnd_6078221 := by
    simpa [prefixWord, tailWord_6078221, baseEnd_6078221] using wordTrace_append hprefix tailTrace_6078221
  have hstable : (prefixWord ++ tailWord_6078221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078221).length < 2 ^ (prefixWord ++ tailWord_6078221).sum := by decide
  have hdescent : baseEnd_6078221 < baseStart_6078221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078228 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6078228 : Nat := 118140960795 + 6078228 * 2 ^ 59
def prefixEnd_6078228 : Nat := 4983230072969 + 3 ^ 40 * 6078228 * 2
def baseEnd_6078228 : Nat := 3121052491616550138696745

theorem tailTrace_6078228 : CollatzResearch.WordTrace tailWord_6078228 prefixEnd_6078228 3121052491616550138696745 := by
  unfold tailWord_6078228
  simp only [CollatzResearch.WordTrace]
  refine ⟨110845593911812754770921669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147794125215750339694562225 110845593911812754770921669)
  ·
    refine ⟨20783548858464891519547813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110845593911812754770921669 20783548858464891519547813)
    ·
      refine ⟨3896915410962167159915215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20783548858464891519547813 3896915410962167159915215)
      ·
        refine ⟨5845373116443250739872823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896915410962167159915215 5845373116443250739872823)
        ·
          refine ⟨8768059674664876109809235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845373116443250739872823 8768059674664876109809235)
          ·
            refine ⟨13152089511997314164713853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768059674664876109809235 13152089511997314164713853)
            ·
              refine ⟨4932033566998992811767695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13152089511997314164713853 4932033566998992811767695)
              ·
                refine ⟨7398050350498489217651543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932033566998992811767695 7398050350498489217651543)
                ·
                  refine ⟨11097075525747733826477315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398050350498489217651543 11097075525747733826477315)
                  ·
                    refine ⟨16645613288621600739715973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11097075525747733826477315 16645613288621600739715973)
                    ·
                      refine ⟨3121052491616550138696745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16645613288621600739715973 3121052491616550138696745)
                      ·
                        rfl

theorem cell23_6078228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6078228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078228 prefixEnd_6078228 := by exact prefixLift 6078228
  have htrace : WordTrace (prefixWord ++ tailWord_6078228) baseStart_6078228 baseEnd_6078228 := by
    simpa [prefixWord, tailWord_6078228, baseEnd_6078228] using wordTrace_append hprefix tailTrace_6078228
  have hstable : (prefixWord ++ tailWord_6078228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078228).length < 2 ^ (prefixWord ++ tailWord_6078228).sum := by decide
  have hdescent : baseEnd_6078228 < baseStart_6078228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078244 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_6078244 : Nat := 118140960795 + 6078244 * 2 ^ 59
def prefixEnd_6078244 : Nat := 4983230072969 + 3 ^ 40 * 6078244 * 2
def baseEnd_6078244 : Nat := 3121060707307022076096671

theorem tailTrace_6078244 : CollatzResearch.WordTrace tailWord_6078244 prefixEnd_6078244 3121060707307022076096671 := by
  unfold tailWord_6078244
  simp only [CollatzResearch.WordTrace]
  refine ⟨110845885695783772137212893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147794514261045029516283857 110845885695783772137212893)
  ·
    refine ⟨41567207135918914551454835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110845885695783772137212893 41567207135918914551454835)
    ·
      refine ⟨62350810703878371827182253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41567207135918914551454835 62350810703878371827182253)
      ·
        refine ⟨23381554013954389435193345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62350810703878371827182253 23381554013954389435193345)
        ·
          refine ⟨17536165510465792076395009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23381554013954389435193345 17536165510465792076395009)
          ·
            refine ⟨13152124132849344057296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17536165510465792076395009 13152124132849344057296257)
            ·
              refine ⟨9864093099637008042972193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13152124132849344057296257 9864093099637008042972193)
              ·
                refine ⟨7398069824727756032229145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9864093099637008042972193 7398069824727756032229145)
                ·
                  refine ⟨5548552368545817024171859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398069824727756032229145 5548552368545817024171859)
                  ·
                    refine ⟨8322828552818725536257789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5548552368545817024171859 8322828552818725536257789)
                    ·
                      refine ⟨3121060707307022076096671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8322828552818725536257789 3121060707307022076096671)
                      ·
                        rfl

theorem cell23_6078244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_6078244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078244 prefixEnd_6078244 := by exact prefixLift 6078244
  have htrace : WordTrace (prefixWord ++ tailWord_6078244) baseStart_6078244 baseEnd_6078244 := by
    simpa [prefixWord, tailWord_6078244, baseEnd_6078244] using wordTrace_append hprefix tailTrace_6078244
  have hstable : (prefixWord ++ tailWord_6078244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078244).length < 2 ^ (prefixWord ++ tailWord_6078244).sum := by decide
  have hdescent : baseEnd_6078244 < baseStart_6078244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078260 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6078260 : Nat := 118140960795 + 6078260 * 2 ^ 59
def prefixEnd_6078260 : Nat := 4983230072969 + 3 ^ 40 * 6078260 * 2
def baseEnd_6078260 : Nat := 1040356307665831337832199

theorem tailTrace_6078260 : CollatzResearch.WordTrace tailWord_6078260 prefixEnd_6078260 1040356307665831337832199 := by
  unfold tailWord_6078260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110846177479754789503504117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147794903306339719338005489 110846177479754789503504117)
  ·
    refine ⟨10391829138727011515953511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110846177479754789503504117 10391829138727011515953511)
    ·
      refine ⟨15587743708090517273930267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10391829138727011515953511 15587743708090517273930267)
      ·
        refine ⟨23381615562135775910895401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587743708090517273930267 23381615562135775910895401)
        ·
          refine ⟨17536211671601831933171551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23381615562135775910895401 17536211671601831933171551)
          ·
            refine ⟨26304317507402747899757327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17536211671601831933171551 26304317507402747899757327)
            ·
              refine ⟨39456476261104121849635991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26304317507402747899757327 39456476261104121849635991)
              ·
                refine ⟨59184714391656182774453987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39456476261104121849635991 59184714391656182774453987)
                ·
                  refine ⟨88777071587484274161680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59184714391656182774453987 88777071587484274161680981)
                  ·
                    refine ⟨1040356307665831337832199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88777071587484274161680981 1040356307665831337832199)
                    ·
                      rfl

theorem cell23_6078260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6078260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078260 prefixEnd_6078260 := by exact prefixLift 6078260
  have htrace : WordTrace (prefixWord ++ tailWord_6078260) baseStart_6078260 baseEnd_6078260 := by
    simpa [prefixWord, tailWord_6078260, baseEnd_6078260] using wordTrace_append hprefix tailTrace_6078260
  have hstable : (prefixWord ++ tailWord_6078260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078260).length < 2 ^ (prefixWord ++ tailWord_6078260).sum := by decide
  have hdescent : baseEnd_6078260 < baseStart_6078260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078313 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_6078313 : Nat := 118140960795 + 6078313 * 2 ^ 59
def prefixEnd_6078313 : Nat := 4983230072969 + 3 ^ 40 * 6078313 * 2
def baseEnd_6078313 : Nat := 3121096137472182306133853

theorem tailTrace_6078313 : CollatzResearch.WordTrace tailWord_6078313 prefixEnd_6078313 3121096137472182306133853 := by
  unfold tailWord_6078313
  simp only [CollatzResearch.WordTrace]
  refine ⟨221694288028317569058687593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147796192018878379372458395 221694288028317569058687593)
  ·
    refine ⟨166270716021238176794015695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221694288028317569058687593 166270716021238176794015695)
    ·
      refine ⟨249406074031857265191023543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166270716021238176794015695 249406074031857265191023543)
      ·
        refine ⟨374109111047785897786535315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249406074031857265191023543 374109111047785897786535315)
        ·
          refine ⟨561163666571678846679802973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374109111047785897786535315 561163666571678846679802973)
          ·
            refine ⟨210436374964379567504926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561163666571678846679802973 210436374964379567504926115)
            ·
              refine ⟨315654562446569351257389173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210436374964379567504926115 315654562446569351257389173)
              ·
                refine ⟨29592615229365876680380235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315654562446569351257389173 29592615229365876680380235)
                ·
                  refine ⟨44388922844048815020570353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29592615229365876680380235 44388922844048815020570353)
                  ·
                    refine ⟨33291692133036611265427765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44388922844048815020570353 33291692133036611265427765)
                    ·
                      refine ⟨3121096137472182306133853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33291692133036611265427765 3121096137472182306133853)
                      ·
                        rfl

theorem cell23_6078313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_6078313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078313 prefixEnd_6078313 := by exact prefixLift 6078313
  have htrace : WordTrace (prefixWord ++ tailWord_6078313) baseStart_6078313 baseEnd_6078313 := by
    simpa [prefixWord, tailWord_6078313, baseEnd_6078313] using wordTrace_append hprefix tailTrace_6078313
  have hstable : (prefixWord ++ tailWord_6078313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078313).length < 2 ^ (prefixWord ++ tailWord_6078313).sum := by decide
  have hdescent : baseEnd_6078313 < baseStart_6078313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078318 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6078318 : Nat := 118140960795 + 6078318 * 2 ^ 59
def prefixEnd_6078318 : Nat := 4983230072969 + 3 ^ 40 * 6078318 * 2
def baseEnd_6078318 : Nat := 3121098704875454786571331

theorem tailTrace_6078318 : CollatzResearch.WordTrace tailWord_6078318 prefixEnd_6078318 3121098704875454786571331 := by
  unfold tailWord_6078318
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711808799162431864077451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147796313595532969941746405 27711808799162431864077451)
  ·
    refine ⟨41567713198743647796116177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27711808799162431864077451 41567713198743647796116177)
    ·
      refine ⟨31175784899057735847087133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41567713198743647796116177 31175784899057735847087133)
      ·
        refine ⟨11690919337146650942657675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31175784899057735847087133 11690919337146650942657675)
        ·
          refine ⟨17536379005719976413986513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11690919337146650942657675 17536379005719976413986513)
          ·
            refine ⟨13152284254289982310489885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17536379005719976413986513 13152284254289982310489885)
            ·
              refine ⟨4932106595358743366433707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13152284254289982310489885 4932106595358743366433707)
              ·
                refine ⟨7398159893038115049650561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932106595358743366433707 7398159893038115049650561)
                ·
                  refine ⟨5548619919778586287237921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398159893038115049650561 5548619919778586287237921)
                  ·
                    refine ⟨4161464939833939715428441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548619919778586287237921 4161464939833939715428441)
                    ·
                      refine ⟨3121098704875454786571331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161464939833939715428441 3121098704875454786571331)
                      ·
                        rfl

theorem cell23_6078318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6078318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078318 prefixEnd_6078318 := by exact prefixLift 6078318
  have htrace : WordTrace (prefixWord ++ tailWord_6078318) baseStart_6078318 baseEnd_6078318 := by
    simpa [prefixWord, tailWord_6078318, baseEnd_6078318] using wordTrace_append hprefix tailTrace_6078318
  have hstable : (prefixWord ++ tailWord_6078318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078318).length < 2 ^ (prefixWord ++ tailWord_6078318).sum := by decide
  have hdescent : baseEnd_6078318 < baseStart_6078318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078333 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_6078333 : Nat := 118140960795 + 6078333 * 2 ^ 59
def prefixEnd_6078333 : Nat := 4983230072969 + 3 ^ 40 * 6078333 * 2
def baseEnd_6078333 : Nat := 1040368802361757409294587

theorem tailTrace_6078333 : CollatzResearch.WordTrace tailWord_6078333 prefixEnd_6078333 1040368802361757409294587 := by
  unfold tailWord_6078333
  simp only [CollatzResearch.WordTrace]
  refine ⟨221695017488245112474415653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147796678325496741649610435 221695017488245112474415653)
  ·
    refine ⟨41567815779045958588952935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221695017488245112474415653 41567815779045958588952935)
    ·
      refine ⟨62351723668568937883429403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41567815779045958588952935 62351723668568937883429403)
      ·
        refine ⟨93527585502853406825144105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62351723668568937883429403 93527585502853406825144105)
        ·
          refine ⟨70145689127140055118858079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93527585502853406825144105 70145689127140055118858079)
          ·
            refine ⟨105218533690710082678287119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70145689127140055118858079 105218533690710082678287119)
            ·
              refine ⟨157827800536065124017430679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105218533690710082678287119 157827800536065124017430679)
              ·
                refine ⟨236741700804097686026146019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157827800536065124017430679 236741700804097686026146019)
                ·
                  refine ⟨355112551206146529039219029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236741700804097686026146019 355112551206146529039219029)
                  ·
                    refine ⟨1040368802361757409294587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 355112551206146529039219029 1040368802361757409294587)
                    ·
                      rfl

theorem cell23_6078333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_6078333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078333 prefixEnd_6078333 := by exact prefixLift 6078333
  have htrace : WordTrace (prefixWord ++ tailWord_6078333) baseStart_6078333 baseEnd_6078333 := by
    simpa [prefixWord, tailWord_6078333, baseEnd_6078333] using wordTrace_append hprefix tailTrace_6078333
  have hstable : (prefixWord ++ tailWord_6078333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078333).length < 2 ^ (prefixWord ++ tailWord_6078333).sum := by decide
  have hdescent : baseEnd_6078333 < baseStart_6078333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078340 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6078340 : Nat := 118140960795 + 6078340 * 2 ^ 59
def prefixEnd_6078340 : Nat := 4983230072969 + 3 ^ 40 * 6078340 * 2
def baseEnd_6078340 : Nat := 3121110001449853700496229

theorem tailTrace_6078340 : CollatzResearch.WordTrace tailWord_6078340 prefixEnd_6078340 3121110001449853700496229 := by
  unfold tailWord_6078340
  simp only [CollatzResearch.WordTrace]
  refine ⟨110847636399609876334960237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147796848532813168446613649 110847636399609876334960237)
  ·
    refine ⟨41567863649853703625610089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110847636399609876334960237 41567863649853703625610089)
    ·
      refine ⟨31175897737390277719207567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41567863649853703625610089 31175897737390277719207567)
      ·
        refine ⟨46763846606085416578811351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31175897737390277719207567 46763846606085416578811351)
        ·
          refine ⟨70145769909128124868217027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46763846606085416578811351 70145769909128124868217027)
          ·
            refine ⟨105218654863692187302325541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70145769909128124868217027 105218654863692187302325541)
            ·
              refine ⟨19728497786942285119186039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105218654863692187302325541 19728497786942285119186039)
              ·
                refine ⟨29592746680413427678779059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19728497786942285119186039 29592746680413427678779059)
                ·
                  refine ⟨44389120020620141518168589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29592746680413427678779059 44389120020620141518168589)
                  ·
                    refine ⟨16645920007732553069313221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44389120020620141518168589 16645920007732553069313221)
                    ·
                      refine ⟨3121110001449853700496229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16645920007732553069313221 3121110001449853700496229)
                      ·
                        rfl

theorem cell23_6078340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6078340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078340 prefixEnd_6078340 := by exact prefixLift 6078340
  have htrace : WordTrace (prefixWord ++ tailWord_6078340) baseStart_6078340 baseEnd_6078340 := by
    simpa [prefixWord, tailWord_6078340, baseEnd_6078340] using wordTrace_append hprefix tailTrace_6078340
  have hstable : (prefixWord ++ tailWord_6078340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078340).length < 2 ^ (prefixWord ++ tailWord_6078340).sum := by decide
  have hdescent : baseEnd_6078340 < baseStart_6078340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078353 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_6078353 : Nat := 118140960795 + 6078353 * 2 ^ 59
def prefixEnd_6078353 : Nat := 4983230072969 + 3 ^ 40 * 6078353 * 2
def baseEnd_6078353 : Nat := 3121116676698362149633669

theorem tailTrace_6078353 : CollatzResearch.WordTrace tailWord_6078353 prefixEnd_6078353 3121116676698362149633669 := by
  unfold tailWord_6078353
  simp only [CollatzResearch.WordTrace]
  refine ⟨221695746948172655890143713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147797164632115103926762475 221695746948172655890143713)
  ·
    refine ⟨166271810211129491917607785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221695746948172655890143713 166271810211129491917607785)
    ·
      refine ⟨124703857658347118938205839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166271810211129491917607785 124703857658347118938205839)
      ·
        refine ⟨187055786487520678407308759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124703857658347118938205839 187055786487520678407308759)
        ·
          refine ⟨280583679731281017610963139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187055786487520678407308759 280583679731281017610963139)
          ·
            refine ⟨420875519596921526416444709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280583679731281017610963139 420875519596921526416444709)
            ·
              refine ⟨78914159924422786203083383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420875519596921526416444709 78914159924422786203083383)
              ·
                refine ⟨118371239886634179304625075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78914159924422786203083383 118371239886634179304625075)
                ·
                  refine ⟨177556859829951268956937613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118371239886634179304625075 177556859829951268956937613)
                  ·
                    refine ⟨66583822436231725858851605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177556859829951268956937613 66583822436231725858851605)
                    ·
                      refine ⟨3121116676698362149633669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66583822436231725858851605 3121116676698362149633669)
                      ·
                        rfl

theorem cell23_6078353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_6078353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078353 prefixEnd_6078353 := by exact prefixLift 6078353
  have htrace : WordTrace (prefixWord ++ tailWord_6078353) baseStart_6078353 baseEnd_6078353 := by
    simpa [prefixWord, tailWord_6078353, baseEnd_6078353] using wordTrace_append hprefix tailTrace_6078353
  have hstable : (prefixWord ++ tailWord_6078353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078353).length < 2 ^ (prefixWord ++ tailWord_6078353).sum := by decide
  have hdescent : baseEnd_6078353 < baseStart_6078353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078358 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6078358 : Nat := 118140960795 + 6078358 * 2 ^ 59
def prefixEnd_6078358 : Nat := 4983230072969 + 3 ^ 40 * 6078358 * 2
def baseEnd_6078358 : Nat := 346791027122403847785683

theorem tailTrace_6078358 : CollatzResearch.WordTrace tailWord_6078358 prefixEnd_6078358 346791027122403847785683 := by
  unfold tailWord_6078358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855995582072158859004733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147797286208769694496050485 13855995582072158859004733)
  ·
    refine ⟨5195998343277059572126775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13855995582072158859004733 5195998343277059572126775)
    ·
      refine ⟨7793997514915589358190163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5195998343277059572126775 7793997514915589358190163)
      ·
        refine ⟨11690996272373384037285245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793997514915589358190163 11690996272373384037285245)
        ·
          refine ⟨4384123602140019013981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11690996272373384037285245 4384123602140019013981967)
          ·
            refine ⟨6576185403210028520972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384123602140019013981967 6576185403210028520972951)
            ·
              refine ⟨9864278104815042781459427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576185403210028520972951 9864278104815042781459427)
              ·
                refine ⟨14796417157222564172189141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864278104815042781459427 14796417157222564172189141)
                ·
                  refine ⟨346791027122403847785683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14796417157222564172189141 346791027122403847785683)
                  ·
                    rfl

theorem cell23_6078358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6078358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078358 prefixEnd_6078358 := by exact prefixLift 6078358
  have htrace : WordTrace (prefixWord ++ tailWord_6078358) baseStart_6078358 baseEnd_6078358 := by
    simpa [prefixWord, tailWord_6078358, baseEnd_6078358] using wordTrace_append hprefix tailTrace_6078358
  have hstable : (prefixWord ++ tailWord_6078358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078358).length < 2 ^ (prefixWord ++ tailWord_6078358).sum := by decide
  have hdescent : baseEnd_6078358 < baseStart_6078358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078417 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_6078417 : Nat := 118140960795 + 6078417 * 2 ^ 59
def prefixEnd_6078417 : Nat := 4983230072969 + 3 ^ 40 * 6078417 * 2
def baseEnd_6078417 : Nat := 3121149539460249899233375

theorem tailTrace_6078417 : CollatzResearch.WordTrace tailWord_6078417 prefixEnd_6078417 3121149539460249899233375 := by
  unfold tailWord_6078417
  simp only [CollatzResearch.WordTrace]
  refine ⟨221698081219940794820473505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147798720813293863213649003 221698081219940794820473505)
  ·
    refine ⟨166273560914955596115355129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221698081219940794820473505 166273560914955596115355129)
    ·
      refine ⟨124705170686216697086516347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166273560914955596115355129 124705170686216697086516347)
      ·
        refine ⟨187057756029325045629774521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124705170686216697086516347 187057756029325045629774521)
        ·
          refine ⟨140293317021993784222330891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187057756029325045629774521 140293317021993784222330891)
          ·
            refine ⟨210439975532990676333496337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140293317021993784222330891 210439975532990676333496337)
            ·
              refine ⟨157829981649743007250122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210439975532990676333496337 157829981649743007250122253)
              ·
                refine ⟨59186243118653627718795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157829981649743007250122253 59186243118653627718795845)
                ·
                  refine ⟨11097420584747555197274221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59186243118653627718795845 11097420584747555197274221)
                  ·
                    refine ⟨4161532719280333198977833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11097420584747555197274221 4161532719280333198977833)
                    ·
                      refine ⟨3121149539460249899233375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161532719280333198977833 3121149539460249899233375)
                      ·
                        rfl

theorem cell23_6078417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_6078417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078417 prefixEnd_6078417 := by exact prefixLift 6078417
  have htrace : WordTrace (prefixWord ++ tailWord_6078417) baseStart_6078417 baseEnd_6078417 := by
    simpa [prefixWord, tailWord_6078417, baseEnd_6078417] using wordTrace_append hprefix tailTrace_6078417
  have hstable : (prefixWord ++ tailWord_6078417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078417).length < 2 ^ (prefixWord ++ tailWord_6078417).sum := by decide
  have hdescent : baseEnd_6078417 < baseStart_6078417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078447 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_6078447 : Nat := 118140960795 + 6078447 * 2 ^ 59
def prefixEnd_6078447 : Nat := 4983230072969 + 3 ^ 40 * 6078447 * 2
def baseEnd_6078447 : Nat := 3121164943879884781858237

theorem tailTrace_6078447 : CollatzResearch.WordTrace tailWord_6078447 prefixEnd_6078447 3121164943879884781858237 := by
  unfold tailWord_6078447
  simp only [CollatzResearch.WordTrace]
  refine ⟨221699175409832109944065595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147799450273221406629377063 221699175409832109944065595)
  ·
    refine ⟨332548763114748164916098393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221699175409832109944065595 332548763114748164916098393)
    ·
      refine ⟨249411572336061123687073795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332548763114748164916098393 249411572336061123687073795)
      ·
        refine ⟨374117358504091685530610693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249411572336061123687073795 374117358504091685530610693)
        ·
          refine ⟨70147004719517191036989505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374117358504091685530610693 70147004719517191036989505)
          ·
            refine ⟨52610253539637893277742129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70147004719517191036989505 52610253539637893277742129)
            ·
              refine ⟨39457690154728419958306597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52610253539637893277742129 39457690154728419958306597)
              ·
                refine ⟨7398316904011578742182487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39457690154728419958306597 7398316904011578742182487)
                ·
                  refine ⟨11097475356017368113273731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398316904011578742182487 11097475356017368113273731)
                  ·
                    refine ⟨16646213034026052169910597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11097475356017368113273731 16646213034026052169910597)
                    ·
                      refine ⟨3121164943879884781858237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16646213034026052169910597 3121164943879884781858237)
                      ·
                        rfl

theorem cell23_6078447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_6078447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078447 prefixEnd_6078447 := by exact prefixLift 6078447
  have htrace : WordTrace (prefixWord ++ tailWord_6078447) baseStart_6078447 baseEnd_6078447 := by
    simpa [prefixWord, tailWord_6078447, baseEnd_6078447] using wordTrace_append hprefix tailTrace_6078447
  have hstable : (prefixWord ++ tailWord_6078447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078447).length < 2 ^ (prefixWord ++ tailWord_6078447).sum := by decide
  have hdescent : baseEnd_6078447 < baseStart_6078447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078474 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_6078474 : Nat := 118140960795 + 6078474 * 2 ^ 59
def prefixEnd_6078474 : Nat := 4983230072969 + 3 ^ 40 * 6078474 * 2
def baseEnd_6078474 : Nat := 1040392935952518725406871

theorem tailTrace_6078474 : CollatzResearch.WordTrace tailWord_6078474 prefixEnd_6078474 1040392935952518725406871 := by
  unfold tailWord_6078474
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425040045183573388824619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147800106787156195703532317 55425040045183573388824619)
  ·
    refine ⟨83137560067775360083236929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55425040045183573388824619 83137560067775360083236929)
    ·
      refine ⟨62353170050831520062427697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83137560067775360083236929 62353170050831520062427697)
      ·
        refine ⟨46764877538123640046820773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62353170050831520062427697 46764877538123640046820773)
        ·
          refine ⟨8768414538398182508778895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46764877538123640046820773 8768414538398182508778895)
          ·
            refine ⟨13152621807597273763168343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768414538398182508778895 13152621807597273763168343)
            ·
              refine ⟨19728932711395910644752515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13152621807597273763168343 19728932711395910644752515)
              ·
                refine ⟨29593399067093865967128773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19728932711395910644752515 29593399067093865967128773)
                ·
                  refine ⟨5548762325080099868836645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29593399067093865967128773 5548762325080099868836645)
                  ·
                    refine ⟨1040392935952518725406871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5548762325080099868836645 1040392935952518725406871)
                    ·
                      rfl

theorem cell23_6078474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_6078474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078474 prefixEnd_6078474 := by exact prefixLift 6078474
  have htrace : WordTrace (prefixWord ++ tailWord_6078474) baseStart_6078474 baseEnd_6078474 := by
    simpa [prefixWord, tailWord_6078474, baseEnd_6078474] using wordTrace_append hprefix tailTrace_6078474
  have hstable : (prefixWord ++ tailWord_6078474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078474).length < 2 ^ (prefixWord ++ tailWord_6078474).sum := by decide
  have hdescent : baseEnd_6078474 < baseStart_6078474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078504 : List Nat := [2, 1, 5, 3, 1, 1, 1, 9]
def baseStart_6078504 : Nat := 118140960795 + 6078504 * 2 ^ 59
def prefixEnd_6078504 : Nat := 4983230072969 + 3 ^ 40 * 6078504 * 2
def baseEnd_6078504 : Nat := 115599785639895965142425

theorem tailTrace_6078504 : CollatzResearch.WordTrace tailWord_6078504 prefixEnd_6078504 115599785639895965142425 := by
  unfold tailWord_6078504
  simp only [CollatzResearch.WordTrace]
  refine ⟨110850627185312804339445283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147800836247083739119260377 110850627185312804339445283)
  ·
    refine ⟨166275940777969206509167925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110850627185312804339445283 166275940777969206509167925)
    ·
      refine ⟨15588369447934613110234493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166275940777969206509167925 15588369447934613110234493)
      ·
        refine ⟨5845638542975479916337935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15588369447934613110234493 5845638542975479916337935)
        ·
          refine ⟨8768457814463219874506903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845638542975479916337935 8768457814463219874506903)
          ·
            refine ⟨13152686721694829811760355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768457814463219874506903 13152686721694829811760355)
            ·
              refine ⟨19729030082542244717640533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13152686721694829811760355 19729030082542244717640533)
              ·
                refine ⟨115599785639895965142425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19729030082542244717640533 115599785639895965142425)
                ·
                  rfl

theorem cell23_6078504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 9].length) (baseStart_6078504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078504 prefixEnd_6078504 := by exact prefixLift 6078504
  have htrace : WordTrace (prefixWord ++ tailWord_6078504) baseStart_6078504 baseEnd_6078504 := by
    simpa [prefixWord, tailWord_6078504, baseEnd_6078504] using wordTrace_append hprefix tailTrace_6078504
  have hstable : (prefixWord ++ tailWord_6078504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078504).length < 2 ^ (prefixWord ++ tailWord_6078504).sum := by decide
  have hdescent : baseEnd_6078504 < baseStart_6078504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078514 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_6078514 : Nat := 118140960795 + 6078514 * 2 ^ 59
def prefixEnd_6078514 : Nat := 4983230072969 + 3 ^ 40 * 6078514 * 2
def baseEnd_6078514 : Nat := 3121199347083736019720429

theorem tailTrace_6078514 : CollatzResearch.WordTrace tailWord_6078514 prefixEnd_6078514 3121199347083736019720429 := by
  unfold tailWord_6078514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425404775147345096688649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147801079400392920257836397 55425404775147345096688649)
  ·
    refine ⟨41569053581360508822516487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55425404775147345096688649 41569053581360508822516487)
    ·
      refine ⟨62353580372040763233774731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41569053581360508822516487 62353580372040763233774731)
      ·
        refine ⟨93530370558061144850662097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62353580372040763233774731 93530370558061144850662097)
        ·
          refine ⟨70147777918545858637996573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93530370558061144850662097 70147777918545858637996573)
          ·
            refine ⟨26305416719454696989248715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70147777918545858637996573 26305416719454696989248715)
            ·
              refine ⟨39458125079182045483873073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26305416719454696989248715 39458125079182045483873073)
              ·
                refine ⟨29593593809386534112904805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39458125079182045483873073 29593593809386534112904805)
                ·
                  refine ⟨5548798839259975146169651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29593593809386534112904805 5548798839259975146169651)
                  ·
                    refine ⟨8323198258889962719254477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5548798839259975146169651 8323198258889962719254477)
                    ·
                      refine ⟨3121199347083736019720429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8323198258889962719254477 3121199347083736019720429)
                      ·
                        rfl

theorem cell23_6078514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_6078514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078514 prefixEnd_6078514 := by exact prefixLift 6078514
  have htrace : WordTrace (prefixWord ++ tailWord_6078514) baseStart_6078514 baseEnd_6078514 := by
    simpa [prefixWord, tailWord_6078514, baseEnd_6078514] using wordTrace_append hprefix tailTrace_6078514
  have hstable : (prefixWord ++ tailWord_6078514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078514).length < 2 ^ (prefixWord ++ tailWord_6078514).sum := by decide
  have hdescent : baseEnd_6078514 < baseStart_6078514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078534 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_6078534 : Nat := 118140960795 + 6078534 * 2 ^ 59
def prefixEnd_6078534 : Nat := 4983230072969 + 3 ^ 40 * 6078534 * 2
def baseEnd_6078534 : Nat := 1040403205565608647156779

theorem tailTrace_6078534 : CollatzResearch.WordTrace tailWord_6078534 prefixEnd_6078534 1040403205565608647156779 := by
  unfold tailWord_6078534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928198392516153868827583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147801565707011282534988437 6928198392516153868827583)
  ·
    refine ⟨10392297588774230803241375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6928198392516153868827583 10392297588774230803241375)
    ·
      refine ⟨15588446383161346204862063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392297588774230803241375 15588446383161346204862063)
      ·
        refine ⟨23382669574742019307293095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15588446383161346204862063 23382669574742019307293095)
        ·
          refine ⟨35074004362113028960939643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23382669574742019307293095 35074004362113028960939643)
          ·
            refine ⟨52611006543169543441409465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35074004362113028960939643 52611006543169543441409465)
            ·
              refine ⟨39458254907377157581057099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52611006543169543441409465 39458254907377157581057099)
              ·
                refine ⟨59187382361065736371585649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39458254907377157581057099 59187382361065736371585649)
                ·
                  refine ⟨44390536770799302278689237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59187382361065736371585649 44390536770799302278689237)
                  ·
                    refine ⟨1040403205565608647156779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44390536770799302278689237 1040403205565608647156779)
                    ·
                      rfl

theorem cell23_6078534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_6078534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078534 prefixEnd_6078534 := by exact prefixLift 6078534
  have htrace : WordTrace (prefixWord ++ tailWord_6078534) baseStart_6078534 baseEnd_6078534 := by
    simpa [prefixWord, tailWord_6078534, baseEnd_6078534] using wordTrace_append hprefix tailTrace_6078534
  have hstable : (prefixWord ++ tailWord_6078534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078534).length < 2 ^ (prefixWord ++ tailWord_6078534).sum := by decide
  have hdescent : baseEnd_6078534 < baseStart_6078534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078541 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6078541 : Nat := 118140960795 + 6078541 * 2 ^ 59
def prefixEnd_6078541 : Nat := 4983230072969 + 3 ^ 40 * 6078541 * 2
def baseEnd_6078541 : Nat := 3121213211061407414082805

theorem tailTrace_6078541 : CollatzResearch.WordTrace tailWord_6078541 prefixEnd_6078541 3121213211061407414082805 := by
  unfold tailWord_6078541
  simp only [CollatzResearch.WordTrace]
  refine ⟨221702603871491563997987477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147801735914327709331991651 221702603871491563997987477)
  ·
    refine ⟨10392309556476167062405663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221702603871491563997987477 10392309556476167062405663)
    ·
      refine ⟨15588464334714250593608495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392309556476167062405663 15588464334714250593608495)
      ·
        refine ⟨23382696502071375890412743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15588464334714250593608495 23382696502071375890412743)
        ·
          refine ⟨35074044753107063835619115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23382696502071375890412743 35074044753107063835619115)
          ·
            refine ⟨52611067129660595753428673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35074044753107063835619115 52611067129660595753428673)
            ·
              refine ⟨39458300347245446815071505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52611067129660595753428673 39458300347245446815071505)
              ·
                refine ⟨29593725260434085111303629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39458300347245446815071505 29593725260434085111303629)
                ·
                  refine ⟨11097646972662781916738861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29593725260434085111303629 11097646972662781916738861)
                  ·
                    refine ⟨4161617614748543218777073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11097646972662781916738861 4161617614748543218777073)
                    ·
                      refine ⟨3121213211061407414082805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161617614748543218777073 3121213211061407414082805)
                      ·
                        rfl

theorem cell23_6078541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6078541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078541 prefixEnd_6078541 := by exact prefixLift 6078541
  have htrace : WordTrace (prefixWord ++ tailWord_6078541) baseStart_6078541 baseEnd_6078541 := by
    simpa [prefixWord, tailWord_6078541, baseEnd_6078541] using wordTrace_append hprefix tailTrace_6078541
  have hstable : (prefixWord ++ tailWord_6078541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078541).length < 2 ^ (prefixWord ++ tailWord_6078541).sum := by decide
  have hdescent : baseEnd_6078541 < baseStart_6078541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078554 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_6078554 : Nat := 118140960795 + 6078554 * 2 ^ 59
def prefixEnd_6078554 : Nat := 4983230072969 + 3 ^ 40 * 6078554 * 2
def baseEnd_6078554 : Nat := 3121219886309915863220245

theorem tailTrace_6078554 : CollatzResearch.WordTrace tailWord_6078554 prefixEnd_6078554 3121219886309915863220245 := by
  unfold tailWord_6078554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55425769505111116804552679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147802052013629644812140477 55425769505111116804552679)
  ·
    refine ⟨83138654257666675206829019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55425769505111116804552679 83138654257666675206829019)
    ·
      refine ⟨124707981386500012810243529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83138654257666675206829019 124707981386500012810243529)
      ·
        refine ⟨93530986039875009607682647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124707981386500012810243529 93530986039875009607682647)
        ·
          refine ⟨140296479059812514411523971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93530986039875009607682647 140296479059812514411523971)
          ·
            refine ⟨210444718589718771617285957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140296479059812514411523971 210444718589718771617285957)
            ·
              refine ⟨39458384735572269678241117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210444718589718771617285957 39458384735572269678241117)
              ·
                refine ⟨14796894275839601129340419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39458384735572269678241117 14796894275839601129340419)
                ·
                  refine ⟨22195341413759401694010629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14796894275839601129340419 22195341413759401694010629)
                  ·
                    refine ⟨4161626515079887817626993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22195341413759401694010629 4161626515079887817626993)
                    ·
                      refine ⟨3121219886309915863220245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161626515079887817626993 3121219886309915863220245)
                      ·
                        rfl

theorem cell23_6078554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_6078554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078554 prefixEnd_6078554 := by exact prefixLift 6078554
  have htrace : WordTrace (prefixWord ++ tailWord_6078554) baseStart_6078554 baseEnd_6078554 := by
    simpa [prefixWord, tailWord_6078554, baseEnd_6078554] using wordTrace_append hprefix tailTrace_6078554
  have hstable : (prefixWord ++ tailWord_6078554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078554).length < 2 ^ (prefixWord ++ tailWord_6078554).sum := by decide
  have hdescent : baseEnd_6078554 < baseStart_6078554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078588 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_6078588 : Nat := 118140960795 + 6078588 * 2 ^ 59
def prefixEnd_6078588 : Nat := 4983230072969 + 3 ^ 40 * 6078588 * 2
def baseEnd_6078588 : Nat := 3121237344652168730195089

theorem tailTrace_6078588 : CollatzResearch.WordTrace tailWord_6078588 prefixEnd_6078588 3121237344652168730195089 := by
  unfold tailWord_6078588
  simp only [CollatzResearch.WordTrace]
  refine ⟨110852159051160645512474209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147802878734880860683298945 110852159051160645512474209)
  ·
    refine ⟨83139119288370484134355657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110852159051160645512474209 83139119288370484134355657)
    ·
      refine ⟨62354339466277863100766743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83139119288370484134355657 62354339466277863100766743)
      ·
        refine ⟨93531509199416794651150115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62354339466277863100766743 93531509199416794651150115)
        ·
          refine ⟨140297263799125191976725173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93531509199416794651150115 140297263799125191976725173)
          ·
            refine ⟨13152868481167986747817985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140297263799125191976725173 13152868481167986747817985)
            ·
              refine ⟨9864651360875990060863489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13152868481167986747817985 9864651360875990060863489)
              ·
                refine ⟨7398488520656992545647617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9864651360875990060863489 7398488520656992545647617)
                ·
                  refine ⟨5548866390492744409235713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398488520656992545647617 5548866390492744409235713)
                  ·
                    refine ⟨4161649792869558306926785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548866390492744409235713 4161649792869558306926785)
                    ·
                      refine ⟨3121237344652168730195089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161649792869558306926785 3121237344652168730195089)
                      ·
                        rfl

theorem cell23_6078588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_6078588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078588 prefixEnd_6078588 := by exact prefixLift 6078588
  have htrace : WordTrace (prefixWord ++ tailWord_6078588) baseStart_6078588 baseEnd_6078588 := by
    simpa [prefixWord, tailWord_6078588, baseEnd_6078588] using wordTrace_append hprefix tailTrace_6078588
  have hstable : (prefixWord ++ tailWord_6078588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078588).length < 2 ^ (prefixWord ++ tailWord_6078588).sum := by decide
  have hdescent : baseEnd_6078588 < baseStart_6078588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078624 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_6078624 : Nat := 118140960795 + 6078624 * 2 ^ 59
def prefixEnd_6078624 : Nat := 4983230072969 + 3 ^ 40 * 6078624 * 2
def baseEnd_6078624 : Nat := 1040418609985243529781641

theorem tailTrace_6078624 : CollatzResearch.WordTrace tailWord_6078624 prefixEnd_6078624 1040418609985243529781641 := by
  unfold tailWord_6078624
  simp only [CollatzResearch.WordTrace]
  refine ⟨110852815565095434586629463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147803754086793912782172617 110852815565095434586629463)
  ·
    refine ⟨166279223347643151879944195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110852815565095434586629463 166279223347643151879944195)
    ·
      refine ⟨249418835021464727819916293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166279223347643151879944195 249418835021464727819916293)
      ·
        refine ⟨46766031566524636466234305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249418835021464727819916293 46766031566524636466234305)
        ·
          refine ⟨35074523674893477349675729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46766031566524636466234305 35074523674893477349675729)
          ·
            refine ⟨26305892756170108012256797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35074523674893477349675729 26305892756170108012256797)
            ·
              refine ⟨9864709783563790504596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26305892756170108012256797 9864709783563790504596299)
              ·
                refine ⟨14797064675345685756894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864709783563790504596299 14797064675345685756894449)
                ·
                  refine ⟨11097798506509264317670837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14797064675345685756894449 11097798506509264317670837)
                  ·
                    refine ⟨1040418609985243529781641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11097798506509264317670837 1040418609985243529781641)
                    ·
                      rfl

theorem cell23_6078624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_6078624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078624 prefixEnd_6078624 := by exact prefixLift 6078624
  have htrace : WordTrace (prefixWord ++ tailWord_6078624) baseStart_6078624 baseEnd_6078624 := by
    simpa [prefixWord, tailWord_6078624, baseEnd_6078624] using wordTrace_append hprefix tailTrace_6078624
  have hstable : (prefixWord ++ tailWord_6078624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078624).length < 2 ^ (prefixWord ++ tailWord_6078624).sum := by decide
  have hdescent : baseEnd_6078624 < baseStart_6078624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078721 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_6078721 : Nat := 118140960795 + 6078721 * 2 ^ 59
def prefixEnd_6078721 : Nat := 4983230072969 + 3 ^ 40 * 6078721 * 2
def baseEnd_6078721 : Nat := 3121305637579216709831977

theorem tailTrace_6078721 : CollatzResearch.WordTrace tailWord_6078721 prefixEnd_6078721 3121305637579216709831977 := by
  unfold tailWord_6078721
  simp only [CollatzResearch.WordTrace]
  refine ⟨221709169010839454739540017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147806112673892969826360011 221709169010839454739540017)
  ·
    refine ⟨166281876758129591054655013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221709169010839454739540017 166281876758129591054655013)
    ·
      refine ⟨31177851892149298322747815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166281876758129591054655013 31177851892149298322747815)
      ·
        refine ⟨46766777838223947484121723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31177851892149298322747815 46766777838223947484121723)
        ·
          refine ⟨70150166757335921226182585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46766777838223947484121723 70150166757335921226182585)
          ·
            refine ⟨52612625068001940919636939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70150166757335921226182585 52612625068001940919636939)
            ·
              refine ⟨78918937602002911379455409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52612625068001940919636939 78918937602002911379455409)
              ·
                refine ⟨59189203201502183534591557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78918937602002911379455409 59189203201502183534591557)
                ·
                  refine ⟨11097975600281659412735917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59189203201502183534591557 11097975600281659412735917)
                  ·
                    refine ⟨4161740850105622279775969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11097975600281659412735917 4161740850105622279775969)
                    ·
                      refine ⟨3121305637579216709831977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161740850105622279775969 3121305637579216709831977)
                      ·
                        rfl

theorem cell23_6078721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_6078721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078721 prefixEnd_6078721 := by exact prefixLift 6078721
  have htrace : WordTrace (prefixWord ++ tailWord_6078721) baseStart_6078721 baseEnd_6078721 := by
    simpa [prefixWord, tailWord_6078721, baseEnd_6078721] using wordTrace_append hprefix tailTrace_6078721
  have hstable : (prefixWord ++ tailWord_6078721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078721).length < 2 ^ (prefixWord ++ tailWord_6078721).sum := by decide
  have hdescent : baseEnd_6078721 < baseStart_6078721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078744 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_6078744 : Nat := 118140960795 + 6078744 * 2 ^ 59
def prefixEnd_6078744 : Nat := 4983230072969 + 3 ^ 40 * 6078744 * 2
def baseEnd_6078744 : Nat := 1040439149211423373281457

theorem tailTrace_6078744 : CollatzResearch.WordTrace tailWord_6078744 prefixEnd_6078744 1040439149211423373281457 := by
  unfold tailWord_6078744
  simp only [CollatzResearch.WordTrace]
  refine ⟨110855003944878064833813643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147806671926504086445084857 110855003944878064833813643)
  ·
    refine ⟨166282505917317097250720465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110855003944878064833813643 166282505917317097250720465)
    ·
      refine ⟨124711879437987822938040349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166282505917317097250720465 124711879437987822938040349)
      ·
        refine ⟨46766954789245433601765131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124711879437987822938040349 46766954789245433601765131)
        ·
          refine ⟨70150432183868150402647697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46766954789245433601765131 70150432183868150402647697)
          ·
            refine ⟨52612824137901112801985773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70150432183868150402647697 52612824137901112801985773)
            ·
              refine ⟨19729809051712917300744665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52612824137901112801985773 19729809051712917300744665)
              ·
                refine ⟨14797356788784687975558499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19729809051712917300744665 14797356788784687975558499)
                ·
                  refine ⟨22196035183177031963337749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14797356788784687975558499 22196035183177031963337749)
                  ·
                    refine ⟨1040439149211423373281457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22196035183177031963337749 1040439149211423373281457)
                    ·
                      rfl

theorem cell23_6078744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_6078744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078744 prefixEnd_6078744 := by exact prefixLift 6078744
  have htrace : WordTrace (prefixWord ++ tailWord_6078744) baseStart_6078744 baseEnd_6078744 := by
    simpa [prefixWord, tailWord_6078744, baseEnd_6078744] using wordTrace_append hprefix tailTrace_6078744
  have hstable : (prefixWord ++ tailWord_6078744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078744).length < 2 ^ (prefixWord ++ tailWord_6078744).sum := by decide
  have hdescent : baseEnd_6078744 < baseStart_6078744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078757 : List Nat := [1, 3, 1, 2, 16]
def baseStart_6078757 : Nat := 118140960795 + 6078757 * 2 ^ 59
def prefixEnd_6078757 : Nat := 4983230072969 + 3 ^ 40 * 6078757 * 2
def baseEnd_6078757 : Nat := 4281651746066911617259

theorem tailTrace_6078757 : CollatzResearch.WordTrace tailWord_6078757 prefixEnd_6078757 4281651746066911617259 := by
  unfold tailWord_6078757
  simp only [CollatzResearch.WordTrace]
  refine ⟨221710482038709032887850525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147806988025806021925233683 221710482038709032887850525)
  ·
    refine ⟨83141430764515887332943947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221710482038709032887850525 83141430764515887332943947)
    ·
      refine ⟨124712146146773830999415921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83141430764515887332943947 124712146146773830999415921)
      ·
        refine ⟨93534109610080373249561941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124712146146773830999415921 93534109610080373249561941)
        ·
          refine ⟨4281651746066911617259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 93534109610080373249561941 4281651746066911617259)
          ·
            rfl

theorem cell23_6078757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 16].length) (baseStart_6078757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078757 prefixEnd_6078757 := by exact prefixLift 6078757
  have htrace : WordTrace (prefixWord ++ tailWord_6078757) baseStart_6078757 baseEnd_6078757 := by
    simpa [prefixWord, tailWord_6078757, baseEnd_6078757] using wordTrace_append hprefix tailTrace_6078757
  have hstable : (prefixWord ++ tailWord_6078757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078757).length < 2 ^ (prefixWord ++ tailWord_6078757).sum := by decide
  have hdescent : baseEnd_6078757 < baseStart_6078757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078762 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6078762 : Nat := 118140960795 + 6078762 * 2 ^ 59
def prefixEnd_6078762 : Nat := 4983230072969 + 3 ^ 40 * 6078762 * 2
def baseEnd_6078762 : Nat := 3121326690286051049419289

theorem tailTrace_6078762 : CollatzResearch.WordTrace tailWord_6078762 prefixEnd_6078762 3121326690286051049419289 := by
  unfold tailWord_6078762
  simp only [CollatzResearch.WordTrace]
  refine ⟨55427666100922729685445635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147807109602460612494521693 55427666100922729685445635)
  ·
    refine ⟨83141499151384094528168453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55427666100922729685445635 83141499151384094528168453)
    ·
      refine ⟨15589031090884517724031585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83141499151384094528168453 15589031090884517724031585)
      ·
        refine ⟨11691773318163388293023689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15589031090884517724031585 11691773318163388293023689)
        ·
          refine ⟨8768829988622541219767767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11691773318163388293023689 8768829988622541219767767)
          ·
            refine ⟨13153244982933811829651651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768829988622541219767767 13153244982933811829651651)
            ·
              refine ⟨19729867474400717744477477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13153244982933811829651651 19729867474400717744477477)
              ·
                refine ⟨3699350151450134577089527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19729867474400717744477477 3699350151450134577089527)
                ·
                  refine ⟨5549025227175201865634291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699350151450134577089527 5549025227175201865634291)
                  ·
                    refine ⟨8323537840762802798451437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5549025227175201865634291 8323537840762802798451437)
                    ·
                      refine ⟨3121326690286051049419289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8323537840762802798451437 3121326690286051049419289)
                      ·
                        rfl

theorem cell23_6078762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6078762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078762 prefixEnd_6078762 := by exact prefixLift 6078762
  have htrace : WordTrace (prefixWord ++ tailWord_6078762) baseStart_6078762 baseEnd_6078762 := by
    simpa [prefixWord, tailWord_6078762, baseEnd_6078762] using wordTrace_append hprefix tailTrace_6078762
  have hstable : (prefixWord ++ tailWord_6078762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078762).length < 2 ^ (prefixWord ++ tailWord_6078762).sum := by decide
  have hdescent : baseEnd_6078762 < baseStart_6078762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078801 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_6078801 : Nat := 118140960795 + 6078801 * 2 ^ 59
def prefixEnd_6078801 : Nat := 4983230072969 + 3 ^ 40 * 6078801 * 2
def baseEnd_6078801 : Nat := 3121346716031576396831609

theorem tailTrace_6078801 : CollatzResearch.WordTrace tailWord_6078801 prefixEnd_6078801 3121346716031576396831609 := by
  unfold tailWord_6078801
  simp only [CollatzResearch.WordTrace]
  refine ⟨221712086850549628402452257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147808057900366418934968171 221712086850549628402452257)
  ·
    refine ⟨166284065137912221301839193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221712086850549628402452257 166284065137912221301839193)
    ·
      refine ⟨124713048853434165976379395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166284065137912221301839193 124713048853434165976379395)
      ·
        refine ⟨187069573280151248964569093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124713048853434165976379395 187069573280151248964569093)
        ·
          refine ⟨35075544990028359180856705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187069573280151248964569093 35075544990028359180856705)
          ·
            refine ⟨26306658742521269385642529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35075544990028359180856705 26306658742521269385642529)
            ·
              refine ⟨19729994056890952039231897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26306658742521269385642529 19729994056890952039231897)
              ·
                refine ⟨14797495542668214029423923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19729994056890952039231897 14797495542668214029423923)
                ·
                  refine ⟨22196243314002321044135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14797495542668214029423923 22196243314002321044135885)
                  ·
                    refine ⟨8323591242750870391550957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22196243314002321044135885 8323591242750870391550957)
                    ·
                      refine ⟨3121346716031576396831609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8323591242750870391550957 3121346716031576396831609)
                      ·
                        rfl

theorem cell23_6078801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_6078801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078801 prefixEnd_6078801 := by exact prefixLift 6078801
  have htrace : WordTrace (prefixWord ++ tailWord_6078801) baseStart_6078801 baseEnd_6078801 := by
    simpa [prefixWord, tailWord_6078801, baseEnd_6078801] using wordTrace_append hprefix tailTrace_6078801
  have hstable : (prefixWord ++ tailWord_6078801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078801).length < 2 ^ (prefixWord ++ tailWord_6078801).sum := by decide
  have hdescent : baseEnd_6078801 < baseStart_6078801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078812 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_6078812 : Nat := 118140960795 + 6078812 * 2 ^ 59
def prefixEnd_6078812 : Nat := 4983230072969 + 3 ^ 40 * 6078812 * 2
def baseEnd_6078812 : Nat := 1040450788106258617931353

theorem tailTrace_6078812 : CollatzResearch.WordTrace tailWord_6078812 prefixEnd_6078812 1040450788106258617931353 := by
  unfold tailWord_6078812
  simp only [CollatzResearch.WordTrace]
  refine ⟨110856244026754888640551345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147808325369006518187401793 110856244026754888640551345)
  ·
    refine ⟨83142183020066166480413509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110856244026754888640551345 83142183020066166480413509)
    ·
      refine ⟨15589159316262406215077533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83142183020066166480413509 15589159316262406215077533)
      ·
        refine ⟨5845934743598402330654075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15589159316262406215077533 5845934743598402330654075)
        ·
          refine ⟨8768902115397603495981113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845934743598402330654075 8768902115397603495981113)
          ·
            refine ⟨6576676586548202621985835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8768902115397603495981113 6576676586548202621985835)
            ·
              refine ⟨9865014879822303932978753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576676586548202621985835 9865014879822303932978753)
              ·
                refine ⟨7398761159866727949734065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9865014879822303932978753 7398761159866727949734065)
                ·
                  refine ⟨5549070869900045962300549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7398761159866727949734065 5549070869900045962300549)
                  ·
                    refine ⟨1040450788106258617931353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549070869900045962300549 1040450788106258617931353)
                    ·
                      rfl

theorem cell23_6078812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_6078812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078812 prefixEnd_6078812 := by exact prefixLift 6078812
  have htrace : WordTrace (prefixWord ++ tailWord_6078812) baseStart_6078812 baseEnd_6078812 := by
    simpa [prefixWord, tailWord_6078812, baseEnd_6078812] using wordTrace_append hprefix tailTrace_6078812
  have hstable : (prefixWord ++ tailWord_6078812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078812).length < 2 ^ (prefixWord ++ tailWord_6078812).sum := by decide
  have hdescent : baseEnd_6078812 < baseStart_6078812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078845 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_6078845 : Nat := 118140960795 + 6078845 * 2 ^ 59
def prefixEnd_6078845 : Nat := 4983230072969 + 3 ^ 40 * 6078845 * 2
def baseEnd_6078845 : Nat := 3121369309180374224681407

theorem tailTrace_6078845 : CollatzResearch.WordTrace tailWord_6078845 prefixEnd_6078845 3121369309180374224681407 := by
  unfold tailWord_6078845
  simp only [CollatzResearch.WordTrace]
  refine ⟨221713691662390223917053989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147809127774926815944702659 221713691662390223917053989)
  ·
    refine ⟨41571317186698166984447623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221713691662390223917053989 41571317186698166984447623)
    ·
      refine ⟨62356975780047250476671435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41571317186698166984447623 62356975780047250476671435)
      ·
        refine ⟨93535463670070875715007153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62356975780047250476671435 93535463670070875715007153)
        ·
          refine ⟨70151597752553156786255365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93535463670070875715007153 70151597752553156786255365)
          ·
            refine ⟨13153424578603716897422881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70151597752553156786255365 13153424578603716897422881)
            ·
              refine ⟨9865068433952787673067161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13153424578603716897422881 9865068433952787673067161)
              ·
                refine ⟨7398801325464590754800371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9865068433952787673067161 7398801325464590754800371)
                ·
                  refine ⟨11098201988196886132200557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398801325464590754800371 11098201988196886132200557)
                  ·
                    refine ⟨4161825745573832299575209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11098201988196886132200557 4161825745573832299575209)
                    ·
                      refine ⟨3121369309180374224681407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161825745573832299575209 3121369309180374224681407)
                      ·
                        rfl

theorem cell23_6078845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_6078845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078845 prefixEnd_6078845 := by exact prefixLift 6078845
  have htrace : WordTrace (prefixWord ++ tailWord_6078845) baseStart_6078845 baseEnd_6078845 := by
    simpa [prefixWord, tailWord_6078845, baseEnd_6078845] using wordTrace_append hprefix tailTrace_6078845
  have hstable : (prefixWord ++ tailWord_6078845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078845).length < 2 ^ (prefixWord ++ tailWord_6078845).sum := by decide
  have hdescent : baseEnd_6078845 < baseStart_6078845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078870 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6078870 : Nat := 118140960795 + 6078870 * 2 ^ 59
def prefixEnd_6078870 : Nat := 4983230072969 + 3 ^ 40 * 6078870 * 2
def baseEnd_6078870 : Nat := 3121382146196736626868793

theorem tailTrace_6078870 : CollatzResearch.WordTrace tailWord_6078870 prefixEnd_6078870 3121382146196736626868793 := by
  unfold tailWord_6078870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857162717956228324169629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147809735658199768791142709 13857162717956228324169629)
  ·
    refine ⟨5196436019233585621563611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13857162717956228324169629 5196436019233585621563611)
    ·
      refine ⟨7794654028850378432345417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196436019233585621563611 7794654028850378432345417)
      ·
        refine ⟨5845990521637783824259063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794654028850378432345417 5845990521637783824259063)
        ·
          refine ⟨8768985782456675736388595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845990521637783824259063 8768985782456675736388595)
          ·
            refine ⟨13153478673685013604582893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768985782456675736388595 13153478673685013604582893)
            ·
              refine ⟨4932554502631880101718585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13153478673685013604582893 4932554502631880101718585)
              ·
                refine ⟨3699415876973910076288939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932554502631880101718585 3699415876973910076288939)
                ·
                  refine ⟨5549123815460865114433409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699415876973910076288939 5549123815460865114433409)
                  ·
                    refine ⟨4161842861595648835825057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549123815460865114433409 4161842861595648835825057)
                    ·
                      refine ⟨3121382146196736626868793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4161842861595648835825057 3121382146196736626868793)
                      ·
                        rfl

theorem cell23_6078870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6078870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078870 prefixEnd_6078870 := by exact prefixLift 6078870
  have htrace : WordTrace (prefixWord ++ tailWord_6078870) baseStart_6078870 baseEnd_6078870 := by
    simpa [prefixWord, tailWord_6078870, baseEnd_6078870] using wordTrace_append hprefix tailTrace_6078870
  have hstable : (prefixWord ++ tailWord_6078870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078870).length < 2 ^ (prefixWord ++ tailWord_6078870).sum := by decide
  have hdescent : baseEnd_6078870 < baseStart_6078870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078904 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_6078904 : Nat := 118140960795 + 6078904 * 2 ^ 59
def prefixEnd_6078904 : Nat := 4983230072969 + 3 ^ 40 * 6078904 * 2
def baseEnd_6078904 : Nat := 3121399604538989493843635

theorem tailTrace_6078904 : CollatzResearch.WordTrace tailWord_6078904 prefixEnd_6078904 3121399604538989493843635 := by
  unfold tailWord_6078904
  simp only [CollatzResearch.WordTrace]
  refine ⟨110857921784588238496725883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147810562379450984662301177 110857921784588238496725883)
  ·
    refine ⟨166286882676882357745088825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110857921784588238496725883 166286882676882357745088825)
    ·
      refine ⟨124715162007661768308816619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166286882676882357745088825 124715162007661768308816619)
      ·
        refine ⟨187072743011492652463224929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124715162007661768308816619 187072743011492652463224929)
        ·
          refine ⟨140304557258619489347418697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187072743011492652463224929 140304557258619489347418697)
          ·
            refine ⟨105228417943964617010564023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140304557258619489347418697 105228417943964617010564023)
            ·
              refine ⟨157842626915946925515846035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105228417943964617010564023 157842626915946925515846035)
              ·
                refine ⟨236763940373920388273769053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157842626915946925515846035 236763940373920388273769053)
                ·
                  refine ⟨88786477640220145602663395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236763940373920388273769053 88786477640220145602663395)
                  ·
                    refine ⟨133179716460330218403995093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88786477640220145602663395 133179716460330218403995093)
                    ·
                      refine ⟨3121399604538989493843635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133179716460330218403995093 3121399604538989493843635)
                      ·
                        rfl

theorem cell23_6078904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_6078904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078904 prefixEnd_6078904 := by exact prefixLift 6078904
  have htrace : WordTrace (prefixWord ++ tailWord_6078904) baseStart_6078904 baseEnd_6078904 := by
    simpa [prefixWord, tailWord_6078904, baseEnd_6078904] using wordTrace_append hprefix tailTrace_6078904
  have hstable : (prefixWord ++ tailWord_6078904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078904).length < 2 ^ (prefixWord ++ tailWord_6078904).sum := by decide
  have hdescent : baseEnd_6078904 < baseStart_6078904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078932 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 5]
def baseStart_6078932 : Nat := 118140960795 + 6078932 * 2 ^ 59
def prefixEnd_6078932 : Nat := 4983230072969 + 3 ^ 40 * 6078932 * 2
def baseEnd_6078932 : Nat := 346823775777479487143723

theorem tailTrace_6078932 : CollatzResearch.WordTrace tailWord_6078932 prefixEnd_6078932 346823775777479487143723 := by
  unfold tailWord_6078932
  simp only [CollatzResearch.WordTrace]
  refine ⟨110858432406537518887735525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147811243208716691850314033 110858432406537518887735525)
  ·
    refine ⟨20785956076225784791450411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110858432406537518887735525 20785956076225784791450411)
    ·
      refine ⟨31178934114338677187175617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20785956076225784791450411 31178934114338677187175617)
      ·
        refine ⟨23384200585754007890381713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31178934114338677187175617 23384200585754007890381713)
        ·
          refine ⟨17538150439315505917786285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23384200585754007890381713 17538150439315505917786285)
          ·
            refine ⟨6576806414743314719169857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17538150439315505917786285 6576806414743314719169857)
            ·
              refine ⟨4932604811057486039377393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6576806414743314719169857 4932604811057486039377393)
              ·
                refine ⟨3699453608293114529533045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932604811057486039377393 3699453608293114529533045)
                ·
                  refine ⟨346823775777479487143723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699453608293114529533045 346823775777479487143723)
                  ·
                    rfl

theorem cell23_6078932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_6078932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078932 prefixEnd_6078932 := by exact prefixLift 6078932
  have htrace : WordTrace (prefixWord ++ tailWord_6078932) baseStart_6078932 baseEnd_6078932 := by
    simpa [prefixWord, tailWord_6078932, baseEnd_6078932] using wordTrace_append hprefix tailTrace_6078932
  have hstable : (prefixWord ++ tailWord_6078932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078932).length < 2 ^ (prefixWord ++ tailWord_6078932).sum := by decide
  have hdescent : baseEnd_6078932 < baseStart_6078932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078958 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6078958 : Nat := 118140960795 + 6078958 * 2 ^ 59
def prefixEnd_6078958 : Nat := 4983230072969 + 3 ^ 40 * 6078958 * 2
def baseEnd_6078958 : Nat := 1040475777498110760856129

theorem tailTrace_6078958 : CollatzResearch.WordTrace tailWord_6078958 prefixEnd_6078958 1040475777498110760856129 := by
  unfold tailWord_6078958
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714726638872605526989691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147811875407320562810611685 27714726638872605526989691)
  ·
    refine ⟨41572089958308908290484537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27714726638872605526989691 41572089958308908290484537)
    ·
      refine ⟨31179067468731681217863403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41572089958308908290484537 31179067468731681217863403)
      ·
        refine ⟨46768601203097521826795105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31179067468731681217863403 46768601203097521826795105)
        ·
          refine ⟨35076450902323141370096329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46768601203097521826795105 35076450902323141370096329)
          ·
            refine ⟨26307338176742356027572247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35076450902323141370096329 26307338176742356027572247)
            ·
              refine ⟨39461007265113534041358371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26307338176742356027572247 39461007265113534041358371)
              ·
                refine ⟨59191510897670301062037557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39461007265113534041358371 59191510897670301062037557)
                ·
                  refine ⟨5549204146656590724566021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59191510897670301062037557 5549204146656590724566021)
                  ·
                    refine ⟨1040475777498110760856129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549204146656590724566021 1040475777498110760856129)
                    ·
                      rfl

theorem cell23_6078958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6078958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078958 prefixEnd_6078958 := by exact prefixLift 6078958
  have htrace : WordTrace (prefixWord ++ tailWord_6078958) baseStart_6078958 baseEnd_6078958 := by
    simpa [prefixWord, tailWord_6078958, baseEnd_6078958] using wordTrace_append hprefix tailTrace_6078958
  have hstable : (prefixWord ++ tailWord_6078958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078958).length < 2 ^ (prefixWord ++ tailWord_6078958).sum := by decide
  have hdescent : baseEnd_6078958 < baseStart_6078958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078962 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_6078962 : Nat := 118140960795 + 6078962 * 2 ^ 59
def prefixEnd_6078962 : Nat := 4983230072969 + 3 ^ 40 * 6078962 * 2
def baseEnd_6078962 : Nat := 1040476462138983422306123

theorem tailTrace_6078962 : CollatzResearch.WordTrace tailWord_6078962 prefixEnd_6078962 1040476462138983422306123 := by
  unfold tailWord_6078962
  simp only [CollatzResearch.WordTrace]
  refine ⟨55429489750741588224765785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147811972668644235266042093 55429489750741588224765785)
  ·
    refine ⟨41572117313056191168574339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55429489750741588224765785 41572117313056191168574339)
    ·
      refine ⟨62358175969584286752861509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41572117313056191168574339 62358175969584286752861509)
      ·
        refine ⟨11692157994297053766161533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62358175969584286752861509 11692157994297053766161533)
        ·
          refine ⟨4384559247861395162310575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11692157994297053766161533 4384559247861395162310575)
          ·
            refine ⟨6576838871792092743465863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384559247861395162310575 6576838871792092743465863)
            ·
              refine ⟨9865258307688139115198795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576838871792092743465863 9865258307688139115198795)
              ·
                refine ⟨14797887461532208672798193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9865258307688139115198795 14797887461532208672798193)
                ·
                  refine ⟨11098415596149156504598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14797887461532208672798193 11098415596149156504598645)
                  ·
                    refine ⟨1040476462138983422306123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11098415596149156504598645 1040476462138983422306123)
                    ·
                      rfl

theorem cell23_6078962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_6078962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078962 prefixEnd_6078962 := by exact prefixLift 6078962
  have htrace : WordTrace (prefixWord ++ tailWord_6078962) baseStart_6078962 baseEnd_6078962 := by
    simpa [prefixWord, tailWord_6078962, baseEnd_6078962] using wordTrace_append hprefix tailTrace_6078962
  have hstable : (prefixWord ++ tailWord_6078962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078962).length < 2 ^ (prefixWord ++ tailWord_6078962).sum := by decide
  have hdescent : baseEnd_6078962 < baseStart_6078962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078965 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6078965 : Nat := 118140960795 + 6078965 * 2 ^ 59
def prefixEnd_6078965 : Nat := 4983230072969 + 3 ^ 40 * 6078965 * 2
def baseEnd_6078965 : Nat := 3121430926858913755180855

theorem tailTrace_6078965 : CollatzResearch.WordTrace tailWord_6078965 prefixEnd_6078965 3121430926858913755180855 := by
  unfold tailWord_6078965
  simp only [CollatzResearch.WordTrace]
  refine ⟨221718068421955484411422349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147812045614636989607614899 221718068421955484411422349)
  ·
    refine ⟨83144275658233306654283381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221718068421955484411422349 83144275658233306654283381)
    ·
      refine ⟨7794775842959372498839067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83144275658233306654283381 7794775842959372498839067)
      ·
        refine ⟨11692163764439058748258601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7794775842959372498839067 11692163764439058748258601)
        ·
          refine ⟨8769122823329294061193951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11692163764439058748258601 8769122823329294061193951)
          ·
            refine ⟨13153684234993941091790927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769122823329294061193951 13153684234993941091790927)
            ·
              refine ⟨19730526352490911637686391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13153684234993941091790927 19730526352490911637686391)
              ·
                refine ⟨29595789528736367456529587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19730526352490911637686391 29595789528736367456529587)
                ·
                  refine ⟨44393684293104551184794381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29595789528736367456529587 44393684293104551184794381)
                  ·
                    refine ⟨16647631609914206694297893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44393684293104551184794381 16647631609914206694297893)
                    ·
                      refine ⟨3121430926858913755180855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16647631609914206694297893 3121430926858913755180855)
                      ·
                        rfl

theorem cell23_6078965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6078965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078965 prefixEnd_6078965 := by exact prefixLift 6078965
  have htrace : WordTrace (prefixWord ++ tailWord_6078965) baseStart_6078965 baseEnd_6078965 := by
    simpa [prefixWord, tailWord_6078965, baseEnd_6078965] using wordTrace_append hprefix tailTrace_6078965
  have hstable : (prefixWord ++ tailWord_6078965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078965).length < 2 ^ (prefixWord ++ tailWord_6078965).sum := by decide
  have hdescent : baseEnd_6078965 < baseStart_6078965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078975 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 1, 4]
def baseStart_6078975 : Nat := 118140960795 + 6078975 * 2 ^ 59
def prefixEnd_6078975 : Nat := 4983230072969 + 3 ^ 40 * 6078975 * 2
def baseEnd_6078975 : Nat := 1040478687221819572018603

theorem tailTrace_6078975 : CollatzResearch.WordTrace tailWord_6078975 prefixEnd_6078975 1040478687221819572018603 := by
  unfold tailWord_6078975
  simp only [CollatzResearch.WordTrace]
  refine ⟨221718433151919256119286379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147812288767946170746190919 221718433151919256119286379)
  ·
    refine ⟨332577649727878884178929569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221718433151919256119286379 332577649727878884178929569)
    ·
      refine ⟨249433237295909163134197177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332577649727878884178929569 249433237295909163134197177)
      ·
        refine ⟨187074927971931872350647883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249433237295909163134197177 187074927971931872350647883)
        ·
          refine ⟨280612391957897808525971825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187074927971931872350647883 280612391957897808525971825)
          ·
            refine ⟨210459293968423356394478869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280612391957897808525971825 210459293968423356394478869)
            ·
              refine ⟨9865279404769844830991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210459293968423356394478869 9865279404769844830991197)
              ·
                refine ⟨3699479776788691811621699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9865279404769844830991197 3699479776788691811621699)
                ·
                  refine ⟨5549219665183037717432549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699479776788691811621699 5549219665183037717432549)
                  ·
                    refine ⟨1040478687221819572018603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549219665183037717432549 1040478687221819572018603)
                    ·
                      rfl

theorem cell23_6078975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_6078975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078975 prefixEnd_6078975 := by exact prefixLift 6078975
  have htrace : WordTrace (prefixWord ++ tailWord_6078975) baseStart_6078975 baseEnd_6078975 := by
    simpa [prefixWord, tailWord_6078975, baseEnd_6078975] using wordTrace_append hprefix tailTrace_6078975
  have hstable : (prefixWord ++ tailWord_6078975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078975).length < 2 ^ (prefixWord ++ tailWord_6078975).sum := by decide
  have hdescent : baseEnd_6078975 < baseStart_6078975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6078988 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 6]
def baseStart_6078988 : Nat := 118140960795 + 6078988 * 2 ^ 59
def prefixEnd_6078988 : Nat := 4983230072969 + 3 ^ 40 * 6078988 * 2
def baseEnd_6078988 : Nat := 346826970768218573910361

theorem tailTrace_6078988 : CollatzResearch.WordTrace tailWord_6078988 prefixEnd_6078988 346826970768218573910361 := by
  unfold tailWord_6078988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110859453650436079669754809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147812604867248106226339745 110859453650436079669754809)
  ·
    refine ⟨83144590237827059752316107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110859453650436079669754809 83144590237827059752316107)
    ·
      refine ⟨124716885356740589628474161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83144590237827059752316107 124716885356740589628474161)
      ·
        refine ⟨93537664017555442221355621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124716885356740589628474161 93537664017555442221355621)
        ·
          refine ⟨17538312003291645416504179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93537664017555442221355621 17538312003291645416504179)
          ·
            refine ⟨26307468004937468124756269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17538312003291645416504179 26307468004937468124756269)
            ·
              refine ⟨9865300501851550546783601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26307468004937468124756269 9865300501851550546783601)
              ·
                refine ⟨7398975376388662910087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9865300501851550546783601 7398975376388662910087701)
                ·
                  refine ⟨346826970768218573910361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7398975376388662910087701 346826970768218573910361)
                  ·
                    rfl

theorem cell23_6078988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_6078988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6078988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6078988 prefixEnd_6078988 := by exact prefixLift 6078988
  have htrace : WordTrace (prefixWord ++ tailWord_6078988) baseStart_6078988 baseEnd_6078988 := by
    simpa [prefixWord, tailWord_6078988, baseEnd_6078988] using wordTrace_append hprefix tailTrace_6078988
  have hstable : (prefixWord ++ tailWord_6078988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6078988).length < 2 ^ (prefixWord ++ tailWord_6078988).sum := by decide
  have hdescent : baseEnd_6078988 < baseStart_6078988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6078988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079005 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 6]
def baseStart_6079005 : Nat := 118140960795 + 6079005 * 2 ^ 59
def prefixEnd_6079005 : Nat := 4983230072969 + 3 ^ 40 * 6079005 * 2
def baseEnd_6079005 : Nat := 346827940676121510964519

theorem tailTrace_6079005 : CollatzResearch.WordTrace tailWord_6079005 prefixEnd_6079005 346827940676121510964519 := by
  unfold tailWord_6079005
  simp only [CollatzResearch.WordTrace]
  refine ⟨221719527341810571242878469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147813018227873714161918979 221719527341810571242878469)
  ·
    refine ⟨41572411376589482108039713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221719527341810571242878469 41572411376589482108039713)
    ·
      refine ⟨31179308532442111581029785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41572411376589482108039713 31179308532442111581029785)
      ·
        refine ⟨23384481399331583685772339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31179308532442111581029785 23384481399331583685772339)
        ·
          refine ⟨35076722098997375528658509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23384481399331583685772339 35076722098997375528658509)
          ·
            refine ⟨13153770787124015823246941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35076722098997375528658509 13153770787124015823246941)
            ·
              refine ⟨4932664045171505933717603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13153770787124015823246941 4932664045171505933717603)
              ·
                refine ⟨7398996067757258900576405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932664045171505933717603 7398996067757258900576405)
                ·
                  refine ⟨346827940676121510964519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7398996067757258900576405 346827940676121510964519)
                  ·
                    rfl

theorem cell23_6079005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_6079005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079005 prefixEnd_6079005 := by exact prefixLift 6079005
  have htrace : WordTrace (prefixWord ++ tailWord_6079005) baseStart_6079005 baseEnd_6079005 := by
    simpa [prefixWord, tailWord_6079005, baseEnd_6079005] using wordTrace_append hprefix tailTrace_6079005
  have hstable : (prefixWord ++ tailWord_6079005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079005).length < 2 ^ (prefixWord ++ tailWord_6079005).sum := by decide
  have hdescent : baseEnd_6079005 < baseStart_6079005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079031 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 6]
def baseStart_6079031 : Nat := 118140960795 + 6079031 * 2 ^ 59
def prefixEnd_6079031 : Nat := 4983230072969 + 3 ^ 40 * 6079031 * 2
def baseEnd_6079031 : Nat := 1040488272194036832318517

theorem tailTrace_6079031 : CollatzResearch.WordTrace tailWord_6079031 prefixEnd_6079031 1040488272194036832318517 := by
  unfold tailWord_6079031
  simp only [CollatzResearch.WordTrace]
  refine ⟨221720475639716377683324947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147813650426477585122216631 221720475639716377683324947)
  ·
    refine ⟨332580713459574566524987421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221720475639716377683324947 332580713459574566524987421)
    ·
      refine ⟨124717767547340462446870283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332580713459574566524987421 124717767547340462446870283)
      ·
        refine ⟨187076651321010693670305425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124717767547340462446870283 187076651321010693670305425)
        ·
          refine ⟨140307488490758020252729069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187076651321010693670305425 140307488490758020252729069)
          ·
            refine ⟨52615308184034257594773401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140307488490758020252729069 52615308184034257594773401)
            ·
              refine ⟨39461481138025693196080051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52615308184034257594773401 39461481138025693196080051)
              ·
                refine ⟨59192221707038539794120077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39461481138025693196080051 59192221707038539794120077)
                ·
                  refine ⟨22197083140139452422795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59192221707038539794120077 22197083140139452422795029)
                  ·
                    refine ⟨1040488272194036832318517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22197083140139452422795029 1040488272194036832318517)
                    ·
                      rfl

theorem cell23_6079031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_6079031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079031 prefixEnd_6079031 := by exact prefixLift 6079031
  have htrace : WordTrace (prefixWord ++ tailWord_6079031) baseStart_6079031 baseEnd_6079031 := by
    simpa [prefixWord, tailWord_6079031, baseEnd_6079031] using wordTrace_append hprefix tailTrace_6079031
  have hstable : (prefixWord ++ tailWord_6079031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079031).length < 2 ^ (prefixWord ++ tailWord_6079031).sum := by decide
  have hdescent : baseEnd_6079031 < baseStart_6079031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079051 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_6079051 : Nat := 118140960795 + 6079051 * 2 ^ 59
def prefixEnd_6079051 : Nat := 4983230072969 + 3 ^ 40 * 6079051 * 2
def baseEnd_6079051 : Nat := 3121475086195200418705459

theorem tailTrace_6079051 : CollatzResearch.WordTrace tailWord_6079051 prefixEnd_6079051 3121475086195200418705459 := by
  unfold tailWord_6079051
  simp only [CollatzResearch.WordTrace]
  refine ⟨221721205099643921099053007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147814136733095947399368671 221721205099643921099053007)
  ·
    refine ⟨332581807649465881648579511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221721205099643921099053007 332581807649465881648579511)
    ·
      refine ⟨498872711474198822472869267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332581807649465881648579511 498872711474198822472869267)
      ·
        refine ⟨748309067211298233709303901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498872711474198822472869267 748309067211298233709303901)
        ·
          refine ⟨280615900204236837640988963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 748309067211298233709303901 280615900204236837640988963)
          ·
            refine ⟨420923850306355256461483445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280615900204236837640988963 420923850306355256461483445)
            ·
              refine ⟨39461610966220805293264073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420923850306355256461483445 39461610966220805293264073)
              ·
                refine ⟨29596208224665603969948055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39461610966220805293264073 29596208224665603969948055)
                ·
                  refine ⟨44394312336998405954922083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29596208224665603969948055 44394312336998405954922083)
                  ·
                    refine ⟨66591468505497608932383125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44394312336998405954922083 66591468505497608932383125)
                    ·
                      refine ⟨3121475086195200418705459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66591468505497608932383125 3121475086195200418705459)
                      ·
                        rfl

theorem cell23_6079051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_6079051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079051 prefixEnd_6079051 := by exact prefixLift 6079051
  have htrace : WordTrace (prefixWord ++ tailWord_6079051) baseStart_6079051 baseEnd_6079051 := by
    simpa [prefixWord, tailWord_6079051, baseEnd_6079051] using wordTrace_append hprefix tailTrace_6079051
  have hstable : (prefixWord ++ tailWord_6079051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079051).length < 2 ^ (prefixWord ++ tailWord_6079051).sum := by decide
  have hdescent : baseEnd_6079051 < baseStart_6079051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079058 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6079058 : Nat := 118140960795 + 6079058 * 2 ^ 59
def prefixEnd_6079058 : Nat := 4983230072969 + 3 ^ 40 * 6079058 * 2
def baseEnd_6079058 : Nat := 3121478680559781891317927

theorem tailTrace_6079058 : CollatzResearch.WordTrace tailWord_6079058 prefixEnd_6079058 3121478680559781891317927 := by
  unfold tailWord_6079058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55430365102654640323639457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147814306940412374196371885 55430365102654640323639457)
  ·
    refine ⟨41572773826990980242729593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55430365102654640323639457 41572773826990980242729593)
    ·
      refine ⟨31179580370243235182047195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41572773826990980242729593 31179580370243235182047195)
      ·
        refine ⟨46769370555364852773070793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31179580370243235182047195 46769370555364852773070793)
        ·
          refine ⟨35077027916523639579803095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46769370555364852773070793 35077027916523639579803095)
          ·
            refine ⟨52615541874785459369704643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35077027916523639579803095 52615541874785459369704643)
            ·
              refine ⟨78923312812178189054556965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52615541874785459369704643 78923312812178189054556965)
              ·
                refine ⟨14798121152283410447729431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78923312812178189054556965 14798121152283410447729431)
                ·
                  refine ⟨22197181728425115671594147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14798121152283410447729431 22197181728425115671594147)
                  ·
                    refine ⟨33295772592637673507391221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22197181728425115671594147 33295772592637673507391221)
                    ·
                      refine ⟨3121478680559781891317927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33295772592637673507391221 3121478680559781891317927)
                      ·
                        rfl

theorem cell23_6079058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6079058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079058 prefixEnd_6079058 := by exact prefixLift 6079058
  have htrace : WordTrace (prefixWord ++ tailWord_6079058) baseStart_6079058 baseEnd_6079058 := by
    simpa [prefixWord, tailWord_6079058, baseEnd_6079058] using wordTrace_append hprefix tailTrace_6079058
  have hstable : (prefixWord ++ tailWord_6079058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079058).length < 2 ^ (prefixWord ++ tailWord_6079058).sum := by decide
  have hdescent : baseEnd_6079058 < baseStart_6079058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079061 : List Nat := [1, 3, 2, 2, 1, 1, 3, 10]
def baseStart_6079061 : Nat := 118140960795 + 6079061 * 2 ^ 59
def prefixEnd_6079061 : Nat := 4983230072969 + 3 ^ 40 * 6079061 * 2
def baseEnd_6079061 : Nat := 115610378555620199243719

theorem tailTrace_6079061 : CollatzResearch.WordTrace tailWord_6079061 prefixEnd_6079061 115610378555620199243719 := by
  unfold tailWord_6079061
  simp only [CollatzResearch.WordTrace]
  refine ⟨221721569829607692806917037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147814379886405128537944691 221721569829607692806917037)
  ·
    refine ⟨83145588686102884802593889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221721569829607692806917037 83145588686102884802593889)
    ·
      refine ⟨62359191514577163601945417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83145588686102884802593889 62359191514577163601945417)
      ·
        refine ⟨46769393635932872701459063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62359191514577163601945417 46769393635932872701459063)
        ·
          refine ⟨70154090453899309052188595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46769393635932872701459063 70154090453899309052188595)
          ·
            refine ⟨105231135680848963578282893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70154090453899309052188595 105231135680848963578282893)
            ·
              refine ⟨39461675880318361341856085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105231135680848963578282893 39461675880318361341856085)
              ·
                refine ⟨115610378555620199243719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39461675880318361341856085 115610378555620199243719)
                ·
                  rfl

theorem cell23_6079061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 10].length) (baseStart_6079061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079061 prefixEnd_6079061 := by exact prefixLift 6079061
  have htrace : WordTrace (prefixWord ++ tailWord_6079061) baseStart_6079061 baseEnd_6079061 := by
    simpa [prefixWord, tailWord_6079061, baseEnd_6079061] using wordTrace_append hprefix tailTrace_6079061
  have hstable : (prefixWord ++ tailWord_6079061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079061).length < 2 ^ (prefixWord ++ tailWord_6079061).sum := by decide
  have hdescent : baseEnd_6079061 < baseStart_6079061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079085 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6079085 : Nat := 118140960795 + 6079085 * 2 ^ 59
def prefixEnd_6079085 : Nat := 4983230072969 + 3 ^ 40 * 6079085 * 2
def baseEnd_6079085 : Nat := 3121492544537453285680303

theorem tailTrace_6079085 : CollatzResearch.WordTrace tailWord_6079085 prefixEnd_6079085 3121492544537453285680303 := by
  unfold tailWord_6079085
  simp only [CollatzResearch.WordTrace]
  refine ⟨221722445181520744905790709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147814963454347163270527139 221722445181520744905790709)
  ·
    refine ⟨20786479235767569834917879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221722445181520744905790709 20786479235767569834917879)
    ·
      refine ⟨31179718853651354752376819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786479235767569834917879 31179718853651354752376819)
      ·
        refine ⟨46769578280477032128565229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31179718853651354752376819 46769578280477032128565229)
        ·
          refine ⟨17538591855178887048211961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46769578280477032128565229 17538591855178887048211961)
          ·
            refine ⟨13153943891384165286158971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17538591855178887048211961 13153943891384165286158971)
            ·
              refine ⟨19730915837076247929238457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13153943891384165286158971 19730915837076247929238457)
              ·
                refine ⟨14798186877807185946928843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19730915837076247929238457 14798186877807185946928843)
                ·
                  refine ⟨22197280316710778920393265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14798186877807185946928843 22197280316710778920393265)
                  ·
                    refine ⟨16647960237533084190294949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22197280316710778920393265 16647960237533084190294949)
                    ·
                      refine ⟨3121492544537453285680303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16647960237533084190294949 3121492544537453285680303)
                      ·
                        rfl

theorem cell23_6079085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6079085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079085 prefixEnd_6079085 := by exact prefixLift 6079085
  have htrace : WordTrace (prefixWord ++ tailWord_6079085) baseStart_6079085 baseEnd_6079085 := by
    simpa [prefixWord, tailWord_6079085, baseEnd_6079085] using wordTrace_append hprefix tailTrace_6079085
  have hstable : (prefixWord ++ tailWord_6079085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079085).length < 2 ^ (prefixWord ++ tailWord_6079085).sum := by decide
  have hdescent : baseEnd_6079085 < baseStart_6079085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079108 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_6079108 : Nat := 118140960795 + 6079108 * 2 ^ 59
def prefixEnd_6079108 : Nat := 4983230072969 + 3 ^ 40 * 6079108 * 2
def baseEnd_6079108 : Nat := 1040501451530835565230899

theorem tailTrace_6079108 : CollatzResearch.WordTrace tailWord_6079108 prefixEnd_6079108 1040501451530835565230899 := by
  unfold tailWord_6079108
  simp only [CollatzResearch.WordTrace]
  refine ⟨110861642030218709916938989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147815522706958279889251985 110861642030218709916938989)
  ·
    refine ⟨41573115761332016218852121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110861642030218709916938989 41573115761332016218852121)
    ·
      refine ⟨31179836820999012164139091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41573115761332016218852121 31179836820999012164139091)
      ·
        refine ⟨46769755231498518246208637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31179836820999012164139091 46769755231498518246208637)
        ·
          refine ⟨17538658211811944342328239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46769755231498518246208637 17538658211811944342328239)
          ·
            refine ⟨26307987317717916513492359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17538658211811944342328239 26307987317717916513492359)
            ·
              refine ⟨39461980976576874770238539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26307987317717916513492359 39461980976576874770238539)
              ·
                refine ⟨59192971464865312155357809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39461980976576874770238539 59192971464865312155357809)
                ·
                  refine ⟨44394728598648984116518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59192971464865312155357809 44394728598648984116518357)
                  ·
                    refine ⟨1040501451530835565230899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44394728598648984116518357 1040501451530835565230899)
                    ·
                      rfl

theorem cell23_6079108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_6079108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079108 prefixEnd_6079108 := by exact prefixLift 6079108
  have htrace : WordTrace (prefixWord ++ tailWord_6079108) baseStart_6079108 baseEnd_6079108 := by
    simpa [prefixWord, tailWord_6079108, baseEnd_6079108] using wordTrace_append hprefix tailTrace_6079108
  have hstable : (prefixWord ++ tailWord_6079108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079108).length < 2 ^ (prefixWord ++ tailWord_6079108).sum := by decide
  have hdescent : baseEnd_6079108 < baseStart_6079108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079122 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6079122 : Nat := 118140960795 + 6079122 * 2 ^ 59
def prefixEnd_6079122 : Nat := 4983230072969 + 3 ^ 40 * 6079122 * 2
def baseEnd_6079122 : Nat := 3121511543321669640917633

theorem tailTrace_6079122 : CollatzResearch.WordTrace tailWord_6079122 prefixEnd_6079122 3121511543321669640917633 := by
  unfold tailWord_6079122
  simp only [CollatzResearch.WordTrace]
  refine ⟨55430948670596675056221905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147815863121591133483258413 55430948670596675056221905)
  ·
    refine ⟨41573211502947506292166429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55430948670596675056221905 41573211502947506292166429)
    ·
      refine ⟨15589954313605314859562411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41573211502947506292166429 15589954313605314859562411)
      ·
        refine ⟨23384931470407972289343617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15589954313605314859562411 23384931470407972289343617)
        ·
          refine ⟨17538698602805979217007713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23384931470407972289343617 17538698602805979217007713)
          ·
            refine ⟨13154023952104484412755785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17538698602805979217007713 13154023952104484412755785)
            ·
              refine ⟨9865517964078363309566839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13154023952104484412755785 9865517964078363309566839)
              ·
                refine ⟨14798276946117544964350259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9865517964078363309566839 14798276946117544964350259)
                ·
                  refine ⟨22197415419176317446525389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14798276946117544964350259 22197415419176317446525389)
                  ·
                    refine ⟨8324030782191119042447021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22197415419176317446525389 8324030782191119042447021)
                    ·
                      refine ⟨3121511543321669640917633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324030782191119042447021 3121511543321669640917633)
                      ·
                        rfl

theorem cell23_6079122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6079122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079122 prefixEnd_6079122 := by exact prefixLift 6079122
  have htrace : WordTrace (prefixWord ++ tailWord_6079122) baseStart_6079122 baseEnd_6079122 := by
    simpa [prefixWord, tailWord_6079122, baseEnd_6079122] using wordTrace_append hprefix tailTrace_6079122
  have hstable : (prefixWord ++ tailWord_6079122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079122).length < 2 ^ (prefixWord ++ tailWord_6079122).sum := by decide
  have hdescent : baseEnd_6079122 < baseStart_6079122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079128 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6079128 : Nat := 118140960795 + 6079128 * 2 ^ 59
def prefixEnd_6079128 : Nat := 4983230072969 + 3 ^ 40 * 6079128 * 2
def baseEnd_6079128 : Nat := 3121514624205596617442605

theorem tailTrace_6079128 : CollatzResearch.WordTrace tailWord_6079128 prefixEnd_6079128 3121514624205596617442605 := by
  unfold tailWord_6079128
  simp only [CollatzResearch.WordTrace]
  refine ⟨110862006760182481624803019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147816009013576642166404025 110862006760182481624803019)
  ·
    refine ⟨166293010140273722437204529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110862006760182481624803019 166293010140273722437204529)
    ·
      refine ⟨124719757605205291827903397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166293010140273722437204529 124719757605205291827903397)
      ·
        refine ⟨23384954550975992217731887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124719757605205291827903397 23384954550975992217731887)
        ·
          refine ⟨35077431826463988326597831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23384954550975992217731887 35077431826463988326597831)
          ·
            refine ⟨52616147739695982489896747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35077431826463988326597831 52616147739695982489896747)
            ·
              refine ⟨78924221609543973734845121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52616147739695982489896747 78924221609543973734845121)
              ·
                refine ⟨59193166207157980301133841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78924221609543973734845121 59193166207157980301133841)
                ·
                  refine ⟨44394874655368485225850381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59193166207157980301133841 44394874655368485225850381)
                  ·
                    refine ⟨16648077995763181959693893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44394874655368485225850381 16648077995763181959693893)
                    ·
                      refine ⟨3121514624205596617442605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16648077995763181959693893 3121514624205596617442605)
                      ·
                        rfl

theorem cell23_6079128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6079128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079128 prefixEnd_6079128 := by exact prefixLift 6079128
  have htrace : WordTrace (prefixWord ++ tailWord_6079128) baseStart_6079128 baseEnd_6079128 := by
    simpa [prefixWord, tailWord_6079128, baseEnd_6079128] using wordTrace_append hprefix tailTrace_6079128
  have hstable : (prefixWord ++ tailWord_6079128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079128).length < 2 ^ (prefixWord ++ tailWord_6079128).sum := by decide
  have hdescent : baseEnd_6079128 < baseStart_6079128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079132 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6079132 : Nat := 118140960795 + 6079132 * 2 ^ 59
def prefixEnd_6079132 : Nat := 4983230072969 + 3 ^ 40 * 6079132 * 2
def baseEnd_6079132 : Nat := 3121516678128214601792587

theorem tailTrace_6079132 : CollatzResearch.WordTrace tailWord_6079132 prefixEnd_6079132 3121516678128214601792587 := by
  unfold tailWord_6079132
  simp only [CollatzResearch.WordTrace]
  refine ⟨110862079706175235966375825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147816106274900314621834433 110862079706175235966375825)
  ·
    refine ⟨83146559779631426974781869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110862079706175235966375825 83146559779631426974781869)
    ·
      refine ⟨31179959917361785115543201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83146559779631426974781869 31179959917361785115543201)
      ·
        refine ⟨23384969938021338836657401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31179959917361785115543201 23384969938021338836657401)
        ·
          refine ⟨17538727453516004127493051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23384969938021338836657401 17538727453516004127493051)
          ·
            refine ⟨26308091180274006191239577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17538727453516004127493051 26308091180274006191239577)
            ·
              refine ⟨19731068385205504643429683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26308091180274006191239577 19731068385205504643429683)
              ·
                refine ⟨29596602577808256965144525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19731068385205504643429683 29596602577808256965144525)
                ·
                  refine ⟨11098725966678096361929197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29596602577808256965144525 11098725966678096361929197)
                  ·
                    refine ⟨4162022237504286135723449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11098725966678096361929197 4162022237504286135723449)
                    ·
                      refine ⟨3121516678128214601792587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162022237504286135723449 3121516678128214601792587)
                      ·
                        rfl

theorem cell23_6079132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6079132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079132 prefixEnd_6079132 := by exact prefixLift 6079132
  have htrace : WordTrace (prefixWord ++ tailWord_6079132) baseStart_6079132 baseEnd_6079132 := by
    simpa [prefixWord, tailWord_6079132, baseEnd_6079132] using wordTrace_append hprefix tailTrace_6079132
  have hstable : (prefixWord ++ tailWord_6079132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079132).length < 2 ^ (prefixWord ++ tailWord_6079132).sum := by decide
  have hdescent : baseEnd_6079132 < baseStart_6079132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079143 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6079143 : Nat := 118140960795 + 6079143 * 2 ^ 59
def prefixEnd_6079143 : Nat := 4983230072969 + 3 ^ 40 * 6079143 * 2
def baseEnd_6079143 : Nat := 3121522326415414058755037

theorem tailTrace_6079143 : CollatzResearch.WordTrace tailWord_6079143 prefixEnd_6079143 3121522326415414058755037 := by
  unfold tailWord_6079143
  simp only [CollatzResearch.WordTrace]
  refine ⟨221724560615310620811402083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147816373743540413874268055 221724560615310620811402083)
  ·
    refine ⟨332586840922965931217103125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221724560615310620811402083 332586840922965931217103125)
    ·
      refine ⟨15590008168264028025801709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332586840922965931217103125 15590008168264028025801709)
      ·
        refine ⟨5846253063099010509675641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15590008168264028025801709 5846253063099010509675641)
        ·
          refine ⟨4384689797324257882256731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846253063099010509675641 4384689797324257882256731)
          ·
            refine ⟨6577034695986386823385097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384689797324257882256731 6577034695986386823385097)
            ·
              refine ⟨4932776021989790117538823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577034695986386823385097 4932776021989790117538823)
              ·
                refine ⟨7399164032984685176308235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932776021989790117538823 7399164032984685176308235)
                ·
                  refine ⟨11098746049477027764462353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399164032984685176308235 11098746049477027764462353)
                  ·
                    refine ⟨8324059537107770823346765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11098746049477027764462353 8324059537107770823346765)
                    ·
                      refine ⟨3121522326415414058755037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324059537107770823346765 3121522326415414058755037)
                      ·
                        rfl

theorem cell23_6079143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6079143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079143 prefixEnd_6079143 := by exact prefixLift 6079143
  have htrace : WordTrace (prefixWord ++ tailWord_6079143) baseStart_6079143 baseEnd_6079143 := by
    simpa [prefixWord, tailWord_6079143, baseEnd_6079143] using wordTrace_append hprefix tailTrace_6079143
  have hstable : (prefixWord ++ tailWord_6079143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079143).length < 2 ^ (prefixWord ++ tailWord_6079143).sum := by decide
  have hdescent : baseEnd_6079143 < baseStart_6079143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079149 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6079149 : Nat := 118140960795 + 6079149 * 2 ^ 59
def prefixEnd_6079149 : Nat := 4983230072969 + 3 ^ 40 * 6079149 * 2
def baseEnd_6079149 : Nat := 3121525407299341035280009

theorem tailTrace_6079149 : CollatzResearch.WordTrace tailWord_6079149 prefixEnd_6079149 3121525407299341035280009 := by
  unfold tailWord_6079149
  simp only [CollatzResearch.WordTrace]
  refine ⟨221724779453288883836120501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147816519635525922557413667 221724779453288883836120501)
  ·
    refine ⟨20786698073745832859636297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221724779453288883836120501 20786698073745832859636297)
    ·
      refine ⟨15590023555309374644727223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20786698073745832859636297 15590023555309374644727223)
      ·
        refine ⟨23385035332964061967090835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15590023555309374644727223 23385035332964061967090835)
        ·
          refine ⟨35077552999446092950636253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23385035332964061967090835 35077552999446092950636253)
          ·
            refine ⟨13154082374792284856488595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35077552999446092950636253 13154082374792284856488595)
            ·
              refine ⟨19731123562188427284732893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154082374792284856488595 19731123562188427284732893)
              ·
                refine ⟨7399171335820660231774835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19731123562188427284732893 7399171335820660231774835)
                ·
                  refine ⟨11098757003730990347662253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399171335820660231774835 11098757003730990347662253)
                  ·
                    refine ⟨4162033876399121380373345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11098757003730990347662253 4162033876399121380373345)
                    ·
                      refine ⟨3121525407299341035280009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162033876399121380373345 3121525407299341035280009)
                      ·
                        rfl

theorem cell23_6079149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6079149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079149 prefixEnd_6079149 := by exact prefixLift 6079149
  have htrace : WordTrace (prefixWord ++ tailWord_6079149) baseStart_6079149 baseEnd_6079149 := by
    simpa [prefixWord, tailWord_6079149, baseEnd_6079149] using wordTrace_append hprefix tailTrace_6079149
  have hstable : (prefixWord ++ tailWord_6079149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079149).length < 2 ^ (prefixWord ++ tailWord_6079149).sum := by decide
  have hdescent : baseEnd_6079149 < baseStart_6079149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079162 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_6079162 : Nat := 118140960795 + 6079162 * 2 ^ 59
def prefixEnd_6079162 : Nat := 4983230072969 + 3 ^ 40 * 6079162 * 2
def baseEnd_6079162 : Nat := 3121532082547849484417449

theorem tailTrace_6079162 : CollatzResearch.WordTrace tailWord_6079162 prefixEnd_6079162 3121532082547849484417449 := by
  unfold tailWord_6079162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55431313400560446764085935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147816835734827858037562493 55431313400560446764085935)
  ·
    refine ⟨83146970100840670146128903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55431313400560446764085935 83146970100840670146128903)
    ·
      refine ⟨124720455151261005219193355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83146970100840670146128903 124720455151261005219193355)
      ·
        refine ⟨187080682726891507828790033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124720455151261005219193355 187080682726891507828790033)
        ·
          refine ⟨140310512045168630871592525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187080682726891507828790033 140310512045168630871592525)
          ·
            refine ⟨52616442016938236576847197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140310512045168630871592525 52616442016938236576847197)
            ·
              refine ⟨19731165756351838716317699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52616442016938236576847197 19731165756351838716317699)
              ·
                refine ⟨29596748634527758074476549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19731165756351838716317699 29596748634527758074476549)
                ·
                  refine ⟨5549390368973954638964353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29596748634527758074476549 5549390368973954638964353)
                  ·
                    refine ⟨4162042776730465979223265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549390368973954638964353 4162042776730465979223265)
                    ·
                      refine ⟨3121532082547849484417449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162042776730465979223265 3121532082547849484417449)
                      ·
                        rfl

theorem cell23_6079162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_6079162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079162 prefixEnd_6079162 := by exact prefixLift 6079162
  have htrace : WordTrace (prefixWord ++ tailWord_6079162) baseStart_6079162 baseEnd_6079162 := by
    simpa [prefixWord, tailWord_6079162, baseEnd_6079162] using wordTrace_append hprefix tailTrace_6079162
  have hstable : (prefixWord ++ tailWord_6079162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079162).length < 2 ^ (prefixWord ++ tailWord_6079162).sum := by decide
  have hdescent : baseEnd_6079162 < baseStart_6079162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079168 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 7]
def baseStart_6079168 : Nat := 118140960795 + 6079168 * 2 ^ 59
def prefixEnd_6079168 : Nat := 4983230072969 + 3 ^ 40 * 6079168 * 2
def baseEnd_6079168 : Nat := 346837240381308495660269

theorem tailTrace_6079168 : CollatzResearch.WordTrace tailWord_6079168 prefixEnd_6079168 346837240381308495660269 := by
  unfold tailWord_6079168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110862736220110025040531079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147816981626813366720708105 110862736220110025040531079)
  ·
    refine ⟨166294104330165037560796619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110862736220110025040531079 166294104330165037560796619)
    ·
      refine ⟨249441156495247556341194929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166294104330165037560796619 249441156495247556341194929)
      ·
        refine ⟨187080867371435667255896197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249441156495247556341194929 187080867371435667255896197)
        ·
          refine ⟨35077662632144187610480537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187080867371435667255896197 35077662632144187610480537)
          ·
            refine ⟨26308246974108140707860403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35077662632144187610480537 26308246974108140707860403)
            ·
              refine ⟨39462370461162211061790605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26308246974108140707860403 39462370461162211061790605)
              ·
                refine ⟨14798388922935829148171477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39462370461162211061790605 14798388922935829148171477)
                ·
                  refine ⟨346837240381308495660269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14798388922935829148171477 346837240381308495660269)
                  ·
                    rfl

theorem cell23_6079168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_6079168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079168 prefixEnd_6079168 := by exact prefixLift 6079168
  have htrace : WordTrace (prefixWord ++ tailWord_6079168) baseStart_6079168 baseEnd_6079168 := by
    simpa [prefixWord, tailWord_6079168, baseEnd_6079168] using wordTrace_append hprefix tailTrace_6079168
  have hstable : (prefixWord ++ tailWord_6079168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079168).length < 2 ^ (prefixWord ++ tailWord_6079168).sum := by decide
  have hdescent : baseEnd_6079168 < baseStart_6079168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079215 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 2, 5]
def baseStart_6079215 : Nat := 118140960795 + 6079215 * 2 ^ 59
def prefixEnd_6079215 : Nat := 4983230072969 + 3 ^ 40 * 6079215 * 2
def baseEnd_6079215 : Nat := 1040519765674179259018235

theorem tailTrace_6079215 : CollatzResearch.WordTrace tailWord_6079215 prefixEnd_6079215 1040519765674179259018235 := by
  unfold tailWord_6079215
  simp only [CollatzResearch.WordTrace]
  refine ⟨221727186671049777108023099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147818124447366518072015399 221727186671049777108023099)
  ·
    refine ⟨332590780006574665662034649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221727186671049777108023099 332590780006574665662034649)
    ·
      refine ⟨249443085004930999246525987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332590780006574665662034649 249443085004930999246525987)
      ·
        refine ⟨374164627507396498869788981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249443085004930999246525987 374164627507396498869788981)
        ·
          refine ⟨35077933828818421769042717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 374164627507396498869788981 35077933828818421769042717)
          ·
            refine ⟨13154225185806908163391019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35077933828818421769042717 13154225185806908163391019)
            ·
              refine ⟨19731337778710362245086529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154225185806908163391019 19731337778710362245086529)
              ·
                refine ⟨14798503334032771683814897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19731337778710362245086529 14798503334032771683814897)
                ·
                  refine ⟨11098877500524578762861173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14798503334032771683814897 11098877500524578762861173)
                  ·
                    refine ⟨1040519765674179259018235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11098877500524578762861173 1040519765674179259018235)
                    ·
                      rfl

theorem cell23_6079215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_6079215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079215 prefixEnd_6079215 := by exact prefixLift 6079215
  have htrace : WordTrace (prefixWord ++ tailWord_6079215) baseStart_6079215 baseEnd_6079215 := by
    simpa [prefixWord, tailWord_6079215, baseEnd_6079215] using wordTrace_append hprefix tailTrace_6079215
  have hstable : (prefixWord ++ tailWord_6079215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079215).length < 2 ^ (prefixWord ++ tailWord_6079215).sum := by decide
  have hdescent : baseEnd_6079215 < baseStart_6079215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079222 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6079222 : Nat := 118140960795 + 6079222 * 2 ^ 59
def prefixEnd_6079222 : Nat := 4983230072969 + 3 ^ 40 * 6079222 * 2
def baseEnd_6079222 : Nat := 3121562891387119249667173

theorem tailTrace_6079222 : CollatzResearch.WordTrace tailWord_6079222 prefixEnd_6079222 3121562891387119249667173 := by
  unfold tailWord_6079222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857965123876526081470495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147818294654682944869018613 13857965123876526081470495)
  ·
    refine ⟨20786947685814789122205743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13857965123876526081470495 20786947685814789122205743)
    ·
      refine ⟨31180421528722183683308615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786947685814789122205743 31180421528722183683308615)
      ·
        refine ⟨46770632293083275524962923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31180421528722183683308615 46770632293083275524962923)
        ·
          refine ⟨70155948439624913287444385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46770632293083275524962923 70155948439624913287444385)
          ·
            refine ⟨52616961329718684965583289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70155948439624913287444385 52616961329718684965583289)
            ·
              refine ⟨39462720997289013724187467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52616961329718684965583289 39462720997289013724187467)
              ·
                refine ⟨59194081495933520586281201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39462720997289013724187467 59194081495933520586281201)
                ·
                  refine ⟨44395561121950140439710901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59194081495933520586281201 44395561121950140439710901)
                  ·
                    refine ⟨4162083855182825666222897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44395561121950140439710901 4162083855182825666222897)
                    ·
                      refine ⟨3121562891387119249667173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162083855182825666222897 3121562891387119249667173)
                      ·
                        rfl

theorem cell23_6079222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6079222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079222 prefixEnd_6079222 := by exact prefixLift 6079222
  have htrace : WordTrace (prefixWord ++ tailWord_6079222) baseStart_6079222 baseEnd_6079222 := by
    simpa [prefixWord, tailWord_6079222, baseEnd_6079222] using wordTrace_append hprefix tailTrace_6079222
  have hstable : (prefixWord ++ tailWord_6079222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079222).length < 2 ^ (prefixWord ++ tailWord_6079222).sum := by decide
  have hdescent : baseEnd_6079222 < baseStart_6079222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079235 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 6, 2]
def baseStart_6079235 : Nat := 118140960795 + 6079235 * 2 ^ 59
def prefixEnd_6079235 : Nat := 4983230072969 + 3 ^ 40 * 6079235 * 2
def baseEnd_6079235 : Nat := 3121569566635627698804613

theorem tailTrace_6079235 : CollatzResearch.WordTrace tailWord_6079235 prefixEnd_6079235 3121569566635627698804613 := by
  unfold tailWord_6079235
  simp only [CollatzResearch.WordTrace]
  refine ⟨221727916130977320523751159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147818610753984880349167439 221727916130977320523751159)
  ·
    refine ⟨332591874196465980785626739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221727916130977320523751159 332591874196465980785626739)
    ·
      refine ⟨498887811294698971178440109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332591874196465980785626739 498887811294698971178440109)
      ·
        refine ⟨187082929235512114191915041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498887811294698971178440109 187082929235512114191915041)
        ·
          refine ⟨140312196926634085643936281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187082929235512114191915041 140312196926634085643936281)
          ·
            refine ⟨105234147694975564232952211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140312196926634085643936281 105234147694975564232952211)
            ·
              refine ⟨157851221542463346349428317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105234147694975564232952211 157851221542463346349428317)
              ·
                refine ⟨59194208078423754881035619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157851221542463346349428317 59194208078423754881035619)
                ·
                  refine ⟨88791312117635632321553429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59194208078423754881035619 88791312117635632321553429)
                  ·
                    refine ⟨4162092755514170265072817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88791312117635632321553429 4162092755514170265072817)
                    ·
                      refine ⟨3121569566635627698804613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162092755514170265072817 3121569566635627698804613)
                      ·
                        rfl

theorem cell23_6079235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_6079235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079235 prefixEnd_6079235 := by exact prefixLift 6079235
  have htrace : WordTrace (prefixWord ++ tailWord_6079235) baseStart_6079235 baseEnd_6079235 := by
    simpa [prefixWord, tailWord_6079235, baseEnd_6079235] using wordTrace_append hprefix tailTrace_6079235
  have hstable : (prefixWord ++ tailWord_6079235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079235).length < 2 ^ (prefixWord ++ tailWord_6079235).sum := by decide
  have hdescent : baseEnd_6079235 < baseStart_6079235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079272 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6079272 : Nat := 118140960795 + 6079272 * 2 ^ 59
def prefixEnd_6079272 : Nat := 4983230072969 + 3 ^ 40 * 6079272 * 2
def baseEnd_6079272 : Nat := 3121588565419844054041943

theorem tailTrace_6079272 : CollatzResearch.WordTrace tailWord_6079272 prefixEnd_6079272 3121588565419844054041943 := by
  unfold tailWord_6079272
  simp only [CollatzResearch.WordTrace]
  refine ⟨110864632815921637921424035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147819510421228850561898713 110864632815921637921424035)
  ·
    refine ⟨166296949223882456882136053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110864632815921637921424035 166296949223882456882136053)
    ·
      refine ⟨15590338989738980332700255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166296949223882456882136053 15590338989738980332700255)
      ·
        refine ⟨23385508484608470499050383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15590338989738980332700255 23385508484608470499050383)
        ·
          refine ⟨35078262726912705748575575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23385508484608470499050383 35078262726912705748575575)
          ·
            refine ⟨52617394090369058622863363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35078262726912705748575575 52617394090369058622863363)
            ·
              refine ⟨78926091135553587934295045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52617394090369058622863363 78926091135553587934295045)
              ·
                refine ⟨14798642087916297737680321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78926091135553587934295045 14798642087916297737680321)
                ·
                  refine ⟨11098981565937223303260241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14798642087916297737680321 11098981565937223303260241)
                  ·
                    refine ⟨8324236174452917477445181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11098981565937223303260241 8324236174452917477445181)
                    ·
                      refine ⟨3121588565419844054041943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324236174452917477445181 3121588565419844054041943)
                      ·
                        rfl

theorem cell23_6079272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6079272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079272 prefixEnd_6079272 := by exact prefixLift 6079272
  have htrace : WordTrace (prefixWord ++ tailWord_6079272) baseStart_6079272 baseEnd_6079272 := by
    simpa [prefixWord, tailWord_6079272, baseEnd_6079272] using wordTrace_append hprefix tailTrace_6079272
  have hstable : (prefixWord ++ tailWord_6079272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079272).length < 2 ^ (prefixWord ++ tailWord_6079272).sum := by decide
  have hdescent : baseEnd_6079272 < baseStart_6079272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079286 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6079286 : Nat := 118140960795 + 6079286 * 2 ^ 59
def prefixEnd_6079286 : Nat := 4983230072969 + 3 ^ 40 * 6079286 * 2
def baseEnd_6079286 : Nat := 3121595754149006999266879

theorem tailTrace_6079286 : CollatzResearch.WordTrace tailWord_6079286 prefixEnd_6079286 3121595754149006999266879 := by
  unfold tailWord_6079286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858111015862034764616107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147819850835861704155905141 13858111015862034764616107)
  ·
    refine ⟨20787166523793052146924161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13858111015862034764616107 20787166523793052146924161)
    ·
      refine ⟨15590374892844789110193121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20787166523793052146924161 15590374892844789110193121)
      ·
        refine ⟨11692781169633591832644841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15590374892844789110193121 11692781169633591832644841)
        ·
          refine ⟨8769585877225193874483631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11692781169633591832644841 8769585877225193874483631)
          ·
            refine ⟨13154378815837790811725447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769585877225193874483631 13154378815837790811725447)
            ·
              refine ⟨19731568223756686217588171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154378815837790811725447 19731568223756686217588171)
              ·
                refine ⟨29597352335635029326382257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19731568223756686217588171 29597352335635029326382257)
                ·
                  refine ⟨22198014251726271994786693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29597352335635029326382257 22198014251726271994786693)
                  ·
                    refine ⟨4162127672198675999022505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22198014251726271994786693 4162127672198675999022505)
                    ·
                      refine ⟨3121595754149006999266879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162127672198675999022505 3121595754149006999266879)
                      ·
                        rfl

theorem cell23_6079286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6079286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079286 prefixEnd_6079286 := by exact prefixLift 6079286
  have htrace : WordTrace (prefixWord ++ tailWord_6079286) baseStart_6079286 baseEnd_6079286 := by
    simpa [prefixWord, tailWord_6079286, baseEnd_6079286] using wordTrace_append hprefix tailTrace_6079286
  have hstable : (prefixWord ++ tailWord_6079286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079286).length < 2 ^ (prefixWord ++ tailWord_6079286).sum := by decide
  have hdescent : baseEnd_6079286 < baseStart_6079286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079305 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_6079305 : Nat := 118140960795 + 6079305 * 2 ^ 59
def prefixEnd_6079305 : Nat := 4983230072969 + 3 ^ 40 * 6079305 * 2
def baseEnd_6079305 : Nat := 1040535170093814141643097

theorem tailTrace_6079305 : CollatzResearch.WordTrace tailWord_6079305 prefixEnd_6079305 1040535170093814141643097 := by
  unfold tailWord_6079305
  simp only [CollatzResearch.WordTrace]
  refine ⟨221730469240723722478799369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147820312827149148319199579 221730469240723722478799369)
  ·
    refine ⟨166297851930542791859099527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221730469240723722478799369 166297851930542791859099527)
    ·
      refine ⟨249446777895814187788649291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166297851930542791859099527 249446777895814187788649291)
      ·
        refine ⟨374170166843721281682973937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249446777895814187788649291 374170166843721281682973937)
        ·
          refine ⟨280627625132790961262230453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374170166843721281682973937 280627625132790961262230453)
          ·
            refine ⟨26308839856199152618334105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280627625132790961262230453 26308839856199152618334105)
            ·
              refine ⟨19731629892149364463750579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26308839856199152618334105 19731629892149364463750579)
              ·
                refine ⟨29597444838224046695625869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19731629892149364463750579 29597444838224046695625869)
                ·
                  refine ⟨11099041814334017510859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29597444838224046695625869 11099041814334017510859701)
                  ·
                    refine ⟨1040535170093814141643097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11099041814334017510859701 1040535170093814141643097)
                    ·
                      rfl

theorem cell23_6079305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_6079305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079305 prefixEnd_6079305 := by exact prefixLift 6079305
  have htrace : WordTrace (prefixWord ++ tailWord_6079305) baseStart_6079305 baseEnd_6079305 := by
    simpa [prefixWord, tailWord_6079305, baseEnd_6079305] using wordTrace_append hprefix tailTrace_6079305
  have hstable : (prefixWord ++ tailWord_6079305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079305).length < 2 ^ (prefixWord ++ tailWord_6079305).sum := by decide
  have hdescent : baseEnd_6079305 < baseStart_6079305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079322 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_6079322 : Nat := 118140960795 + 6079322 * 2 ^ 59
def prefixEnd_6079322 : Nat := 4983230072969 + 3 ^ 40 * 6079322 * 2
def baseEnd_6079322 : Nat := 1040538079817522952805571

theorem tailTrace_6079322 : CollatzResearch.WordTrace tailWord_6079322 prefixEnd_6079322 1040538079817522952805571 := by
  unfold tailWord_6079322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55432772320415533595542055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147820726187774756254778813 55432772320415533595542055)
  ·
    refine ⟨83149158480623300393313083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55432772320415533595542055 83149158480623300393313083)
    ·
      refine ⟨124723737720934950589969625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83149158480623300393313083 124723737720934950589969625)
      ·
        refine ⟨93542803290701212942477219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124723737720934950589969625 93542803290701212942477219)
        ·
          refine ⟨140314204936051819413715829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93542803290701212942477219 140314204936051819413715829)
          ·
            refine ⟨13154456712754858070035859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140314204936051819413715829 13154456712754858070035859)
            ·
              refine ⟨19731685069132287105053789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154456712754858070035859 19731685069132287105053789)
              ·
                refine ⟨7399381900924607664395171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19731685069132287105053789 7399381900924607664395171)
                ·
                  refine ⟨11099072851386911496592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399381900924607664395171 11099072851386911496592757)
                  ·
                    refine ⟨1040538079817522952805571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11099072851386911496592757 1040538079817522952805571)
                    ·
                      rfl

theorem cell23_6079322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_6079322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079322 prefixEnd_6079322 := by exact prefixLift 6079322
  have htrace : WordTrace (prefixWord ++ tailWord_6079322) baseStart_6079322 baseEnd_6079322 := by
    simpa [prefixWord, tailWord_6079322, baseEnd_6079322] using wordTrace_append hprefix tailTrace_6079322
  have hstable : (prefixWord ++ tailWord_6079322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079322).length < 2 ^ (prefixWord ++ tailWord_6079322).sum := by decide
  have hdescent : baseEnd_6079322 < baseStart_6079322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079336 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6079336 : Nat := 118140960795 + 6079336 * 2 ^ 59
def prefixEnd_6079336 : Nat := 4983230072969 + 3 ^ 40 * 6079336 * 2
def baseEnd_6079336 : Nat := 3121621428181731803641649

theorem tailTrace_6079336 : CollatzResearch.WordTrace tailWord_6079336 prefixEnd_6079336 3121621428181731803641649 := by
  unfold tailWord_6079336
  simp only [CollatzResearch.WordTrace]
  refine ⟨110865799951805707386588931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147821066602407609848785241 110865799951805707386588931)
  ·
    refine ⟨166298699927708561079883397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110865799951805707386588931 166298699927708561079883397)
    ·
      refine ⟨31181006236445355202478137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166298699927708561079883397 31181006236445355202478137)
      ·
        refine ⟨23385754677334016401858603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31181006236445355202478137 23385754677334016401858603)
        ·
          refine ⟨35078632016001024602787905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23385754677334016401858603 35078632016001024602787905)
          ·
            refine ⟨26308974012000768452090929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35078632016001024602787905 26308974012000768452090929)
            ·
              refine ⟨19731730509000576339068197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26308974012000768452090929 19731730509000576339068197)
              ·
                refine ⟨3699699470437608063575287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19731730509000576339068197 3699699470437608063575287)
                ·
                  refine ⟨5549549205656412095362931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699699470437608063575287 5549549205656412095362931)
                  ·
                    refine ⟨8324323808484618143044397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5549549205656412095362931 8324323808484618143044397)
                    ·
                      refine ⟨3121621428181731803641649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324323808484618143044397 3121621428181731803641649)
                      ·
                        rfl

theorem cell23_6079336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6079336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079336 prefixEnd_6079336 := by exact prefixLift 6079336
  have htrace : WordTrace (prefixWord ++ tailWord_6079336) baseStart_6079336 baseEnd_6079336 := by
    simpa [prefixWord, tailWord_6079336, baseEnd_6079336] using wordTrace_append hprefix tailTrace_6079336
  have hstable : (prefixWord ++ tailWord_6079336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079336).length < 2 ^ (prefixWord ++ tailWord_6079336).sum := by decide
  have hdescent : baseEnd_6079336 < baseStart_6079336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079345 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_6079345 : Nat := 118140960795 + 6079345 * 2 ^ 59
def prefixEnd_6079345 : Nat := 4983230072969 + 3 ^ 40 * 6079345 * 2
def baseEnd_6079345 : Nat := 3121626049507622268429107

theorem tailTrace_6079345 : CollatzResearch.WordTrace tailWord_6079345 prefixEnd_6079345 3121626049507622268429107 := by
  unfold tailWord_6079345
  simp only [CollatzResearch.WordTrace]
  refine ⟨221731928160578809310255489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147821285440385872873503659 221731928160578809310255489)
  ·
    refine ⟨166298946120434106982691617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221731928160578809310255489 166298946120434106982691617)
    ·
      refine ⟨124724209590325580237018713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166298946120434106982691617 124724209590325580237018713)
      ·
        refine ⟨93543157192744185177764035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124724209590325580237018713 93543157192744185177764035)
        ·
          refine ⟨140314735789116277766646053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93543157192744185177764035 140314735789116277766646053)
          ·
            refine ⟨26309012960459302081246135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140314735789116277766646053 26309012960459302081246135)
            ·
              refine ⟨39463519440688953121869203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26309012960459302081246135 39463519440688953121869203)
              ·
                refine ⟨59195279161033429682803805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39463519440688953121869203 59195279161033429682803805)
                ·
                  refine ⟨22198229685387536131051427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59195279161033429682803805 22198229685387536131051427)
                  ·
                    refine ⟨33297344528081304196577141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22198229685387536131051427 33297344528081304196577141)
                    ·
                      refine ⟨3121626049507622268429107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33297344528081304196577141 3121626049507622268429107)
                      ·
                        rfl

theorem cell23_6079345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_6079345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079345 prefixEnd_6079345 := by exact prefixLift 6079345
  have htrace : WordTrace (prefixWord ++ tailWord_6079345) baseStart_6079345 baseEnd_6079345 := by
    simpa [prefixWord, tailWord_6079345, baseEnd_6079345] using wordTrace_append hprefix tailTrace_6079345
  have hstable : (prefixWord ++ tailWord_6079345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079345).length < 2 ^ (prefixWord ++ tailWord_6079345).sum := by decide
  have hdescent : baseEnd_6079345 < baseStart_6079345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079359 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 3, 2, 2]
def baseStart_6079359 : Nat := 118140960795 + 6079359 * 2 ^ 59
def prefixEnd_6079359 : Nat := 4983230072969 + 3 ^ 40 * 6079359 * 2
def baseEnd_6079359 : Nat := 3121633238236785213654043

theorem tailTrace_6079359 : CollatzResearch.WordTrace tailWord_6079359 prefixEnd_6079359 3121633238236785213654043 := by
  unfold tailWord_6079359
  simp only [CollatzResearch.WordTrace]
  refine ⟨221732438782528089701265131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147821625855018726467510087 221732438782528089701265131)
  ·
    refine ⟨332598658173792134551897697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221732438782528089701265131 332598658173792134551897697)
    ·
      refine ⟨249448993630344100913923273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332598658173792134551897697 249448993630344100913923273)
      ·
        refine ⟨187086745222758075685442455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249448993630344100913923273 187086745222758075685442455)
        ·
          refine ⟨280630117834137113528163683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187086745222758075685442455 280630117834137113528163683)
          ·
            refine ⟨420945176751205670292245525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280630117834137113528163683 420945176751205670292245525)
            ·
              refine ⟨19731805160212765794949009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 420945176751205670292245525 19731805160212765794949009)
              ·
                refine ⟨14798853870159574346211757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19731805160212765794949009 14798853870159574346211757)
                ·
                  refine ⟨5549570201309840379829409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14798853870159574346211757 5549570201309840379829409)
                  ·
                    refine ⟨4162177650982380284872057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549570201309840379829409 4162177650982380284872057)
                    ·
                      refine ⟨3121633238236785213654043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162177650982380284872057 3121633238236785213654043)
                      ·
                        rfl

theorem cell23_6079359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_6079359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079359 prefixEnd_6079359 := by exact prefixLift 6079359
  have htrace : WordTrace (prefixWord ++ tailWord_6079359) baseStart_6079359 baseEnd_6079359 := by
    simpa [prefixWord, tailWord_6079359, baseEnd_6079359] using wordTrace_append hprefix tailTrace_6079359
  have hstable : (prefixWord ++ tailWord_6079359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079359).length < 2 ^ (prefixWord ++ tailWord_6079359).sum := by decide
  have hdescent : baseEnd_6079359 < baseStart_6079359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079365 : List Nat := [1, 3, 1, 1, 3, 4, 1, 9]
def baseStart_6079365 : Nat := 118140960795 + 6079365 * 2 ^ 59
def prefixEnd_6079365 : Nat := 4983230072969 + 3 ^ 40 * 6079365 * 2
def baseEnd_6079365 : Nat := 115616159967433784821445

theorem tailTrace_6079365 : CollatzResearch.WordTrace tailWord_6079365 prefixEnd_6079365 115616159967433784821445 := by
  unfold tailWord_6079365
  simp only [CollatzResearch.WordTrace]
  refine ⟨221732657620506352725983549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147821771747004235150655699 221732657620506352725983549)
  ·
    refine ⟨83149746607689882272243831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221732657620506352725983549 83149746607689882272243831)
    ·
      refine ⟨124724619911534823408365747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83149746607689882272243831 124724619911534823408365747)
      ·
        refine ⟨187086929867302235112548621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124724619911534823408365747 187086929867302235112548621)
        ·
          refine ⟨70157598700238338167205733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187086929867302235112548621 70157598700238338167205733)
          ·
            refine ⟨13154549756294688406351075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70157598700238338167205733 13154549756294688406351075)
            ·
              refine ⟨19731824634442032609526613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154549756294688406351075 19731824634442032609526613)
              ·
                refine ⟨115616159967433784821445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19731824634442032609526613 115616159967433784821445)
                ·
                  rfl

theorem cell23_6079365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 9].length) (baseStart_6079365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079365 prefixEnd_6079365 := by exact prefixLift 6079365
  have htrace : WordTrace (prefixWord ++ tailWord_6079365) baseStart_6079365 baseEnd_6079365 := by
    simpa [prefixWord, tailWord_6079365, baseEnd_6079365] using wordTrace_append hprefix tailTrace_6079365
  have hstable : (prefixWord ++ tailWord_6079365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079365).length < 2 ^ (prefixWord ++ tailWord_6079365).sum := by decide
  have hdescent : baseEnd_6079365 < baseStart_6079365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079393 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6079393 : Nat := 118140960795 + 6079393 * 2 ^ 59
def prefixEnd_6079393 : Nat := 4983230072969 + 3 ^ 40 * 6079393 * 2
def baseEnd_6079393 : Nat := 3121650696579038080628887

theorem tailTrace_6079393 : CollatzResearch.WordTrace tailWord_6079393 prefixEnd_6079393 3121650696579038080628887 := by
  unfold tailWord_6079393
  simp only [CollatzResearch.WordTrace]
  refine ⟨221733678864404913508002833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147822452576269942338668555 221733678864404913508002833)
  ·
    refine ⟨166300259148303685131002125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221733678864404913508002833 166300259148303685131002125)
    ·
      refine ⟨62362597180613881924125797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166300259148303685131002125 62362597180613881924125797)
      ·
        refine ⟨11692986971365102860773587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62362597180613881924125797 11692986971365102860773587)
        ·
          refine ⟨17539480457047654291160381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11692986971365102860773587 17539480457047654291160381)
          ·
            refine ⟨6577305171392870359185143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17539480457047654291160381 6577305171392870359185143)
            ·
              refine ⟨9865957757089305538777715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577305171392870359185143 9865957757089305538777715)
              ·
                refine ⟨14798936635633958308166573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9865957757089305538777715 14798936635633958308166573)
                ·
                  refine ⟨5549601238362734365562465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14798936635633958308166573 5549601238362734365562465)
                  ·
                    refine ⟨4162200928772050774171849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549601238362734365562465 4162200928772050774171849)
                    ·
                      refine ⟨3121650696579038080628887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162200928772050774171849 3121650696579038080628887)
                      ·
                        rfl

theorem cell23_6079393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6079393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079393 prefixEnd_6079393 := by exact prefixLift 6079393
  have htrace : WordTrace (prefixWord ++ tailWord_6079393) baseStart_6079393 baseEnd_6079393 := by
    simpa [prefixWord, tailWord_6079393, baseEnd_6079393] using wordTrace_append hprefix tailTrace_6079393
  have hstable : (prefixWord ++ tailWord_6079393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079393).length < 2 ^ (prefixWord ++ tailWord_6079393).sum := by decide
  have hdescent : baseEnd_6079393 < baseStart_6079393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079466 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_6079466 : Nat := 118140960795 + 6079466 * 2 ^ 59
def prefixEnd_6079466 : Nat := 4983230072969 + 3 ^ 40 * 6079466 * 2
def baseEnd_6079466 : Nat := 3121688180666816295016051

theorem tailTrace_6079466 : CollatzResearch.WordTrace tailWord_6079466 prefixEnd_6079466 3121688180666816295016051 := by
  unfold tailWord_6079466
  simp only [CollatzResearch.WordTrace]
  refine ⟨55434085348285111743852563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147824227595426964650273501 55434085348285111743852563)
  ·
    refine ⟨83151128022427667615778845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55434085348285111743852563 83151128022427667615778845)
    ·
      refine ⟨31181673008410375355917067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83151128022427667615778845 31181673008410375355917067)
      ·
        refine ⟨46772509512615563033875601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31181673008410375355917067 46772509512615563033875601)
        ·
          refine ⟨35079382134461672275406701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46772509512615563033875601 35079382134461672275406701)
          ·
            refine ⟨13154768300423127103277513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35079382134461672275406701 13154768300423127103277513)
            ·
              refine ⟨9866076225317345327458135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13154768300423127103277513 9866076225317345327458135)
              ·
                refine ⟨14799114337976017991187203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9866076225317345327458135 14799114337976017991187203)
                ·
                  refine ⟨22198671506964026986780805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14799114337976017991187203 22198671506964026986780805)
                  ·
                    refine ⟨4162250907555755060021401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22198671506964026986780805 4162250907555755060021401)
                    ·
                      refine ⟨3121688180666816295016051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162250907555755060021401 3121688180666816295016051)
                      ·
                        rfl

theorem cell23_6079466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_6079466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079466 prefixEnd_6079466 := by exact prefixLift 6079466
  have htrace : WordTrace (prefixWord ++ tailWord_6079466) baseStart_6079466 baseEnd_6079466 := by
    simpa [prefixWord, tailWord_6079466, baseEnd_6079466] using wordTrace_append hprefix tailTrace_6079466
  have hstable : (prefixWord ++ tailWord_6079466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079466).length < 2 ^ (prefixWord ++ tailWord_6079466).sum := by decide
  have hdescent : baseEnd_6079466 < baseStart_6079466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079489 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 5]
def baseStart_6079489 : Nat := 118140960795 + 6079489 * 2 ^ 59
def prefixEnd_6079489 : Nat := 4983230072969 + 3 ^ 40 * 6079489 * 2
def baseEnd_6079489 : Nat := 346855554524652189447605

theorem tailTrace_6079489 : CollatzResearch.WordTrace tailWord_6079489 prefixEnd_6079489 346855554524652189447605 := by
  unfold tailWord_6079489
  simp only [CollatzResearch.WordTrace]
  refine ⟨221737180272057121903497521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147824786848038081268998347 221737180272057121903497521)
  ·
    refine ⟨166302885204042841427623141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221737180272057121903497521 166302885204042841427623141)
    ·
      refine ⟨31181790975758032767679339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166302885204042841427623141 31181790975758032767679339)
      ·
        refine ⟨46772686463637049151519009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31181790975758032767679339 46772686463637049151519009)
        ·
          refine ⟨35079514847727786863639257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46772686463637049151519009 35079514847727786863639257)
          ·
            refine ⟨26309636135795840147729443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35079514847727786863639257 26309636135795840147729443)
            ·
              refine ⟨39464454203693760221594165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26309636135795840147729443 39464454203693760221594165)
              ·
                refine ⟨3699792581596290020774453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39464454203693760221594165 3699792581596290020774453)
                ·
                  refine ⟨346855554524652189447605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699792581596290020774453 346855554524652189447605)
                  ·
                    rfl

theorem cell23_6079489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 5].length) (baseStart_6079489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079489 prefixEnd_6079489 := by exact prefixLift 6079489
  have htrace : WordTrace (prefixWord ++ tailWord_6079489) baseStart_6079489 baseEnd_6079489 := by
    simpa [prefixWord, tailWord_6079489, baseEnd_6079489] using wordTrace_append hprefix tailTrace_6079489
  have hstable : (prefixWord ++ tailWord_6079489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079489).length < 2 ^ (prefixWord ++ tailWord_6079489).sum := by decide
  have hdescent : baseEnd_6079489 < baseStart_6079489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079559 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_6079559 : Nat := 118140960795 + 6079559 * 2 ^ 59
def prefixEnd_6079559 : Nat := 4983230072969 + 3 ^ 40 * 6079559 * 2
def baseEnd_6079559 : Nat := 3121735934367684431153123

theorem tailTrace_6079559 : CollatzResearch.WordTrace tailWord_6079559 prefixEnd_6079559 3121735934367684431153123 := by
  unfold tailWord_6079559
  simp only [CollatzResearch.WordTrace]
  refine ⟨221739733381803523858545731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147826488921202349239030487 221739733381803523858545731)
  ·
    refine ⟨332609600072705285787818597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221739733381803523858545731 332609600072705285787818597)
    ·
      refine ⟨62364300013632241085215987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332609600072705285787818597 62364300013632241085215987)
      ·
        refine ⟨93546450020448361627823981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62364300013632241085215987 93546450020448361627823981)
        ·
          refine ⟨35079918757668135610433993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93546450020448361627823981 35079918757668135610433993)
          ·
            refine ⟨26309939068251101707825495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35079918757668135610433993 26309939068251101707825495)
            ·
              refine ⟨39464908602376652561738243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26309939068251101707825495 39464908602376652561738243)
              ·
                refine ⟨59197362903564978842607365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39464908602376652561738243 59197362903564978842607365)
                ·
                  refine ⟨11099505544418433532988881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59197362903564978842607365 11099505544418433532988881)
                  ·
                    refine ⟨8324629158313825149741661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11099505544418433532988881 8324629158313825149741661)
                    ·
                      refine ⟨3121735934367684431153123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324629158313825149741661 3121735934367684431153123)
                      ·
                        rfl

theorem cell23_6079559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_6079559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079559 prefixEnd_6079559 := by exact prefixLift 6079559
  have htrace : WordTrace (prefixWord ++ tailWord_6079559) baseStart_6079559 baseEnd_6079559 := by
    simpa [prefixWord, tailWord_6079559, baseEnd_6079559] using wordTrace_append hprefix tailTrace_6079559
  have hstable : (prefixWord ++ tailWord_6079559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079559).length < 2 ^ (prefixWord ++ tailWord_6079559).sum := by decide
  have hdescent : baseEnd_6079559 < baseStart_6079559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079562 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_6079562 : Nat := 118140960795 + 6079562 * 2 ^ 59
def prefixEnd_6079562 : Nat := 4983230072969 + 3 ^ 40 * 6079562 * 2
def baseEnd_6079562 : Nat := 346859719423294213268401

theorem tailTrace_6079562 : CollatzResearch.WordTrace tailWord_6079562 prefixEnd_6079562 346859719423294213268401 := by
  unfold tailWord_6079562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55434960700198163842726235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147826561867195103580603293 55434960700198163842726235)
  ·
    refine ⟨83152441050297245764089353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55434960700198163842726235 83152441050297245764089353)
    ·
      refine ⟨62364330787722934323067015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83152441050297245764089353 62364330787722934323067015)
      ·
        refine ⟨93546496181584401484600523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62364330787722934323067015 93546496181584401484600523)
        ·
          refine ⟨140319744272376602226900785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93546496181584401484600523 140319744272376602226900785)
          ·
            refine ⟨105239808204282451670175589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140319744272376602226900785 105239808204282451670175589)
            ·
              refine ⟨19732464038302959688157923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105239808204282451670175589 19732464038302959688157923)
              ·
                refine ⟨29598696057454439532236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19732464038302959688157923 29598696057454439532236885)
                ·
                  refine ⟨346859719423294213268401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29598696057454439532236885 346859719423294213268401)
                  ·
                    rfl

theorem cell23_6079562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_6079562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079562 prefixEnd_6079562 := by exact prefixLift 6079562
  have htrace : WordTrace (prefixWord ++ tailWord_6079562) baseStart_6079562 baseEnd_6079562 := by
    simpa [prefixWord, tailWord_6079562, baseEnd_6079562] using wordTrace_append hprefix tailTrace_6079562
  have hstable : (prefixWord ++ tailWord_6079562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079562).length < 2 ^ (prefixWord ++ tailWord_6079562).sum := by decide
  have hdescent : baseEnd_6079562 < baseStart_6079562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079616 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2]
def baseStart_6079616 : Nat := 118140960795 + 6079616 * 2 ^ 59
def prefixEnd_6079616 : Nat := 4983230072969 + 3 ^ 40 * 6079616 * 2
def baseEnd_6079616 : Nat := 3121765202764990708140361

theorem tailTrace_6079616 : CollatzResearch.WordTrace tailWord_6079616 prefixEnd_6079616 3121765202764990708140361 := by
  unfold tailWord_6079616
  simp only [CollatzResearch.WordTrace]
  refine ⟨110870906171298511296685351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147827874895064681728913801 110870906171298511296685351)
  ·
    refine ⟨166306359256947766945028027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110870906171298511296685351 166306359256947766945028027)
    ·
      refine ⟨249459538885421650417542041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166306359256947766945028027 249459538885421650417542041)
      ·
        refine ⟨187094654164066237813156531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249459538885421650417542041 187094654164066237813156531)
        ·
          refine ⟨280641981246099356719734797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187094654164066237813156531 280641981246099356719734797)
          ·
            refine ⟨105240742967287258769900549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280641981246099356719734797 105240742967287258769900549)
            ·
              refine ⟨19732639306366361019356353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105240742967287258769900549 19732639306366361019356353)
              ·
                refine ⟨14799479479774770764517265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19732639306366361019356353 14799479479774770764517265)
                ·
                  refine ⟨11099609609831078073387949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14799479479774770764517265 11099609609831078073387949)
                  ·
                    refine ⟨4162353603686654277520481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11099609609831078073387949 4162353603686654277520481)
                    ·
                      refine ⟨3121765202764990708140361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162353603686654277520481 3121765202764990708140361)
                      ·
                        rfl

theorem cell23_6079616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_6079616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079616 prefixEnd_6079616 := by exact prefixLift 6079616
  have htrace : WordTrace (prefixWord ++ tailWord_6079616) baseStart_6079616 baseEnd_6079616 := by
    simpa [prefixWord, tailWord_6079616, baseEnd_6079616] using wordTrace_append hprefix tailTrace_6079616
  have hstable : (prefixWord ++ tailWord_6079616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079616).length < 2 ^ (prefixWord ++ tailWord_6079616).sum := by decide
  have hdescent : baseEnd_6079616 < baseStart_6079616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079639 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 6]
def baseStart_6079639 : Nat := 118140960795 + 6079639 * 2 ^ 59
def prefixEnd_6079639 : Nat := 4983230072969 + 3 ^ 40 * 6079639 * 2
def baseEnd_6079639 : Nat := 1040592337606681372717585

theorem tailTrace_6079639 : CollatzResearch.WordTrace tailWord_6079639 prefixEnd_6079639 1040592337606681372717585 := by
  unfold tailWord_6079639
  simp only [CollatzResearch.WordTrace]
  refine ⟨221742651221513697521457971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147828434147675798347638647 221742651221513697521457971)
  ·
    refine ⟨332613976832270546282186957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221742651221513697521457971 332613976832270546282186957)
    ·
      refine ⟨124730241312101454855820109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332613976832270546282186957 124730241312101454855820109)
      ·
        refine ⟨46773840492038045570932541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124730241312101454855820109 46773840492038045570932541)
        ·
          refine ⟨17540190184514267089099703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46773840492038045570932541 17540190184514267089099703)
          ·
            refine ⟨26310285276771400633649555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17540190184514267089099703 26310285276771400633649555)
            ·
              refine ⟨39465427915157100950474333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26310285276771400633649555 39465427915157100950474333)
              ·
                refine ⟨14799535468183912856427875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39465427915157100950474333 14799535468183912856427875)
                ·
                  refine ⟨22199303202275869284641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14799535468183912856427875 22199303202275869284641813)
                  ·
                    refine ⟨1040592337606681372717585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22199303202275869284641813 1040592337606681372717585)
                    ·
                      rfl

theorem cell23_6079639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_6079639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079639 prefixEnd_6079639 := by exact prefixLift 6079639
  have htrace : WordTrace (prefixWord ++ tailWord_6079639) baseStart_6079639 baseEnd_6079639 := by
    simpa [prefixWord, tailWord_6079639, baseEnd_6079639] using wordTrace_append hprefix tailTrace_6079639
  have hstable : (prefixWord ++ tailWord_6079639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079639).length < 2 ^ (prefixWord ++ tailWord_6079639).sum := by decide
  have hdescent : baseEnd_6079639 < baseStart_6079639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079673 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_6079673 : Nat := 118140960795 + 6079673 * 2 ^ 59
def prefixEnd_6079673 : Nat := 4983230072969 + 3 ^ 40 * 6079673 * 2
def baseEnd_6079673 : Nat := 1040598157054098995042533

theorem tailTrace_6079673 : CollatzResearch.WordTrace tailWord_6079673 prefixEnd_6079673 1040598157054098995042533 := by
  unfold tailWord_6079673
  simp only [CollatzResearch.WordTrace]
  refine ⟨221743891303390521328195673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147829260868927014218797115 221743891303390521328195673)
  ·
    refine ⟨166307918477542890996146755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221743891303390521328195673 166307918477542890996146755)
    ·
      refine ⟨249461877716314336494220133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166307918477542890996146755 249461877716314336494220133)
      ·
        refine ⟨46774102071808938092666275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249461877716314336494220133 46774102071808938092666275)
        ·
          refine ⟨70161153107713407138999413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46774102071808938092666275 70161153107713407138999413)
          ·
            refine ⟨6577608103848131919281195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70161153107713407138999413 6577608103848131919281195)
            ·
              refine ⟨9866412155772197878921793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577608103848131919281195 9866412155772197878921793)
              ·
                refine ⟨7399809116829148409191345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9866412155772197878921793 7399809116829148409191345)
                ·
                  refine ⟨5549856837621861306893509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7399809116829148409191345 5549856837621861306893509)
                  ·
                    refine ⟨1040598157054098995042533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5549856837621861306893509 1040598157054098995042533)
                    ·
                      rfl

theorem cell23_6079673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_6079673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079673 prefixEnd_6079673 := by exact prefixLift 6079673
  have htrace : WordTrace (prefixWord ++ tailWord_6079673) baseStart_6079673 baseEnd_6079673 := by
    simpa [prefixWord, tailWord_6079673, baseEnd_6079673] using wordTrace_append hprefix tailTrace_6079673
  have hstable : (prefixWord ++ tailWord_6079673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079673).length < 2 ^ (prefixWord ++ tailWord_6079673).sum := by decide
  have hdescent : baseEnd_6079673 < baseStart_6079673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079679 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_6079679 : Nat := 118140960795 + 6079679 * 2 ^ 59
def prefixEnd_6079679 : Nat := 4983230072969 + 3 ^ 40 * 6079679 * 2
def baseEnd_6079679 : Nat := 3121797552046223961652571

theorem tailTrace_6079679 : CollatzResearch.WordTrace tailWord_6079679 prefixEnd_6079679 3121797552046223961652571 := by
  unfold tailWord_6079679
  simp only [CollatzResearch.WordTrace]
  refine ⟨221744110141368784352914091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147829406760912522901942727 221744110141368784352914091)
  ·
    refine ⟨332616165212053176529371137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221744110141368784352914091 332616165212053176529371137)
    ·
      refine ⟨249462123909039882397028353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332616165212053176529371137 249462123909039882397028353)
      ·
        refine ⟨187096592931779911797771265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249462123909039882397028353 187096592931779911797771265)
        ·
          refine ⟨140322444698834933848328449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187096592931779911797771265 140322444698834933848328449)
          ·
            refine ⟨105241833524126200386246337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140322444698834933848328449 105241833524126200386246337)
            ·
              refine ⟨78931375143094650289684753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105241833524126200386246337 78931375143094650289684753)
              ·
                refine ⟨59198531357320987717263565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78931375143094650289684753 59198531357320987717263565)
                ·
                  refine ⟨22199449258995370393973837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59198531357320987717263565 22199449258995370393973837)
                  ·
                    refine ⟨8324793472123263897740189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22199449258995370393973837 8324793472123263897740189)
                    ·
                      refine ⟨3121797552046223961652571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8324793472123263897740189 3121797552046223961652571)
                      ·
                        rfl

theorem cell23_6079679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_6079679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079679 prefixEnd_6079679 := by exact prefixLift 6079679
  have htrace : WordTrace (prefixWord ++ tailWord_6079679) baseStart_6079679 baseEnd_6079679 := by
    simpa [prefixWord, tailWord_6079679, baseEnd_6079679] using wordTrace_append hprefix tailTrace_6079679
  have hstable : (prefixWord ++ tailWord_6079679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079679).length < 2 ^ (prefixWord ++ tailWord_6079679).sum := by decide
  have hdescent : baseEnd_6079679 < baseStart_6079679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079680 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2]
def baseStart_6079680 : Nat := 118140960795 + 6079680 * 2 ^ 59
def prefixEnd_6079680 : Nat := 4983230072969 + 3 ^ 40 * 6079680 * 2
def baseEnd_6079680 : Nat := 3121798065526878457740067

theorem tailTrace_6079680 : CollatzResearch.WordTrace tailWord_6079680 prefixEnd_6079680 3121798065526878457740067 := by
  unfold tailWord_6079680
  simp only [CollatzResearch.WordTrace]
  refine ⟨110872073307182580761850247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147829431076243441015800329 110872073307182580761850247)
  ·
    refine ⟨166308109960773871142775371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110872073307182580761850247 166308109960773871142775371)
    ·
      refine ⟨249462164941160806714163057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166308109960773871142775371 249462164941160806714163057)
      ·
        refine ⟨187096623705870605035622293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249462164941160806714163057 187096623705870605035622293)
        ·
          refine ⟨8770154236212684611044795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187096623705870605035622293 8770154236212684611044795)
          ·
            refine ⟨13155231354319026916567193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770154236212684611044795 13155231354319026916567193)
            ·
              refine ⟨9866423515739270187425395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13155231354319026916567193 9866423515739270187425395)
              ·
                refine ⟨14799635273608905281138093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9866423515739270187425395 14799635273608905281138093)
                ·
                  refine ⟨5549863227603339480426785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14799635273608905281138093 5549863227603339480426785)
                  ·
                    refine ⟨4162397420702504610320089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549863227603339480426785 4162397420702504610320089)
                    ·
                      refine ⟨3121798065526878457740067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162397420702504610320089 3121798065526878457740067)
                      ·
                        rfl

theorem cell23_6079680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_6079680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079680 prefixEnd_6079680 := by exact prefixLift 6079680
  have htrace : WordTrace (prefixWord ++ tailWord_6079680) baseStart_6079680 baseEnd_6079680 := by
    simpa [prefixWord, tailWord_6079680, baseEnd_6079680] using wordTrace_append hprefix tailTrace_6079680
  have hstable : (prefixWord ++ tailWord_6079680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079680).length < 2 ^ (prefixWord ++ tailWord_6079680).sum := by decide
  have hdescent : baseEnd_6079680 < baseStart_6079680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079723 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 1, 3, 2]
def baseStart_6079723 : Nat := 118140960795 + 6079723 * 2 ^ 59
def prefixEnd_6079723 : Nat := 4983230072969 + 3 ^ 40 * 6079723 * 2
def baseEnd_6079723 : Nat := 3121820145195021789502369

theorem tailTrace_6079723 : CollatzResearch.WordTrace tailWord_6079723 prefixEnd_6079723 3121820145195021789502369 := by
  unfold tailWord_6079723
  simp only [CollatzResearch.WordTrace]
  refine ⟨221745714953209379867515823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147830476635472919911677215 221745714953209379867515823)
  ·
    refine ⟨332618572429814069801273735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221745714953209379867515823 332618572429814069801273735)
    ·
      refine ⟨498927858644721104701910603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332618572429814069801273735 498927858644721104701910603)
      ·
        refine ⟨748391787967081657052865905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498927858644721104701910603 748391787967081657052865905)
        ·
          refine ⟨561293840975311242789649429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748391787967081657052865905 561293840975311242789649429)
          ·
            refine ⟨26310648795717714505764817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 561293840975311242789649429 26310648795717714505764817)
            ·
              refine ⟨19732986596788285879323613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26310648795717714505764817 19732986596788285879323613)
              ·
                refine ⟨7399869973795607204746355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19732986596788285879323613 7399869973795607204746355)
                ·
                  refine ⟨11099804960693410807119533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399869973795607204746355 11099804960693410807119533)
                  ·
                    refine ⟨4162426860260029052669825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11099804960693410807119533 4162426860260029052669825)
                    ·
                      refine ⟨3121820145195021789502369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162426860260029052669825 3121820145195021789502369)
                      ·
                        rfl

theorem cell23_6079723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3, 2].length) (baseStart_6079723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079723 prefixEnd_6079723 := by exact prefixLift 6079723
  have htrace : WordTrace (prefixWord ++ tailWord_6079723) baseStart_6079723 baseEnd_6079723 := by
    simpa [prefixWord, tailWord_6079723, baseEnd_6079723] using wordTrace_append hprefix tailTrace_6079723
  have hstable : (prefixWord ++ tailWord_6079723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079723).length < 2 ^ (prefixWord ++ tailWord_6079723).sum := by decide
  have hdescent : baseEnd_6079723 < baseStart_6079723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079749 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_6079749 : Nat := 118140960795 + 6079749 * 2 ^ 59
def prefixEnd_6079749 : Nat := 4983230072969 + 3 ^ 40 * 6079749 * 2
def baseEnd_6079749 : Nat := 3121833495692038687777249

theorem tailTrace_6079749 : CollatzResearch.WordTrace tailWord_6079749 prefixEnd_6079749 3121833495692038687777249 := by
  unfold tailWord_6079749
  simp only [CollatzResearch.WordTrace]
  refine ⟨221746663251115186307962301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147831108834076790871974867 221746663251115186307962301)
  ·
    refine ⟨83154998719168194865485863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221746663251115186307962301 83154998719168194865485863)
    ·
      refine ⟨124732498078752292298228795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83154998719168194865485863 124732498078752292298228795)
      ·
        refine ⟨187098747118128438447343193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124732498078752292298228795 187098747118128438447343193)
        ·
          refine ⟨140324060338596328835507395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187098747118128438447343193 140324060338596328835507395)
          ·
            refine ⟨210486090507894493253261093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140324060338596328835507395 210486090507894493253261093)
            ·
              refine ⟨39466141970230217484986455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210486090507894493253261093 39466141970230217484986455)
              ·
                refine ⟨59199212955345326227479683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39466141970230217484986455 59199212955345326227479683)
                ·
                  refine ⟨88798819433017989341219525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59199212955345326227479683 88798819433017989341219525)
                  ·
                    refine ⟨16649778643690873001478661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88798819433017989341219525 16649778643690873001478661)
                    ·
                      refine ⟨3121833495692038687777249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16649778643690873001478661 3121833495692038687777249)
                      ·
                        rfl

theorem cell23_6079749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_6079749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079749 prefixEnd_6079749 := by exact prefixLift 6079749
  have htrace : WordTrace (prefixWord ++ tailWord_6079749) baseStart_6079749 baseEnd_6079749 := by
    simpa [prefixWord, tailWord_6079749, baseEnd_6079749] using wordTrace_append hprefix tailTrace_6079749
  have hstable : (prefixWord ++ tailWord_6079749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079749).length < 2 ^ (prefixWord ++ tailWord_6079749).sum := by decide
  have hdescent : baseEnd_6079749 < baseStart_6079749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079793 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 5]
def baseStart_6079793 : Nat := 118140960795 + 6079793 * 2 ^ 59
def prefixEnd_6079793 : Nat := 4983230072969 + 3 ^ 40 * 6079793 * 2
def baseEnd_6079793 : Nat := 346872898760092946180783

theorem tailTrace_6079793 : CollatzResearch.WordTrace tailWord_6079793 prefixEnd_6079793 346872898760092946180783 := by
  unfold tailWord_6079793
  simp only [CollatzResearch.WordTrace]
  refine ⟨221748268062955781822564033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147832178708637187881709355 221748268062955781822564033)
  ·
    refine ⟨166311201047216836366923025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221748268062955781822564033 166311201047216836366923025)
    ·
      refine ⟨124733400785412627275192269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166311201047216836366923025 124733400785412627275192269)
      ·
        refine ⟨46775025294529735228197101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124733400785412627275192269 46775025294529735228197101)
        ·
          refine ⟨17540634485448650710573913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46775025294529735228197101 17540634485448650710573913)
          ·
            refine ⟨13155475864086488032930435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17540634485448650710573913 13155475864086488032930435)
            ·
              refine ⟨19733213796129732049395653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13155475864086488032930435 19733213796129732049395653)
              ·
                refine ⟨3699977586774324759261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19733213796129732049395653 3699977586774324759261685)
                ·
                  refine ⟨346872898760092946180783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699977586774324759261685 346872898760092946180783)
                  ·
                    rfl

theorem cell23_6079793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 5].length) (baseStart_6079793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079793 prefixEnd_6079793 := by exact prefixLift 6079793
  have htrace : WordTrace (prefixWord ++ tailWord_6079793) baseStart_6079793 baseEnd_6079793 := by
    simpa [prefixWord, tailWord_6079793, baseEnd_6079793] using wordTrace_append hprefix tailTrace_6079793
  have hstable : (prefixWord ++ tailWord_6079793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079793).length < 2 ^ (prefixWord ++ tailWord_6079793).sum := by decide
  have hdescent : baseEnd_6079793 < baseStart_6079793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079806 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_6079806 : Nat := 118140960795 + 6079806 * 2 ^ 59
def prefixEnd_6079806 : Nat := 4983230072969 + 3 ^ 40 * 6079806 * 2
def baseEnd_6079806 : Nat := 1040620921363114988254829

theorem tailTrace_6079806 : CollatzResearch.WordTrace tailWord_6079806 prefixEnd_6079806 1040620921363114988254829 := by
  unfold tailWord_6079806
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718592776488585630348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147832494807939123361858181 27718592776488585630348409)
  ·
    refine ⟨20788944582366439222761307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27718592776488585630348409 20788944582366439222761307)
    ·
      refine ⟨31183416873549658834141961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20788944582366439222761307 31183416873549658834141961)
      ·
        refine ⟨23387562655162244125606471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31183416873549658834141961 23387562655162244125606471)
        ·
          refine ⟨35081343982743366188409707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23387562655162244125606471 35081343982743366188409707)
          ·
            refine ⟨52622015974115049282614561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35081343982743366188409707 52622015974115049282614561)
            ·
              refine ⟨39466511980586286961960921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52622015974115049282614561 39466511980586286961960921)
              ·
                refine ⟨29599883985439715221470691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39466511980586286961960921 29599883985439715221470691)
                ·
                  refine ⟨44399825978159572832206037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29599883985439715221470691 44399825978159572832206037)
                  ·
                    refine ⟨1040620921363114988254829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44399825978159572832206037 1040620921363114988254829)
                    ·
                      rfl

theorem cell23_6079806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_6079806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079806 prefixEnd_6079806 := by exact prefixLift 6079806
  have htrace : WordTrace (prefixWord ++ tailWord_6079806) baseStart_6079806 baseEnd_6079806 := by
    simpa [prefixWord, tailWord_6079806, baseEnd_6079806] using wordTrace_append hprefix tailTrace_6079806
  have hstable : (prefixWord ++ tailWord_6079806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079806).length < 2 ^ (prefixWord ++ tailWord_6079806).sum := by decide
  have hdescent : baseEnd_6079806 < baseStart_6079806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079843 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 4, 2]
def baseStart_6079843 : Nat := 118140960795 + 6079843 * 2 ^ 59
def prefixEnd_6079843 : Nat := 4983230072969 + 3 ^ 40 * 6079843 * 2
def baseEnd_6079843 : Nat := 3121881762873561320001817

theorem tailTrace_6079843 : CollatzResearch.WordTrace tailWord_6079843 prefixEnd_6079843 3121881762873561320001817 := by
  unfold tailWord_6079843
  simp only [CollatzResearch.WordTrace]
  refine ⟨221750091712774640361884183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147833394475183093574589455 221750091712774640361884183)
  ·
    refine ⟨332625137569161960542826275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221750091712774640361884183 332625137569161960542826275)
    ·
      refine ⟨498937706353742940814239413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332625137569161960542826275 498937706353742940814239413)
      ·
        refine ⟨46775409970663400701334945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 498937706353742940814239413 46775409970663400701334945)
        ·
          refine ⟨35081557477997550526001209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46775409970663400701334945 35081557477997550526001209)
          ·
            refine ⟨26311168108498162894500907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35081557477997550526001209 26311168108498162894500907)
            ·
              refine ⟨39466752162747244341751361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26311168108498162894500907 39466752162747244341751361)
              ·
                refine ⟨29600064122060433256313521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39466752162747244341751361 29600064122060433256313521)
                ·
                  refine ⟨22200048091545324942235141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29600064122060433256313521 22200048091545324942235141)
                  ·
                    refine ⟨4162509017164748426669089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22200048091545324942235141 4162509017164748426669089)
                    ·
                      refine ⟨3121881762873561320001817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162509017164748426669089 3121881762873561320001817)
                      ·
                        rfl

theorem cell23_6079843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_6079843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079843 prefixEnd_6079843 := by exact prefixLift 6079843
  have htrace : WordTrace (prefixWord ++ tailWord_6079843) baseStart_6079843 baseEnd_6079843 := by
    simpa [prefixWord, tailWord_6079843, baseEnd_6079843] using wordTrace_append hprefix tailTrace_6079843
  have hstable : (prefixWord ++ tailWord_6079843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079843).length < 2 ^ (prefixWord ++ tailWord_6079843).sum := by decide
  have hdescent : baseEnd_6079843 < baseStart_6079843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079853 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_6079853 : Nat := 118140960795 + 6079853 * 2 ^ 59
def prefixEnd_6079853 : Nat := 4983230072969 + 3 ^ 40 * 6079853 * 2
def baseEnd_6079853 : Nat := 1040628965893368760292257

theorem tailTrace_6079853 : CollatzResearch.WordTrace tailWord_6079853 prefixEnd_6079853 1040628965893368760292257 := by
  unfold tailWord_6079853
  simp only [CollatzResearch.WordTrace]
  refine ⟨221750456442738412069748213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147833637628492274713165475 221750456442738412069748213)
  ·
    refine ⟨20789105291506726131538895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221750456442738412069748213 20789105291506726131538895)
    ·
      refine ⟨31183657937260089197308343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789105291506726131538895 31183657937260089197308343)
      ·
        refine ⟨46775486905890133795962515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31183657937260089197308343 46775486905890133795962515)
        ·
          refine ⟨70163230358835200693943773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46775486905890133795962515 70163230358835200693943773)
          ·
            refine ⟨26311211384563200260228915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70163230358835200693943773 26311211384563200260228915)
            ·
              refine ⟨39466817076844800390343373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26311211384563200260228915 39466817076844800390343373)
              ·
                refine ⟨14800056403816800146378765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39466817076844800390343373 14800056403816800146378765)
                ·
                  refine ⟨5550021151431300054892037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14800056403816800146378765 5550021151431300054892037)
                  ·
                    refine ⟨1040628965893368760292257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550021151431300054892037 1040628965893368760292257)
                    ·
                      rfl

theorem cell23_6079853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_6079853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079853 prefixEnd_6079853 := by exact prefixLift 6079853
  have htrace : WordTrace (prefixWord ++ tailWord_6079853) baseStart_6079853 baseEnd_6079853 := by
    simpa [prefixWord, tailWord_6079853, baseEnd_6079853] using wordTrace_append hprefix tailTrace_6079853
  have hstable : (prefixWord ++ tailWord_6079853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079853).length < 2 ^ (prefixWord ++ tailWord_6079853).sum := by decide
  have hdescent : baseEnd_6079853 < baseStart_6079853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079893 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_6079893 : Nat := 118140960795 + 6079893 * 2 ^ 59
def prefixEnd_6079893 : Nat := 4983230072969 + 3 ^ 40 * 6079893 * 2
def baseEnd_6079893 : Nat := 3121907436906286124376587

theorem tailTrace_6079893 : CollatzResearch.WordTrace tailWord_6079893 prefixEnd_6079893 3121907436906286124376587 := by
  unfold tailWord_6079893
  simp only [CollatzResearch.WordTrace]
  refine ⟨221751915362593498901204333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147834610241728999267469555 221751915362593498901204333)
  ·
    refine ⟨83156968260972562087951625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221751915362593498901204333 83156968260972562087951625)
    ·
      refine ⟨62367726195729421565963719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83156968260972562087951625 62367726195729421565963719)
      ·
        refine ⟨93551589293594132348945579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62367726195729421565963719 93551589293594132348945579)
        ·
          refine ⟨140327383940391198523418369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93551589293594132348945579 140327383940391198523418369)
          ·
            refine ⟨105245537955293398892563777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140327383940391198523418369 105245537955293398892563777)
            ·
              refine ⟨78934153466470049169422833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105245537955293398892563777 78934153466470049169422833)
              ·
                refine ⟨59200615099852536877067125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78934153466470049169422833 59200615099852536877067125)
                ·
                  refine ⟨5550057665611175332225043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59200615099852536877067125 5550057665611175332225043)
                  ·
                    refine ⟨8325086498416762998337565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5550057665611175332225043 8325086498416762998337565)
                    ·
                      refine ⟨3121907436906286124376587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8325086498416762998337565 3121907436906286124376587)
                      ·
                        rfl

theorem cell23_6079893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_6079893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079893 prefixEnd_6079893 := by exact prefixLift 6079893
  have htrace : WordTrace (prefixWord ++ tailWord_6079893) baseStart_6079893 baseEnd_6079893 := by
    simpa [prefixWord, tailWord_6079893, baseEnd_6079893] using wordTrace_append hprefix tailTrace_6079893
  have hstable : (prefixWord ++ tailWord_6079893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079893).length < 2 ^ (prefixWord ++ tailWord_6079893).sum := by decide
  have hdescent : baseEnd_6079893 < baseStart_6079893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
