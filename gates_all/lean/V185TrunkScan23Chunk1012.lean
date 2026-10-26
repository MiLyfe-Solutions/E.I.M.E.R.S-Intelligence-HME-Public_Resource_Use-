import V185TrunkScan23Chunk1011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5992672 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_5992672 : Nat := 118140960795 + 5992672 * 2 ^ 59
def prefixEnd_5992672 : Nat := 4983230072969 + 3 ^ 40 * 5992672 * 2
def baseEnd_5992672 : Nat := 1025707046913494292313403

theorem tailTrace_5992672 : CollatzResearch.WordTrace tailWord_5992672 prefixEnd_5992672 1025707046913494292313403 := by
  unfold tailWord_5992672
  simp only [CollatzResearch.WordTrace]
  refine ⟨109285352072790142870174135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145713802763720190493565513 109285352072790142870174135)
  ·
    refine ⟨163928028109185214305261203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109285352072790142870174135 163928028109185214305261203)
    ·
      refine ⟨245892042163777821457891805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163928028109185214305261203 245892042163777821457891805)
      ·
        refine ⟨92209515811416683046709427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245892042163777821457891805 92209515811416683046709427)
        ·
          refine ⟨138314273717125024570064141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92209515811416683046709427 138314273717125024570064141)
          ·
            refine ⟨51867852643921884213774053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138314273717125024570064141 51867852643921884213774053)
            ·
              refine ⟨9725222370735353290082635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51867852643921884213774053 9725222370735353290082635)
              ·
                refine ⟨14587833556103029935123953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9725222370735353290082635 14587833556103029935123953)
                ·
                  refine ⟨10940875167077272451342965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14587833556103029935123953 10940875167077272451342965)
                  ·
                    refine ⟨1025707046913494292313403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10940875167077272451342965 1025707046913494292313403)
                    ·
                      rfl

theorem cell23_5992672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_5992672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992672 prefixEnd_5992672 := by exact prefixLift 5992672
  have htrace : WordTrace (prefixWord ++ tailWord_5992672) baseStart_5992672 baseEnd_5992672 := by
    simpa [prefixWord, tailWord_5992672, baseEnd_5992672] using wordTrace_append hprefix tailTrace_5992672
  have hstable : (prefixWord ++ tailWord_5992672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992672).length < 2 ^ (prefixWord ++ tailWord_5992672).sum := by decide
  have hdescent : baseEnd_5992672 < baseStart_5992672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992736 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 1, 4]
def baseStart_5992736 : Nat := 118140960795 + 5992736 * 2 ^ 59
def prefixEnd_5992736 : Nat := 4983230072969 + 3 ^ 40 * 5992736 * 2
def baseEnd_5992736 : Nat := 1025718001167456875513305

theorem tailTrace_5992736 : CollatzResearch.WordTrace tailWord_5992736 prefixEnd_5992736 1025718001167456875513305 := by
  unfold tailWord_5992736
  simp only [CollatzResearch.WordTrace]
  refine ⟨109286519208674212335339031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145715358944898949780452041 109286519208674212335339031)
  ·
    refine ⟨163929778813011318503008547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109286519208674212335339031 163929778813011318503008547)
    ·
      refine ⟨245894668219516977754512821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163929778813011318503008547 245894668219516977754512821)
      ·
        refine ⟨23052625145579716664485577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245894668219516977754512821 23052625145579716664485577)
        ·
          refine ⟨17289468859184787498364183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23052625145579716664485577 17289468859184787498364183)
          ·
            refine ⟨25934203288777181247546275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17289468859184787498364183 25934203288777181247546275)
            ·
              refine ⟨38901304933165771871319413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25934203288777181247546275 38901304933165771871319413)
              ·
                refine ⟨3646997337484291112936195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38901304933165771871319413 3646997337484291112936195)
                ·
                  refine ⟨5470496006226436669404293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646997337484291112936195 5470496006226436669404293)
                  ·
                    refine ⟨1025718001167456875513305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470496006226436669404293 1025718001167456875513305)
                    ·
                      rfl

theorem cell23_5992736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_5992736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992736 prefixEnd_5992736 := by exact prefixLift 5992736
  have htrace : WordTrace (prefixWord ++ tailWord_5992736) baseStart_5992736 baseEnd_5992736 := by
    simpa [prefixWord, tailWord_5992736, baseEnd_5992736] using wordTrace_append hprefix tailTrace_5992736
  have hstable : (prefixWord ++ tailWord_5992736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992736).length < 2 ^ (prefixWord ++ tailWord_5992736).sum := by decide
  have hdescent : baseEnd_5992736 < baseStart_5992736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992766 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_5992766 : Nat := 118140960795 + 5992766 * 2 ^ 59
def prefixEnd_5992766 : Nat := 4983230072969 + 3 ^ 40 * 5992766 * 2
def baseEnd_5992766 : Nat := 341907711991333945462753

theorem tailTrace_5992766 : CollatzResearch.WordTrace tailWord_5992766 prefixEnd_5992766 341907711991333945462753 := by
  unfold tailWord_5992766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321766575904967474283769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145716088404826493196180101 27321766575904967474283769)
  ·
    refine ⟨20491324931928725605712827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27321766575904967474283769 20491324931928725605712827)
    ·
      refine ⟨30736987397893088408569241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491324931928725605712827 30736987397893088408569241)
      ·
        refine ⟨23052740548419816306426931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30736987397893088408569241 23052740548419816306426931)
        ·
          refine ⟨34579110822629724459640397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23052740548419816306426931 34579110822629724459640397)
          ·
            refine ⟨12967166558486146672365149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34579110822629724459640397 12967166558486146672365149)
            ·
              refine ⟨4862687459432305002136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12967166558486146672365149 4862687459432305002136931)
              ·
                refine ⟨7294031189148457503205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862687459432305002136931 7294031189148457503205397)
                ·
                  refine ⟨341907711991333945462753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7294031189148457503205397 341907711991333945462753)
                  ·
                    rfl

theorem cell23_5992766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_5992766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992766 prefixEnd_5992766 := by exact prefixLift 5992766
  have htrace : WordTrace (prefixWord ++ tailWord_5992766) baseStart_5992766 baseEnd_5992766 := by
    simpa [prefixWord, tailWord_5992766, baseEnd_5992766] using wordTrace_append hprefix tailTrace_5992766
  have hstable : (prefixWord ++ tailWord_5992766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992766).length < 2 ^ (prefixWord ++ tailWord_5992766).sum := by decide
  have hdescent : baseEnd_5992766 < baseStart_5992766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992799 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_5992799 : Nat := 118140960795 + 5992799 * 2 ^ 59
def prefixEnd_5992799 : Nat := 4983230072969 + 3 ^ 40 * 5992799 * 2
def baseEnd_5992799 : Nat := 3077186352783603880052125

theorem tailTrace_5992799 : CollatzResearch.WordTrace tailWord_5992799 prefixEnd_5992799 3077186352783603880052125 := by
  unfold tailWord_5992799
  simp only [CollatzResearch.WordTrace]
  refine ⟨218575336216120186430221451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145716890810746790953480967 218575336216120186430221451)
  ·
    refine ⟨327863004324180279645332177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218575336216120186430221451 327863004324180279645332177)
    ·
      refine ⟨245897253243135209733999133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327863004324180279645332177 245897253243135209733999133)
      ·
        refine ⟨92211469966175703650249675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245897253243135209733999133 92211469966175703650249675)
        ·
          refine ⟨138317204949263555475374513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92211469966175703650249675 138317204949263555475374513)
          ·
            refine ⟨103737903711947666606530885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138317204949263555475374513 103737903711947666606530885)
            ·
              refine ⟨19450856945990187488724541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103737903711947666606530885 19450856945990187488724541)
              ·
                refine ⟨7294071354746320308271703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19450856945990187488724541 7294071354746320308271703)
                ·
                  refine ⟨10941107032119480462407555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294071354746320308271703 10941107032119480462407555)
                  ·
                    refine ⟨16411660548179220693611333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10941107032119480462407555 16411660548179220693611333)
                    ·
                      refine ⟨3077186352783603880052125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16411660548179220693611333 3077186352783603880052125)
                      ·
                        rfl

theorem cell23_5992799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_5992799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992799 prefixEnd_5992799 := by exact prefixLift 5992799
  have htrace : WordTrace (prefixWord ++ tailWord_5992799) baseStart_5992799 baseEnd_5992799 := by
    simpa [prefixWord, tailWord_5992799, baseEnd_5992799] using wordTrace_append hprefix tailTrace_5992799
  have hstable : (prefixWord ++ tailWord_5992799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992799).length < 2 ^ (prefixWord ++ tailWord_5992799).sum := by decide
  have hdescent : baseEnd_5992799 < baseStart_5992799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992809 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_5992809 : Nat := 118140960795 + 5992809 * 2 ^ 59
def prefixEnd_5992809 : Nat := 4983230072969 + 3 ^ 40 * 5992809 * 2
def baseEnd_5992809 : Nat := 1025730495863382946975693

theorem tailTrace_5992809 : CollatzResearch.WordTrace tailWord_5992809 prefixEnd_5992809 1025730495863382946975693 := by
  unfold tailWord_5992809
  simp only [CollatzResearch.WordTrace]
  refine ⟨218575700946083958138085481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145717133964055972092056987 218575700946083958138085481)
  ·
    refine ⟨163931775709562968603564111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218575700946083958138085481 163931775709562968603564111)
    ·
      refine ⟨245897663564344452905346167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163931775709562968603564111 245897663564344452905346167)
      ·
        refine ⟨368846495346516679358019251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245897663564344452905346167 368846495346516679358019251)
        ·
          refine ⟨553269743019775019037028877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368846495346516679358019251 553269743019775019037028877)
          ·
            refine ⟨207476153632415632138885829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553269743019775019037028877 207476153632415632138885829)
            ·
              refine ⟨38901778806077931026041093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207476153632415632138885829 38901778806077931026041093)
              ·
                refine ⟨7294083526139612067382705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38901778806077931026041093 7294083526139612067382705)
                ·
                  refine ⟨5470562644604709050537029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294083526139612067382705 5470562644604709050537029)
                  ·
                    refine ⟨1025730495863382946975693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470562644604709050537029 1025730495863382946975693)
                    ·
                      rfl

theorem cell23_5992809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_5992809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992809 prefixEnd_5992809 := by exact prefixLift 5992809
  have htrace : WordTrace (prefixWord ++ tailWord_5992809) baseStart_5992809 baseEnd_5992809 := by
    simpa [prefixWord, tailWord_5992809, baseEnd_5992809] using wordTrace_append hprefix tailTrace_5992809
  have hstable : (prefixWord ++ tailWord_5992809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992809).length < 2 ^ (prefixWord ++ tailWord_5992809).sum := by decide
  have hdescent : baseEnd_5992809 < baseStart_5992809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992833 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5992833 : Nat := 118140960795 + 5992833 * 2 ^ 59
def prefixEnd_5992833 : Nat := 4983230072969 + 3 ^ 40 * 5992833 * 2
def baseEnd_5992833 : Nat := 3077203811125856747026969

theorem tailTrace_5992833 : CollatzResearch.WordTrace tailWord_5992833 prefixEnd_5992833 3077203811125856747026969 := by
  unfold tailWord_5992833
  simp only [CollatzResearch.WordTrace]
  refine ⟨218576576297997010236959153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145717717531998006824639435 218576576297997010236959153)
  ·
    refine ⟨163932432223497757677719365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218576576297997010236959153 163932432223497757677719365)
    ·
      refine ⟨30737331041905829564572381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163932432223497757677719365 30737331041905829564572381)
      ·
        refine ⟨11526499140714686086714643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30737331041905829564572381 11526499140714686086714643)
        ·
          refine ⟨17289748711072029130071965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526499140714686086714643 17289748711072029130071965)
          ·
            refine ⟨6483655766652010923776987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17289748711072029130071965 6483655766652010923776987)
            ·
              refine ⟨9725483649978016385665481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483655766652010923776987 9725483649978016385665481)
              ·
                refine ⟨7294112737483512289249111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9725483649978016385665481 7294112737483512289249111)
                ·
                  refine ⟨10941169106225268433873667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294112737483512289249111 10941169106225268433873667)
                  ·
                    refine ⟨16411753659337902650810501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10941169106225268433873667 16411753659337902650810501)
                    ·
                      refine ⟨3077203811125856747026969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16411753659337902650810501 3077203811125856747026969)
                      ·
                        rfl

theorem cell23_5992833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5992833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992833 prefixEnd_5992833 := by exact prefixLift 5992833
  have htrace : WordTrace (prefixWord ++ tailWord_5992833) baseStart_5992833 baseEnd_5992833 := by
    simpa [prefixWord, tailWord_5992833, baseEnd_5992833] using wordTrace_append hprefix tailTrace_5992833
  have hstable : (prefixWord ++ tailWord_5992833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992833).length < 2 ^ (prefixWord ++ tailWord_5992833).sum := by decide
  have hdescent : baseEnd_5992833 < baseStart_5992833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992846 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5992846 : Nat := 118140960795 + 5992846 * 2 ^ 59
def prefixEnd_5992846 : Nat := 4983230072969 + 3 ^ 40 * 5992846 * 2
def baseEnd_5992846 : Nat := 3077210486374365196164409

theorem tailTrace_5992846 : CollatzResearch.WordTrace tailWord_5992846 prefixEnd_5992846 3077210486374365196164409 := by
  unfold tailWord_5992846
  simp only [CollatzResearch.WordTrace]
  refine ⟨27322131305868739182147799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145718033631299942304788261 27322131305868739182147799)
  ·
    refine ⟨40983196958803108773221699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27322131305868739182147799 40983196958803108773221699)
    ·
      refine ⟨61474795438204663159832549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40983196958803108773221699 61474795438204663159832549)
      ·
        refine ⟨11526524144663374342468603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61474795438204663159832549 11526524144663374342468603)
        ·
          refine ⟨17289786216995061513702905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526524144663374342468603 17289786216995061513702905)
          ·
            refine ⟨12967339662746296135277179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17289786216995061513702905 12967339662746296135277179)
            ·
              refine ⟨19451009494119444202915769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12967339662746296135277179 19451009494119444202915769)
              ·
                refine ⟨14588257120589583152186827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19451009494119444202915769 14588257120589583152186827)
                ·
                  refine ⟨21882385680884374728280241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14588257120589583152186827 21882385680884374728280241)
                  ·
                    refine ⟨16411789260663281046210181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21882385680884374728280241 16411789260663281046210181)
                    ·
                      refine ⟨3077210486374365196164409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16411789260663281046210181 3077210486374365196164409)
                      ·
                        rfl

theorem cell23_5992846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5992846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992846 prefixEnd_5992846 := by exact prefixLift 5992846
  have htrace : WordTrace (prefixWord ++ tailWord_5992846) baseStart_5992846 baseEnd_5992846 := by
    simpa [prefixWord, tailWord_5992846, baseEnd_5992846] using wordTrace_append hprefix tailTrace_5992846
  have hstable : (prefixWord ++ tailWord_5992846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992846).length < 2 ^ (prefixWord ++ tailWord_5992846).sum := by decide
  have hdescent : baseEnd_5992846 < baseStart_5992846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992867 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 1, 2, 2]
def baseStart_5992867 : Nat := 118140960795 + 5992867 * 2 ^ 59
def prefixEnd_5992867 : Nat := 4983230072969 + 3 ^ 40 * 5992867 * 2
def baseEnd_5992867 : Nat := 3077221269468109614001813

theorem tailTrace_5992867 : CollatzResearch.WordTrace tailWord_5992867 prefixEnd_5992867 3077221269468109614001813 := by
  unfold tailWord_5992867
  simp only [CollatzResearch.WordTrace]
  refine ⟨218577816379873834043696855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145718544253249222695797903 218577816379873834043696855)
  ·
    refine ⟨327866724569810751065545283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218577816379873834043696855 327866724569810751065545283)
    ·
      refine ⟨491800086854716126598317925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327866724569810751065545283 491800086854716126598317925)
      ·
        refine ⟨92212516285259273737184611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 491800086854716126598317925 92212516285259273737184611)
        ·
          refine ⟨138318774427888910605776917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92212516285259273737184611 138318774427888910605776917)
          ·
            refine ⟨6483692551307292684645793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138318774427888910605776917 6483692551307292684645793)
            ·
              refine ⟨4862769413480469513484345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6483692551307292684645793 4862769413480469513484345)
              ·
                refine ⟨3647077060110352135113259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4862769413480469513484345 3647077060110352135113259)
                ·
                  refine ⟨5470615590165528202669889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647077060110352135113259 5470615590165528202669889)
                  ·
                    refine ⟨4102961692624146152002417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470615590165528202669889 4102961692624146152002417)
                    ·
                      refine ⟨3077221269468109614001813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102961692624146152002417 3077221269468109614001813)
                      ·
                        rfl

theorem cell23_5992867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_5992867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992867 prefixEnd_5992867 := by exact prefixLift 5992867
  have htrace : WordTrace (prefixWord ++ tailWord_5992867) baseStart_5992867 baseEnd_5992867 := by
    simpa [prefixWord, tailWord_5992867, baseEnd_5992867] using wordTrace_append hprefix tailTrace_5992867
  have hstable : (prefixWord ++ tailWord_5992867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992867).length < 2 ^ (prefixWord ++ tailWord_5992867).sum := by decide
  have hdescent : baseEnd_5992867 < baseStart_5992867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992906 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_5992906 : Nat := 118140960795 + 5992906 * 2 ^ 59
def prefixEnd_5992906 : Nat := 4983230072969 + 3 ^ 40 * 5992906 * 2
def baseEnd_5992906 : Nat := 3077241295213634961414133

theorem tailTrace_5992906 : CollatzResearch.WordTrace tailWord_5992906 prefixEnd_5992906 3077241295213634961414133 := by
  unfold tailWord_5992906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54644809706683135926091643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145719492551155029136244381 54644809706683135926091643)
  ·
    refine ⟨81967214560024703889137465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54644809706683135926091643 81967214560024703889137465)
    ·
      refine ⟨61475410920018527916853099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81967214560024703889137465 61475410920018527916853099)
      ·
        refine ⟨92213116380027791875279649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61475410920018527916853099 92213116380027791875279649)
        ·
          refine ⟨69159837285020843906459737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92213116380027791875279649 69159837285020843906459737)
          ·
            refine ⟨51869877963765632929844803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69159837285020843906459737 51869877963765632929844803)
            ·
              refine ⟨77804816945648449394767205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51869877963765632929844803 77804816945648449394767205)
              ·
                refine ⟨14588403177309084261518851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77804816945648449394767205 14588403177309084261518851)
                ·
                  refine ⟨21882604765963626392278277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14588403177309084261518851 21882604765963626392278277)
                  ·
                    refine ⟨4102988393618179948552177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21882604765963626392278277 4102988393618179948552177)
                    ·
                      refine ⟨3077241295213634961414133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4102988393618179948552177 3077241295213634961414133)
                      ·
                        rfl

theorem cell23_5992906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_5992906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992906 prefixEnd_5992906 := by exact prefixLift 5992906
  have htrace : WordTrace (prefixWord ++ tailWord_5992906) baseStart_5992906 baseEnd_5992906 := by
    simpa [prefixWord, tailWord_5992906, baseEnd_5992906] using wordTrace_append hprefix tailTrace_5992906
  have hstable : (prefixWord ++ tailWord_5992906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992906).length < 2 ^ (prefixWord ++ tailWord_5992906).sum := by decide
  have hdescent : baseEnd_5992906 < baseStart_5992906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992929 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 7]
def baseStart_5992929 : Nat := 118140960795 + 5992929 * 2 ^ 59
def prefixEnd_5992929 : Nat := 4983230072969 + 3 ^ 40 * 5992929 * 2
def baseEnd_5992929 : Nat := 341917011696520930158503

theorem tailTrace_5992929 : CollatzResearch.WordTrace tailWord_5992929 prefixEnd_5992929 341917011696520930158503 := by
  unfold tailWord_5992929
  simp only [CollatzResearch.WordTrace]
  refine ⟨218580077705649218632453841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145720051803766145754969227 218580077705649218632453841)
  ·
    refine ⟨163935058279236913974340381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218580077705649218632453841 163935058279236913974340381)
    ·
      refine ⟨61475646854713842740377643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163935058279236913974340381 61475646854713842740377643)
      ·
        refine ⟨92213470282070764110566465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61475646854713842740377643 92213470282070764110566465)
        ·
          refine ⟨69160102711553073082924849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92213470282070764110566465 69160102711553073082924849)
          ·
            refine ⟨51870077033664804812193637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69160102711553073082924849 51870077033664804812193637)
            ·
              refine ⟨9725639443812150902286307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51870077033664804812193637 9725639443812150902286307)
              ·
                refine ⟨14588459165718226353429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9725639443812150902286307 14588459165718226353429461)
                ·
                  refine ⟨341917011696520930158503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14588459165718226353429461 341917011696520930158503)
                  ·
                    rfl

theorem cell23_5992929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_5992929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992929 prefixEnd_5992929 := by exact prefixLift 5992929
  have htrace : WordTrace (prefixWord ++ tailWord_5992929) baseStart_5992929 baseEnd_5992929 := by
    simpa [prefixWord, tailWord_5992929, baseEnd_5992929] using wordTrace_append hprefix tailTrace_5992929
  have hstable : (prefixWord ++ tailWord_5992929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992929).length < 2 ^ (prefixWord ++ tailWord_5992929).sum := by decide
  have hdescent : baseEnd_5992929 < baseStart_5992929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992939 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3]
def baseStart_5992939 : Nat := 118140960795 + 5992939 * 2 ^ 59
def prefixEnd_5992939 : Nat := 4983230072969 + 3 ^ 40 * 5992939 * 2
def baseEnd_5992939 : Nat := 3077258240075233332301481

theorem tailTrace_5992939 : CollatzResearch.WordTrace tailWord_5992939 prefixEnd_5992939 3077258240075233332301481 := by
  unfold tailWord_5992939
  simp only [CollatzResearch.WordTrace]
  refine ⟨218580442435612990340317871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145720294957075326893545247 218580442435612990340317871)
  ·
    refine ⟨327870663653419485510476807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218580442435612990340317871 327870663653419485510476807)
    ·
      refine ⟨491805995480129228265715211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327870663653419485510476807 491805995480129228265715211)
      ·
        refine ⟨737708993220193842398572817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491805995480129228265715211 737708993220193842398572817)
        ·
          refine ⟨553281744915145381798929613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737708993220193842398572817 553281744915145381798929613)
          ·
            refine ⟨207480654343179518174598605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553281744915145381798929613 207480654343179518174598605)
            ·
              refine ⟨77805245378692319315474477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207480654343179518174598605 77805245378692319315474477)
              ·
                refine ⟨29176967017009619743302929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77805245378692319315474477 29176967017009619743302929)
                ·
                  refine ⟨21882725262757214807477197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29176967017009619743302929 21882725262757214807477197)
                  ·
                    refine ⟨8206021973533955552803949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21882725262757214807477197 8206021973533955552803949)
                    ·
                      refine ⟨3077258240075233332301481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206021973533955552803949 3077258240075233332301481)
                      ·
                        rfl

theorem cell23_5992939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].length) (baseStart_5992939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992939 prefixEnd_5992939 := by exact prefixLift 5992939
  have htrace : WordTrace (prefixWord ++ tailWord_5992939) baseStart_5992939 baseEnd_5992939 := by
    simpa [prefixWord, tailWord_5992939, baseEnd_5992939] using wordTrace_append hprefix tailTrace_5992939
  have hstable : (prefixWord ++ tailWord_5992939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992939).length < 2 ^ (prefixWord ++ tailWord_5992939).sum := by decide
  have hdescent : baseEnd_5992939 < baseStart_5992939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992940 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_5992940 : Nat := 118140960795 + 5992940 * 2 ^ 59
def prefixEnd_5992940 : Nat := 4983230072969 + 3 ^ 40 * 5992940 * 2
def baseEnd_5992940 : Nat := 3077258753555887828388977

theorem tailTrace_5992940 : CollatzResearch.WordTrace tailWord_5992940 prefixEnd_5992940 3077258753555887828388977 := by
  unfold tailWord_5992940
  simp only [CollatzResearch.WordTrace]
  refine ⟨109290239454304683755552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145720319272406245007402849 109290239454304683755552137)
  ·
    refine ⟨81967679590728512816664103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109290239454304683755552137 81967679590728512816664103)
    ·
      refine ⟨122951519386092769224996155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81967679590728512816664103 122951519386092769224996155)
      ·
        refine ⟨184427279079139153837494233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122951519386092769224996155 184427279079139153837494233)
        ·
          refine ⟨138320459309354365378120675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184427279079139153837494233 138320459309354365378120675)
          ·
            refine ⟨207480688964031548067181013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138320459309354365378120675 207480688964031548067181013)
            ·
              refine ⟨4862828647594489407824555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207480688964031548067181013 4862828647594489407824555)
              ·
                refine ⟨7294242971391734111736833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862828647594489407824555 7294242971391734111736833)
                ·
                  refine ⟨5470682228543800583802625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294242971391734111736833 5470682228543800583802625)
                  ·
                    refine ⟨4103011671407850437851969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470682228543800583802625 4103011671407850437851969)
                    ·
                      refine ⟨3077258753555887828388977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103011671407850437851969 3077258753555887828388977)
                      ·
                        rfl

theorem cell23_5992940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_5992940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992940 prefixEnd_5992940 := by exact prefixLift 5992940
  have htrace : WordTrace (prefixWord ++ tailWord_5992940) baseStart_5992940 baseEnd_5992940 := by
    simpa [prefixWord, tailWord_5992940, baseEnd_5992940] using wordTrace_append hprefix tailTrace_5992940
  have hstable : (prefixWord ++ tailWord_5992940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992940).length < 2 ^ (prefixWord ++ tailWord_5992940).sum := by decide
  have hdescent : baseEnd_5992940 < baseStart_5992940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5992959 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 2, 5]
def baseStart_5992959 : Nat := 118140960795 + 5992959 * 2 ^ 59
def prefixEnd_5992959 : Nat := 4983230072969 + 3 ^ 40 * 5992959 * 2
def baseEnd_5992959 : Nat := 1025756169896107751350463

theorem tailTrace_5992959 : CollatzResearch.WordTrace tailWord_5992959 prefixEnd_5992959 1025756169896107751350463 := by
  unfold tailWord_5992959
  simp only [CollatzResearch.WordTrace]
  refine ⟨218581171895540533756045931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145720781263693689170697287 218581171895540533756045931)
  ·
    refine ⟨327871757843310800634068897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218581171895540533756045931 327871757843310800634068897)
    ·
      refine ⟨245903818382483100475551673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327871757843310800634068897 245903818382483100475551673)
      ·
        refine ⟨184427863786862325356663755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245903818382483100475551673 184427863786862325356663755)
        ·
          refine ⟨276641795680293488034995633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184427863786862325356663755 276641795680293488034995633)
          ·
            refine ⟨207481346760220116026246725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276641795680293488034995633 207481346760220116026246725)
            ·
              refine ⟨38902752517541271754921261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207481346760220116026246725 38902752517541271754921261)
              ·
                refine ⟨14588532194077976908095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38902752517541271754921261 14588532194077976908095473)
                ·
                  refine ⟨10941399145558482681071605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14588532194077976908095473 10941399145558482681071605)
                  ·
                    refine ⟨1025756169896107751350463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10941399145558482681071605 1025756169896107751350463)
                    ·
                      rfl

theorem cell23_5992959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_5992959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5992959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5992959 prefixEnd_5992959 := by exact prefixLift 5992959
  have htrace : WordTrace (prefixWord ++ tailWord_5992959) baseStart_5992959 baseEnd_5992959 := by
    simpa [prefixWord, tailWord_5992959, baseEnd_5992959] using wordTrace_append hprefix tailTrace_5992959
  have hstable : (prefixWord ++ tailWord_5992959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5992959).length < 2 ^ (prefixWord ++ tailWord_5992959).sum := by decide
  have hdescent : baseEnd_5992959 < baseStart_5992959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5992959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993009 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5993009 : Nat := 118140960795 + 5993009 * 2 ^ 59
def prefixEnd_5993009 : Nat := 4983230072969 + 3 ^ 40 * 5993009 * 2
def baseEnd_5993009 : Nat := 3077294183721048058426159

theorem tailTrace_5993009 : CollatzResearch.WordTrace tailWord_5993009 prefixEnd_5993009 3077294183721048058426159 := by
  unfold tailWord_5993009
  simp only [CollatzResearch.WordTrace]
  refine ⟨218582995545359392295366081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145721997030239594863577387 218582995545359392295366081)
  ·
    refine ⟨163937246659019544221524561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218582995545359392295366081 163937246659019544221524561)
    ·
      refine ⟨122952934994264658166143421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163937246659019544221524561 122952934994264658166143421)
      ·
        refine ⟨46107350622849246812303783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122952934994264658166143421 46107350622849246812303783)
        ·
          refine ⟨69161025934273870218455675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46107350622849246812303783 69161025934273870218455675)
          ·
            refine ⟨103741538901410805327683513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69161025934273870218455675 103741538901410805327683513)
            ·
              refine ⟨77806154176058103995762635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103741538901410805327683513 77806154176058103995762635)
              ·
                refine ⟨116709231264087155993643953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77806154176058103995762635 116709231264087155993643953)
                ·
                  refine ⟨87531923448065366995232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116709231264087155993643953 87531923448065366995232965)
                  ·
                    refine ⟨16412235646512256311606181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87531923448065366995232965 16412235646512256311606181)
                    ·
                      refine ⟨3077294183721048058426159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16412235646512256311606181 3077294183721048058426159)
                      ·
                        rfl

theorem cell23_5993009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5993009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993009 prefixEnd_5993009 := by exact prefixLift 5993009
  have htrace : WordTrace (prefixWord ++ tailWord_5993009) baseStart_5993009 baseEnd_5993009 := by
    simpa [prefixWord, tailWord_5993009, baseEnd_5993009] using wordTrace_append hprefix tailTrace_5993009
  have hstable : (prefixWord ++ tailWord_5993009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993009).length < 2 ^ (prefixWord ++ tailWord_5993009).sum := by decide
  have hdescent : baseEnd_5993009 < baseStart_5993009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993023 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 1, 4]
def baseStart_5993023 : Nat := 118140960795 + 5993023 * 2 ^ 59
def prefixEnd_5993023 : Nat := 4983230072969 + 3 ^ 40 * 5993023 * 2
def baseEnd_5993023 : Nat := 1025767124150070334550365

theorem tailTrace_5993023 : CollatzResearch.WordTrace tailWord_5993023 prefixEnd_5993023 1025767124150070334550365 := by
  unfold tailWord_5993023
  simp only [CollatzResearch.WordTrace]
  refine ⟨218583506167308672686375723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145722337444872448457583815 218583506167308672686375723)
  ·
    refine ⟨327875259250963009029563585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218583506167308672686375723 327875259250963009029563585)
    ·
      refine ⟨245906444438222256772172689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327875259250963009029563585 245906444438222256772172689)
      ·
        refine ⟨184429833328666692579129517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245906444438222256772172689 184429833328666692579129517)
        ·
          refine ⟨69161187498250009717173569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184429833328666692579129517 69161187498250009717173569)
          ·
            refine ⟨51870890623687507287880177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69161187498250009717173569 51870890623687507287880177)
            ·
              refine ⟨38903167967765630465910133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51870890623687507287880177 38903167967765630465910133)
              ·
                refine ⟨3647171996978027856179075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38903167967765630465910133 3647171996978027856179075)
                ·
                  refine ⟨5470757995467041784268613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647171996978027856179075 5470757995467041784268613)
                  ·
                    refine ⟨1025767124150070334550365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470757995467041784268613 1025767124150070334550365)
                    ·
                      rfl

theorem cell23_5993023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_5993023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993023 prefixEnd_5993023 := by exact prefixLift 5993023
  have htrace : WordTrace (prefixWord ++ tailWord_5993023) baseStart_5993023 baseEnd_5993023 := by
    simpa [prefixWord, tailWord_5993023, baseEnd_5993023] using wordTrace_append hprefix tailTrace_5993023
  have hstable : (prefixWord ++ tailWord_5993023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993023).length < 2 ^ (prefixWord ++ tailWord_5993023).sum := by decide
  have hdescent : baseEnd_5993023 < baseStart_5993023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993030 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5993030 : Nat := 118140960795 + 5993030 * 2 ^ 59
def prefixEnd_5993030 : Nat := 4983230072969 + 3 ^ 40 * 5993030 * 2
def baseEnd_5993030 : Nat := 3077304966814792476263563

theorem tailTrace_5993030 : CollatzResearch.WordTrace tailWord_5993030 prefixEnd_5993030 3077304966814792476263563 := by
  unfold tailWord_5993030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830742546196353527558767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145722507652188875254587029 6830742546196353527558767)
  ·
    refine ⟨10246113819294530291338151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830742546196353527558767 10246113819294530291338151)
    ·
      refine ⟨15369170728941795437007227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246113819294530291338151 15369170728941795437007227)
      ·
        refine ⟨23053756093412693155510841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15369170728941795437007227 23053756093412693155510841)
        ·
          refine ⟨17290317070059519866633131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23053756093412693155510841 17290317070059519866633131)
          ·
            refine ⟨25935475605089279799949697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17290317070059519866633131 25935475605089279799949697)
            ·
              refine ⟨19451606703816959849962273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25935475605089279799949697 19451606703816959849962273)
              ·
                refine ⟨14588705027862719887471705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19451606703816959849962273 14588705027862719887471705)
                ·
                  refine ⟨10941528770897039915603779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14588705027862719887471705 10941528770897039915603779)
                  ·
                    refine ⟨16412293156345559873405669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10941528770897039915603779 16412293156345559873405669)
                    ·
                      refine ⟨3077304966814792476263563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16412293156345559873405669 3077304966814792476263563)
                      ·
                        rfl

theorem cell23_5993030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5993030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993030 prefixEnd_5993030 := by exact prefixLift 5993030
  have htrace : WordTrace (prefixWord ++ tailWord_5993030) baseStart_5993030 baseEnd_5993030 := by
    simpa [prefixWord, tailWord_5993030, baseEnd_5993030] using wordTrace_append hprefix tailTrace_5993030
  have hstable : (prefixWord ++ tailWord_5993030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993030).length < 2 ^ (prefixWord ++ tailWord_5993030).sum := by decide
  have hdescent : baseEnd_5993030 < baseStart_5993030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993036 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 6]
def baseStart_5993036 : Nat := 118140960795 + 5993036 * 2 ^ 59
def prefixEnd_5993036 : Nat := 4983230072969 + 3 ^ 40 * 5993036 * 2
def baseEnd_5993036 : Nat := 341923116410968828087615

theorem tailTrace_5993036 : CollatzResearch.WordTrace tailWord_5993036 prefixEnd_5993036 341923116410968828087615 := by
  unfold tailWord_5993036
  simp only [CollatzResearch.WordTrace]
  refine ⟨109291990158130787953299481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145722653544174383937732641 109291990158130787953299481)
  ·
    refine ⟨81968992618598090964974611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109291990158130787953299481 81968992618598090964974611)
    ·
      refine ⟨122953488927897136447461917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81968992618598090964974611 122953488927897136447461917)
      ·
        refine ⟨46107558347961426167798219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122953488927897136447461917 46107558347961426167798219)
        ·
          refine ⟨69161337521942139251697329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46107558347961426167798219 69161337521942139251697329)
          ·
            refine ⟨51871003141456604438772997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69161337521942139251697329 51871003141456604438772997)
            ·
              refine ⟨9725813089023113332269937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51871003141456604438772997 9725813089023113332269937)
              ·
                refine ⟨7294359816767334999202453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9725813089023113332269937 7294359816767334999202453)
                ·
                  refine ⟨341923116410968828087615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7294359816767334999202453 341923116410968828087615)
                  ·
                    rfl

theorem cell23_5993036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_5993036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993036 prefixEnd_5993036 := by exact prefixLift 5993036
  have htrace : WordTrace (prefixWord ++ tailWord_5993036) baseStart_5993036 baseEnd_5993036 := by
    simpa [prefixWord, tailWord_5993036, baseEnd_5993036] using wordTrace_append hprefix tailTrace_5993036
  have hstable : (prefixWord ++ tailWord_5993036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993036).length < 2 ^ (prefixWord ++ tailWord_5993036).sum := by decide
  have hdescent : baseEnd_5993036 < baseStart_5993036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993059 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5993059 : Nat := 118140960795 + 5993059 * 2 ^ 59
def prefixEnd_5993059 : Nat := 4983230072969 + 3 ^ 40 * 5993059 * 2
def baseEnd_5993059 : Nat := 3077319857753772862800929

theorem tailTrace_5993059 : CollatzResearch.WordTrace tailWord_5993059 prefixEnd_5993059 3077319857753772862800929 := by
  unfold tailWord_5993059
  simp only [CollatzResearch.WordTrace]
  refine ⟨218584819195178250834686231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145723212796785500556457487 218584819195178250834686231)
  ·
    refine ⟨327877228792767376252029347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218584819195178250834686231 327877228792767376252029347)
    ·
      refine ⟨491815843189151064378044021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327877228792767376252029347 491815843189151064378044021)
      ·
        refine ⟨46107735298982912285441627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491815843189151064378044021 46107735298982912285441627)
        ·
          refine ⟨69161602948474368428162441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46107735298982912285441627 69161602948474368428162441)
          ·
            refine ⟨51871202211355776321121831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69161602948474368428162441 51871202211355776321121831)
            ·
              refine ⟨77806803317033664481682747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51871202211355776321121831 77806803317033664481682747)
              ·
                refine ⟨116710204975550496722524121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77806803317033664481682747 116710204975550496722524121)
                ·
                  refine ⟨87532653731662872541893091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116710204975550496722524121 87532653731662872541893091)
                  ·
                    refine ⟨131298980597494308812839637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87532653731662872541893091 131298980597494308812839637)
                    ·
                      refine ⟨3077319857753772862800929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131298980597494308812839637 3077319857753772862800929)
                      ·
                        rfl

theorem cell23_5993059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5993059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993059 prefixEnd_5993059 := by exact prefixLift 5993059
  have htrace : WordTrace (prefixWord ++ tailWord_5993059) baseStart_5993059 baseEnd_5993059 := by
    simpa [prefixWord, tailWord_5993059, baseEnd_5993059] using wordTrace_append hprefix tailTrace_5993059
  have hstable : (prefixWord ++ tailWord_5993059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993059).length < 2 ^ (prefixWord ++ tailWord_5993059).sum := by decide
  have hdescent : baseEnd_5993059 < baseStart_5993059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993066 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_5993066 : Nat := 118140960795 + 5993066 * 2 ^ 59
def prefixEnd_5993066 : Nat := 4983230072969 + 3 ^ 40 * 5993066 * 2
def baseEnd_5993066 : Nat := 1025774484039451445137799

theorem tailTrace_5993066 : CollatzResearch.WordTrace tailWord_5993066 prefixEnd_5993066 1025774484039451445137799 := by
  unfold tailWord_5993066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54646268626538222757547763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145723383004101927353460701 54646268626538222757547763)
  ·
    refine ⟨81969402939807334136321645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54646268626538222757547763 81969402939807334136321645)
    ·
      refine ⟨30738526102427750301120617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81969402939807334136321645 30738526102427750301120617)
      ·
        refine ⟨23053894576820812725840463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30738526102427750301120617 23053894576820812725840463)
        ·
          refine ⟨34580841865231219088760695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23053894576820812725840463 34580841865231219088760695)
          ·
            refine ⟨51871262797846828633141043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34580841865231219088760695 51871262797846828633141043)
            ·
              refine ⟨77806894196770242949711565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51871262797846828633141043 77806894196770242949711565)
              ·
                refine ⟨29177585323788841106141837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77806894196770242949711565 29177585323788841106141837)
                ·
                  refine ⟨10941594496420815414803189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29177585323788841106141837 10941594496420815414803189)
                  ·
                    refine ⟨1025774484039451445137799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10941594496420815414803189 1025774484039451445137799)
                    ·
                      rfl

theorem cell23_5993066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_5993066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993066 prefixEnd_5993066 := by exact prefixLift 5993066
  have htrace : WordTrace (prefixWord ++ tailWord_5993066) baseStart_5993066 baseEnd_5993066 := by
    simpa [prefixWord, tailWord_5993066, baseEnd_5993066] using wordTrace_append hprefix tailTrace_5993066
  have hstable : (prefixWord ++ tailWord_5993066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993066).length < 2 ^ (prefixWord ++ tailWord_5993066).sum := by decide
  have hdescent : baseEnd_5993066 < baseStart_5993066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 7, 2, 2]
def baseStart_5993103 : Nat := 118140960795 + 5993103 * 2 ^ 59
def prefixEnd_5993103 : Nat := 4983230072969 + 3 ^ 40 * 5993103 * 2
def baseEnd_5993103 : Nat := 3077342450902570690650727

theorem tailTrace_5993103 : CollatzResearch.WordTrace tailWord_5993103 prefixEnd_5993103 3077342450902570690650727 := by
  unfold tailWord_5993103
  simp only [CollatzResearch.WordTrace]
  refine ⟨218586424007018846349287963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145724282671345897566191975 218586424007018846349287963)
  ·
    refine ⟨327879636010528269523931945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218586424007018846349287963 327879636010528269523931945)
    ·
      refine ⟨245909727007896202142948959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327879636010528269523931945 245909727007896202142948959)
      ·
        refine ⟨368864590511844303214423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245909727007896202142948959 368864590511844303214423439)
        ·
          refine ⟨553296885767766454821635159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368864590511844303214423439 553296885767766454821635159)
          ·
            refine ⟨829945328651649682232452739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553296885767766454821635159 829945328651649682232452739)
            ·
              refine ⟨1244917992977474523348679109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829945328651649682232452739 1244917992977474523348679109)
              ·
                refine ⟨233422123683276473127877333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1244917992977474523348679109 233422123683276473127877333)
                ·
                  refine ⟨5470831023826792338934625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233422123683276473127877333 5470831023826792338934625)
                  ·
                    refine ⟨4103123267870094254200969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470831023826792338934625 4103123267870094254200969)
                    ·
                      refine ⟨3077342450902570690650727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103123267870094254200969 3077342450902570690650727)
                      ·
                        rfl

theorem cell23_5993103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2, 2].length) (baseStart_5993103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993103 prefixEnd_5993103 := by exact prefixLift 5993103
  have htrace : WordTrace (prefixWord ++ tailWord_5993103) baseStart_5993103 baseEnd_5993103 := by
    simpa [prefixWord, tailWord_5993103, baseEnd_5993103] using wordTrace_append hprefix tailTrace_5993103
  have hstable : (prefixWord ++ tailWord_5993103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993103).length < 2 ^ (prefixWord ++ tailWord_5993103).sum := by decide
  have hdescent : baseEnd_5993103 < baseStart_5993103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993120 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_5993120 : Nat := 118140960795 + 5993120 * 2 ^ 59
def prefixEnd_5993120 : Nat := 4983230072969 + 3 ^ 40 * 5993120 * 2
def baseEnd_5993120 : Nat := 3077351180073697124138149

theorem tailTrace_5993120 : CollatzResearch.WordTrace tailWord_5993120 prefixEnd_5993120 3077351180073697124138149 := by
  unfold tailWord_5993120
  simp only [CollatzResearch.WordTrace]
  refine ⟨109293522023978629126328407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145724696031971505501771209 109293522023978629126328407)
  ·
    refine ⟨163940283035967943689492611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109293522023978629126328407 163940283035967943689492611)
    ·
      refine ⟨245910424553951915534238917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163940283035967943689492611 245910424553951915534238917)
      ·
        refine ⟨46108204603865984162669797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245910424553951915534238917 46108204603865984162669797)
        ·
          refine ⟨8645288363224872030500587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46108204603865984162669797 8645288363224872030500587)
          ·
            refine ⟨12967932544837308045750881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645288363224872030500587 12967932544837308045750881)
            ·
              refine ⟨9725949408627981034313161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12967932544837308045750881 9725949408627981034313161)
              ·
                refine ⟨7294462056470985775734871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9725949408627981034313161 7294462056470985775734871)
                ·
                  refine ⟨10941693084706478663602307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294462056470985775734871 10941693084706478663602307)
                  ·
                    refine ⟨16412539627059717995403461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10941693084706478663602307 16412539627059717995403461)
                    ·
                      refine ⟨3077351180073697124138149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16412539627059717995403461 3077351180073697124138149)
                      ·
                        rfl

theorem cell23_5993120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_5993120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993120 prefixEnd_5993120 := by exact prefixLift 5993120
  have htrace : WordTrace (prefixWord ++ tailWord_5993120) baseStart_5993120 baseEnd_5993120 := by
    simpa [prefixWord, tailWord_5993120, baseEnd_5993120] using wordTrace_append hprefix tailTrace_5993120
  have hstable : (prefixWord ++ tailWord_5993120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993120).length < 2 ^ (prefixWord ++ tailWord_5993120).sum := by decide
  have hdescent : baseEnd_5993120 < baseStart_5993120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993136 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_5993136 : Nat := 118140960795 + 5993136 * 2 ^ 59
def prefixEnd_5993136 : Nat := 4983230072969 + 3 ^ 40 * 5993136 * 2
def baseEnd_5993136 : Nat := 3077359395764169061538075

theorem tailTrace_5993136 : CollatzResearch.WordTrace tailWord_5993136 prefixEnd_5993136 3077359395764169061538075 := by
  unfold tailWord_5993136
  simp only [CollatzResearch.WordTrace]
  refine ⟨109293813807949646492619631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145725085077266195323492841 109293813807949646492619631)
  ·
    refine ⟨163940720711924469738929447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109293813807949646492619631 163940720711924469738929447)
    ·
      refine ⟨245911081067886704608394171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163940720711924469738929447 245911081067886704608394171)
      ·
        refine ⟨368866621601830056912591257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245911081067886704608394171 368866621601830056912591257)
        ·
          refine ⟨276649966201372542684443443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368866621601830056912591257 276649966201372542684443443)
          ·
            refine ⟨414974949302058814026665165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276649966201372542684443443 414974949302058814026665165)
            ·
              refine ⟨155615605988272055259999437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414974949302058814026665165 155615605988272055259999437)
              ·
                refine ⟨58355852245602020722499789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155615605988272055259999437 58355852245602020722499789)
                ·
                  refine ⟨21883444592100757770937421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58355852245602020722499789 21883444592100757770937421)
                  ·
                    refine ⟨8206291722037784164101533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21883444592100757770937421 8206291722037784164101533)
                    ·
                      refine ⟨3077359395764169061538075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206291722037784164101533 3077359395764169061538075)
                      ·
                        rfl

theorem cell23_5993136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_5993136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993136 prefixEnd_5993136 := by exact prefixLift 5993136
  have htrace : WordTrace (prefixWord ++ tailWord_5993136) baseStart_5993136 baseEnd_5993136 := by
    simpa [prefixWord, tailWord_5993136, baseEnd_5993136] using wordTrace_append hprefix tailTrace_5993136
  have hstable : (prefixWord ++ tailWord_5993136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993136).length < 2 ^ (prefixWord ++ tailWord_5993136).sum := by decide
  have hdescent : baseEnd_5993136 < baseStart_5993136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993143 : List Nat := [1, 1, 3, 1, 7, 1, 9]
def baseStart_5993143 : Nat := 118140960795 + 5993143 * 2 ^ 59
def prefixEnd_5993143 : Nat := 4983230072969 + 3 ^ 40 * 5993143 * 2
def baseEnd_5993143 : Nat := 37992135680601858446303

theorem tailTrace_5993143 : CollatzResearch.WordTrace tailWord_5993143 prefixEnd_5993143 37992135680601858446303 := by
  unfold tailWord_5993143
  simp only [CollatzResearch.WordTrace]
  refine ⟨218587882926873933180744083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145725255284582622120496055 218587882926873933180744083)
  ·
    refine ⟨327881824390310899771116125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218587882926873933180744083 327881824390310899771116125)
    ·
      refine ⟨122955684146366587414168547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327881824390310899771116125 122955684146366587414168547)
      ·
        refine ⟨184433526219549881121252821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122955684146366587414168547 184433526219549881121252821)
        ·
          refine ⟨4322660770770700338779363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184433526219549881121252821 4322660770770700338779363)
          ·
            refine ⟨6483991156156050508169045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322660770770700338779363 6483991156156050508169045)
            ·
              refine ⟨37992135680601858446303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6483991156156050508169045 37992135680601858446303)
              ·
                rfl

theorem cell23_5993143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 9].length) (baseStart_5993143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993143 prefixEnd_5993143 := by exact prefixLift 5993143
  have htrace : WordTrace (prefixWord ++ tailWord_5993143) baseStart_5993143 baseEnd_5993143 := by
    simpa [prefixWord, tailWord_5993143, baseEnd_5993143] using wordTrace_append hprefix tailTrace_5993143
  have hstable : (prefixWord ++ tailWord_5993143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993143).length < 2 ^ (prefixWord ++ tailWord_5993143).sum := by decide
  have hdescent : baseEnd_5993143 < baseStart_5993143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993193 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 4, 2]
def baseStart_5993193 : Nat := 118140960795 + 5993193 * 2 ^ 59
def prefixEnd_5993193 : Nat := 4983230072969 + 3 ^ 40 * 5993193 * 2
def baseEnd_5993193 : Nat := 3077388664161475338525313

theorem tailTrace_5993193 : CollatzResearch.WordTrace tailWord_5993193 prefixEnd_5993193 3077388664161475338525313 := by
  unfold tailWord_5993193
  simp only [CollatzResearch.WordTrace]
  refine ⟨218589706576692791720064233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145726471051128527813376155 218589706576692791720064233)
  ·
    refine ⟨163942279932519593790048175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218589706576692791720064233 163942279932519593790048175)
    ·
      refine ⟨245913419898779390685072263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163942279932519593790048175 245913419898779390685072263)
      ·
        refine ⟨368870129848169086027608395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245913419898779390685072263 368870129848169086027608395)
        ·
          refine ⟨553305194772253629041412593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368870129848169086027608395 553305194772253629041412593)
          ·
            refine ⟨414978896079190221781059445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553305194772253629041412593 414978896079190221781059445)
            ·
              refine ⟨38904271507424083291974323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414978896079190221781059445 38904271507424083291974323)
              ·
                refine ⟨58356407261136124937961485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38904271507424083291974323 58356407261136124937961485)
                ·
                  refine ⟨21883652722926046851735557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58356407261136124937961485 21883652722926046851735557)
                  ·
                    refine ⟨4103184885548633784700417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21883652722926046851735557 4103184885548633784700417)
                    ·
                      refine ⟨3077388664161475338525313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103184885548633784700417 3077388664161475338525313)
                      ·
                        rfl

theorem cell23_5993193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4, 2].length) (baseStart_5993193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993193 prefixEnd_5993193 := by exact prefixLift 5993193
  have htrace : WordTrace (prefixWord ++ tailWord_5993193) baseStart_5993193 baseEnd_5993193 := by
    simpa [prefixWord, tailWord_5993193, baseEnd_5993193] using wordTrace_append hprefix tailTrace_5993193
  have hstable : (prefixWord ++ tailWord_5993193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993193).length < 2 ^ (prefixWord ++ tailWord_5993193).sum := by decide
  have hdescent : baseEnd_5993193 < baseStart_5993193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993210 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_5993210 : Nat := 118140960795 + 5993210 * 2 ^ 59
def prefixEnd_5993210 : Nat := 4983230072969 + 3 ^ 40 * 5993210 * 2
def baseEnd_5993210 : Nat := 3077397393332601772012735

theorem tailTrace_5993210 : CollatzResearch.WordTrace tailWord_5993210 prefixEnd_5993210 3077397393332601772012735 := by
  unfold tailWord_5993210
  simp only [CollatzResearch.WordTrace]
  refine ⟨54647581654407800905858271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145726884411754135748955389 54647581654407800905858271)
  ·
    refine ⟨81971372481611701358787407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54647581654407800905858271 81971372481611701358787407)
    ·
      refine ⟨122957058722417552038181111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81971372481611701358787407 122957058722417552038181111)
      ·
        refine ⟨184435588083626328057271667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122957058722417552038181111 184435588083626328057271667)
        ·
          refine ⟨276653382125439492085907501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184435588083626328057271667 276653382125439492085907501)
          ·
            refine ⟨103745018297039809532215313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276653382125439492085907501 103745018297039809532215313)
            ·
              refine ⟨77808763722779857149161485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103745018297039809532215313 77808763722779857149161485)
              ·
                refine ⟨29178286396042446430935557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77808763722779857149161485 29178286396042446430935557)
                ·
                  refine ⟨5470928699257958705800417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29178286396042446430935557 5470928699257958705800417)
                  ·
                    refine ⟨4103196524443469029350313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470928699257958705800417 4103196524443469029350313)
                    ·
                      refine ⟨3077397393332601772012735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103196524443469029350313 3077397393332601772012735)
                      ·
                        rfl

theorem cell23_5993210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_5993210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993210 prefixEnd_5993210 := by exact prefixLift 5993210
  have htrace : WordTrace (prefixWord ++ tailWord_5993210) baseStart_5993210 baseEnd_5993210 := by
    simpa [prefixWord, tailWord_5993210, baseEnd_5993210] using wordTrace_append hprefix tailTrace_5993210
  have hstable : (prefixWord ++ tailWord_5993210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993210).length < 2 ^ (prefixWord ++ tailWord_5993210).sum := by decide
  have hdescent : baseEnd_5993210 < baseStart_5993210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993223 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5993223 : Nat := 118140960795 + 5993223 * 2 ^ 59
def prefixEnd_5993223 : Nat := 4983230072969 + 3 ^ 40 * 5993223 * 2
def baseEnd_5993223 : Nat := 3077404068581110221150175

theorem tailTrace_5993223 : CollatzResearch.WordTrace tailWord_5993223 prefixEnd_5993223 3077404068581110221150175 := by
  unfold tailWord_5993223
  simp only [CollatzResearch.WordTrace]
  refine ⟨218590800766584106843656323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145727200511056071229104215 218590800766584106843656323)
  ·
    refine ⟨327886201149876160265484485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218590800766584106843656323 327886201149876160265484485)
    ·
      refine ⟨61478662715601780049778341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327886201149876160265484485 61478662715601780049778341)
      ·
        refine ⟨11527249259175333759333439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61478662715601780049778341 11527249259175333759333439)
        ·
          refine ⟨17290873888763000639000159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11527249259175333759333439 17290873888763000639000159)
          ·
            refine ⟨25936310833144500958500239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17290873888763000639000159 25936310833144500958500239)
            ·
              refine ⟨38904466249716751437750359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25936310833144500958500239 38904466249716751437750359)
              ·
                refine ⟨58356699374575127156625539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38904466249716751437750359 58356699374575127156625539)
                ·
                  refine ⟨87535049061862690734938309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58356699374575127156625539 87535049061862690734938309)
                  ·
                    refine ⟨16412821699099254512800933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87535049061862690734938309 16412821699099254512800933)
                    ·
                      refine ⟨3077404068581110221150175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16412821699099254512800933 3077404068581110221150175)
                      ·
                        rfl

theorem cell23_5993223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5993223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993223 prefixEnd_5993223 := by exact prefixLift 5993223
  have htrace : WordTrace (prefixWord ++ tailWord_5993223) baseStart_5993223 baseEnd_5993223 := by
    simpa [prefixWord, tailWord_5993223, baseEnd_5993223] using wordTrace_append hprefix tailTrace_5993223
  have hstable : (prefixWord ++ tailWord_5993223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993223).length < 2 ^ (prefixWord ++ tailWord_5993223).sum := by decide
  have hdescent : baseEnd_5993223 < baseStart_5993223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993250 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_5993250 : Nat := 118140960795 + 5993250 * 2 ^ 59
def prefixEnd_5993250 : Nat := 4983230072969 + 3 ^ 40 * 5993250 * 2
def baseEnd_5993250 : Nat := 341935325839864623945839

theorem tailTrace_5993250 : CollatzResearch.WordTrace tailWord_5993250 prefixEnd_5993250 341935325839864623945839 := by
  unfold tailWord_5993250
  simp only [CollatzResearch.WordTrace]
  refine ⟨54647946384371572613722301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145727857024990860303259469 54647946384371572613722301)
  ·
    refine ⟨20492979894139339730145863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54647946384371572613722301 20492979894139339730145863)
    ·
      refine ⟨30739469841209009595218795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20492979894139339730145863 30739469841209009595218795)
      ·
        refine ⟨46109204761813514392828193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30739469841209009595218795 46109204761813514392828193)
        ·
          refine ⟨34581903571360135794621145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46109204761813514392828193 34581903571360135794621145)
          ·
            refine ⟨25936427678520101845965859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34581903571360135794621145 25936427678520101845965859)
            ·
              refine ⟨38904641517780152768948789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25936427678520101845965859 38904641517780152768948789)
              ·
                refine ⟨3647310142291889322088949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38904641517780152768948789 3647310142291889322088949)
                ·
                  refine ⟨341935325839864623945839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647310142291889322088949 341935325839864623945839)
                  ·
                    rfl

theorem cell23_5993250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_5993250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993250 prefixEnd_5993250 := by exact prefixLift 5993250
  have htrace : WordTrace (prefixWord ++ tailWord_5993250) baseStart_5993250 baseEnd_5993250 := by
    simpa [prefixWord, tailWord_5993250, baseEnd_5993250] using wordTrace_append hprefix tailTrace_5993250
  have hstable : (prefixWord ++ tailWord_5993250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993250).length < 2 ^ (prefixWord ++ tailWord_5993250).sum := by decide
  have hdescent : baseEnd_5993250 < baseStart_5993250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993261 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5993261 : Nat := 118140960795 + 5993261 * 2 ^ 59
def prefixEnd_5993261 : Nat := 4983230072969 + 3 ^ 40 * 5993261 * 2
def baseEnd_5993261 : Nat := 3077423580845981072475001

theorem tailTrace_5993261 : CollatzResearch.WordTrace tailWord_5993261 prefixEnd_5993261 3077423580845981072475001 := by
  unfold tailWord_5993261
  simp only [CollatzResearch.WordTrace]
  refine ⟨218592186740446439333539637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145728124493630959555693091 218592186740446439333539637)
  ·
    refine ⟨20493017506916853687519341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218592186740446439333539637 20493017506916853687519341)
    ·
      refine ⟨7684881565093820132819753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20493017506916853687519341 7684881565093820132819753)
      ·
        refine ⟨5763661173820365099614815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7684881565093820132819753 5763661173820365099614815)
        ·
          refine ⟨8645491760730547649422223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763661173820365099614815 8645491760730547649422223)
          ·
            refine ⟨12968237641095821474133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645491760730547649422223 12968237641095821474133335)
            ·
              refine ⟨19452356461643732211200003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968237641095821474133335 19452356461643732211200003)
              ·
                refine ⟨29178534692465598316800005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19452356461643732211200003 29178534692465598316800005)
                ·
                  refine ⟨5470975254837299684400001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29178534692465598316800005 5470975254837299684400001)
                  ·
                    refine ⟨4103231441127974763300001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470975254837299684400001 4103231441127974763300001)
                    ·
                      refine ⟨3077423580845981072475001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103231441127974763300001 3077423580845981072475001)
                      ·
                        rfl

theorem cell23_5993261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5993261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993261 prefixEnd_5993261 := by exact prefixLift 5993261
  have htrace : WordTrace (prefixWord ++ tailWord_5993261) baseStart_5993261 baseEnd_5993261 := by
    simpa [prefixWord, tailWord_5993261, baseEnd_5993261] using wordTrace_append hprefix tailTrace_5993261
  have hstable : (prefixWord ++ tailWord_5993261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993261).length < 2 ^ (prefixWord ++ tailWord_5993261).sum := by decide
  have hdescent : baseEnd_5993261 < baseStart_5993261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993320 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5993320 : Nat := 118140960795 + 5993320 * 2 ^ 59
def prefixEnd_5993320 : Nat := 4983230072969 + 3 ^ 40 * 5993320 * 2
def baseEnd_5993320 : Nat := 3077453876204596341637229

theorem tailTrace_5993320 : CollatzResearch.WordTrace tailWord_5993320 prefixEnd_5993320 3077453876204596341637229 := by
  unfold tailWord_5993320
  simp only [CollatzResearch.WordTrace]
  refine ⟨109297169323616346204968707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145729559098155128273291609 109297169323616346204968707)
  ·
    refine ⟨163945753985424519307453061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109297169323616346204968707 163945753985424519307453061)
    ·
      refine ⟨30739828872267097370147449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163945753985424519307453061 30739828872267097370147449)
      ·
        refine ⟨23054871654200323027610587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30739828872267097370147449 23054871654200323027610587)
        ·
          refine ⟨34582307481300484541415881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23054871654200323027610587 34582307481300484541415881)
          ·
            refine ⟨25936730610975363406061911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34582307481300484541415881 25936730610975363406061911)
            ·
              refine ⟨38905095916463045109092867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25936730610975363406061911 38905095916463045109092867)
              ·
                refine ⟨58357643874694567663639301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38905095916463045109092867 58357643874694567663639301)
                ·
                  refine ⟨10942058226505231436932369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58357643874694567663639301 10942058226505231436932369)
                  ·
                    refine ⟨8206543669878923577699277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10942058226505231436932369 8206543669878923577699277)
                    ·
                      refine ⟨3077453876204596341637229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206543669878923577699277 3077453876204596341637229)
                      ·
                        rfl

theorem cell23_5993320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5993320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993320 prefixEnd_5993320 := by exact prefixLift 5993320
  have htrace : WordTrace (prefixWord ++ tailWord_5993320) baseStart_5993320 baseEnd_5993320 := by
    simpa [prefixWord, tailWord_5993320, baseEnd_5993320] using wordTrace_append hprefix tailTrace_5993320
  have hstable : (prefixWord ++ tailWord_5993320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993320).length < 2 ^ (prefixWord ++ tailWord_5993320).sum := by decide
  have hdescent : baseEnd_5993320 < baseStart_5993320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993400 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_5993400 : Nat := 118140960795 + 5993400 * 2 ^ 59
def prefixEnd_5993400 : Nat := 4983230072969 + 3 ^ 40 * 5993400 * 2
def baseEnd_5993400 : Nat := 1025831651552318676212287

theorem tailTrace_5993400 : CollatzResearch.WordTrace tailWord_5993400 prefixEnd_5993400 1025831651552318676212287 := by
  unfold tailWord_5993400
  simp only [CollatzResearch.WordTrace]
  refine ⟨109298628243471433036424827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145731504324628577381899769 109298628243471433036424827)
  ·
    refine ⟨163947942365207149554637241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109298628243471433036424827 163947942365207149554637241)
    ·
      refine ⟨122960956773905362165977931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163947942365207149554637241 122960956773905362165977931)
      ·
        refine ⟨184441435160858043248966897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122960956773905362165977931 184441435160858043248966897)
        ·
          refine ⟨138331076370643532436725173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184441435160858043248966897 138331076370643532436725173)
          ·
            refine ⟨12968538409747831165942985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138331076370643532436725173 12968538409747831165942985)
            ·
              refine ⟨9726403807310873374457239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12968538409747831165942985 9726403807310873374457239)
              ·
                refine ⟨14589605710966310061685859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726403807310873374457239 14589605710966310061685859)
                ·
                  refine ⟨21884408566449465092528789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14589605710966310061685859 21884408566449465092528789)
                  ·
                    refine ⟨1025831651552318676212287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21884408566449465092528789 1025831651552318676212287)
                    ·
                      rfl

theorem cell23_5993400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_5993400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993400 prefixEnd_5993400 := by exact prefixLift 5993400
  have htrace : WordTrace (prefixWord ++ tailWord_5993400) baseStart_5993400 baseEnd_5993400 := by
    simpa [prefixWord, tailWord_5993400, baseEnd_5993400] using wordTrace_append hprefix tailTrace_5993400
  have hstable : (prefixWord ++ tailWord_5993400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993400).length < 2 ^ (prefixWord ++ tailWord_5993400).sum := by decide
  have hdescent : baseEnd_5993400 < baseStart_5993400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993420 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5993420 : Nat := 118140960795 + 5993420 * 2 ^ 59
def prefixEnd_5993420 : Nat := 4983230072969 + 3 ^ 40 * 5993420 * 2
def baseEnd_5993420 : Nat := 3077505224270045950386769

theorem tailTrace_5993420 : CollatzResearch.WordTrace tailWord_5993420 prefixEnd_5993420 3077505224270045950386769 := by
  unfold tailWord_5993420
  simp only [CollatzResearch.WordTrace]
  refine ⟨109298992973435204744288857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145731990631246939659051809 109298992973435204744288857)
  ·
    refine ⟨81974244730076403558216643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109298992973435204744288857 81974244730076403558216643)
    ·
      refine ⟨122961367095114605337324965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81974244730076403558216643 122961367095114605337324965)
      ·
        refine ⟨23055256330333988500748431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122961367095114605337324965 23055256330333988500748431)
        ·
          refine ⟨34582884495500982751122647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23055256330333988500748431 34582884495500982751122647)
          ·
            refine ⟨51874326743251474126683971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34582884495500982751122647 51874326743251474126683971)
            ·
              refine ⟨77811490114877211190025957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51874326743251474126683971 77811490114877211190025957)
              ·
                refine ⟨14589654396539477098129867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77811490114877211190025957 14589654396539477098129867)
                ·
                  refine ⟨21884481594809215647194801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14589654396539477098129867 21884481594809215647194801)
                  ·
                    refine ⟨16413361196106911735396101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21884481594809215647194801 16413361196106911735396101)
                    ·
                      refine ⟨3077505224270045950386769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16413361196106911735396101 3077505224270045950386769)
                      ·
                        rfl

theorem cell23_5993420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5993420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993420 prefixEnd_5993420 := by exact prefixLift 5993420
  have htrace : WordTrace (prefixWord ++ tailWord_5993420) baseStart_5993420 baseEnd_5993420 := by
    simpa [prefixWord, tailWord_5993420, baseEnd_5993420] using wordTrace_append hprefix tailTrace_5993420
  have hstable : (prefixWord ++ tailWord_5993420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993420).length < 2 ^ (prefixWord ++ tailWord_5993420).sum := by decide
  have hdescent : baseEnd_5993420 < baseStart_5993420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993434 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_5993434 : Nat := 118140960795 + 5993434 * 2 ^ 59
def prefixEnd_5993434 : Nat := 4983230072969 + 3 ^ 40 * 5993434 * 2
def baseEnd_5993434 : Nat := 1025837470999736298537235

theorem tailTrace_5993434 : CollatzResearch.WordTrace tailWord_5993434 prefixEnd_5993434 1025837470999736298537235 := by
  unfold tailWord_5993434
  simp only [CollatzResearch.WordTrace]
  refine ⟨54649624142204922469896839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145732331045879793253058237 54649624142204922469896839)
  ·
    refine ⟨81974436213307383704845259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54649624142204922469896839 81974436213307383704845259)
    ·
      refine ⟨122961654319961075557267889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81974436213307383704845259 122961654319961075557267889)
      ·
        refine ⟨92221240739970806667950917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122961654319961075557267889 92221240739970806667950917)
        ·
          refine ⟨17291482638744526250240797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92221240739970806667950917 17291482638744526250240797)
          ·
            refine ⟨6484305989529197343840299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17291482638744526250240797 6484305989529197343840299)
            ·
              refine ⟨9726458984293796015760449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484305989529197343840299 9726458984293796015760449)
              ·
                refine ⟨7294844238220347011820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9726458984293796015760449 7294844238220347011820337)
                ·
                  refine ⟨5471133178665260258865253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294844238220347011820337 5471133178665260258865253)
                  ·
                    refine ⟨1025837470999736298537235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471133178665260258865253 1025837470999736298537235)
                    ·
                      rfl

theorem cell23_5993434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_5993434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993434 prefixEnd_5993434 := by exact prefixLift 5993434
  have htrace : WordTrace (prefixWord ++ tailWord_5993434) baseStart_5993434 baseEnd_5993434 := by
    simpa [prefixWord, tailWord_5993434, baseEnd_5993434] using wordTrace_append hprefix tailTrace_5993434
  have hstable : (prefixWord ++ tailWord_5993434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993434).length < 2 ^ (prefixWord ++ tailWord_5993434).sum := by decide
  have hdescent : baseEnd_5993434 < baseStart_5993434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993454 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_5993454 : Nat := 118140960795 + 5993454 * 2 ^ 59
def prefixEnd_5993454 : Nat := 4983230072969 + 3 ^ 40 * 5993454 * 2
def baseEnd_5993454 : Nat := 3077522682612298817361613

theorem tailTrace_5993454 : CollatzResearch.WordTrace tailWord_5993454 prefixEnd_5993454 3077522682612298817361613 := by
  unfold tailWord_5993454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324903253593404161914427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145732817352498155530210277 27324903253593404161914427)
  ·
    refine ⟨40987354880390106242871641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324903253593404161914427 40987354880390106242871641)
    ·
      refine ⟨30740516160292579682153731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40987354880390106242871641 30740516160292579682153731)
      ·
        refine ⟨46110774240438869523230597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30740516160292579682153731 46110774240438869523230597)
        ·
          refine ⟨8645770170082288035605737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46110774240438869523230597 8645770170082288035605737)
          ·
            refine ⟨6484327627561716026704303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8645770170082288035605737 6484327627561716026704303)
            ·
              refine ⟨9726491441342574040056455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484327627561716026704303 9726491441342574040056455)
              ·
                refine ⟨14589737162013861060084683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726491441342574040056455 14589737162013861060084683)
                ·
                  refine ⟨21884605743020791590127025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14589737162013861060084683 21884605743020791590127025)
                  ·
                    refine ⟨16413454307265593692595269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21884605743020791590127025 16413454307265593692595269)
                    ·
                      refine ⟨3077522682612298817361613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16413454307265593692595269 3077522682612298817361613)
                      ·
                        rfl

theorem cell23_5993454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_5993454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993454 prefixEnd_5993454 := by exact prefixLift 5993454
  have htrace : WordTrace (prefixWord ++ tailWord_5993454) baseStart_5993454 baseEnd_5993454 := by
    simpa [prefixWord, tailWord_5993454, baseEnd_5993454] using wordTrace_append hprefix tailTrace_5993454
  have hstable : (prefixWord ++ tailWord_5993454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993454).length < 2 ^ (prefixWord ++ tailWord_5993454).sum := by decide
  have hdescent : baseEnd_5993454 < baseStart_5993454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993457 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_5993457 : Nat := 118140960795 + 5993457 * 2 ^ 59
def prefixEnd_5993457 : Nat := 4983230072969 + 3 ^ 40 * 5993457 * 2
def baseEnd_5993457 : Nat := 3077524223054262305624099

theorem tailTrace_5993457 : CollatzResearch.WordTrace tailWord_5993457 prefixEnd_5993457 3077524223054262305624099 := by
  unfold tailWord_5993457
  simp only [CollatzResearch.WordTrace]
  refine ⟨218599335447736364807674625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145732890298490909871783083 218599335447736364807674625)
  ·
    refine ⟨163949501585802273605755969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218599335447736364807674625 163949501585802273605755969)
    ·
      refine ⟨122962126189351705204316977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163949501585802273605755969 122962126189351705204316977)
      ·
        refine ⟨92221594642013778903237733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122962126189351705204316977 92221594642013778903237733)
        ·
          refine ⟨17291548995377583544357075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92221594642013778903237733 17291548995377583544357075)
          ·
            refine ⟨25937323493066375316535613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17291548995377583544357075 25937323493066375316535613)
            ·
              refine ⟨9726496309899890743700855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25937323493066375316535613 9726496309899890743700855)
              ·
                refine ⟨14589744464849836115551283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726496309899890743700855 14589744464849836115551283)
                ·
                  refine ⟨21884616697274754173326925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14589744464849836115551283 21884616697274754173326925)
                  ·
                    refine ⟨8206731261478032814997597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21884616697274754173326925 8206731261478032814997597)
                    ·
                      refine ⟨3077524223054262305624099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206731261478032814997597 3077524223054262305624099)
                      ·
                        rfl

theorem cell23_5993457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_5993457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993457 prefixEnd_5993457 := by exact prefixLift 5993457
  have htrace : WordTrace (prefixWord ++ tailWord_5993457) baseStart_5993457 baseEnd_5993457 := by
    simpa [prefixWord, tailWord_5993457, baseEnd_5993457] using wordTrace_append hprefix tailTrace_5993457
  have hstable : (prefixWord ++ tailWord_5993457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993457).length < 2 ^ (prefixWord ++ tailWord_5993457).sum := by decide
  have hdescent : baseEnd_5993457 < baseStart_5993457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993484 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_5993484 : Nat := 118140960795 + 5993484 * 2 ^ 59
def prefixEnd_5993484 : Nat := 4983230072969 + 3 ^ 40 * 5993484 * 2
def baseEnd_5993484 : Nat := 3077538087031933699986475

theorem tailTrace_5993484 : CollatzResearch.WordTrace tailWord_5993484 prefixEnd_5993484 3077538087031933699986475 := by
  unfold tailWord_5993484
  simp only [CollatzResearch.WordTrace]
  refine ⟨109300160109319274209453753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145733546812425698945938337 109300160109319274209453753)
  ·
    refine ⟨81975120081989455657090315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109300160109319274209453753 81975120081989455657090315)
    ·
      refine ⟨122962680122984183485635473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81975120081989455657090315 122962680122984183485635473)
      ·
        refine ⟨92222010092238137614226605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122962680122984183485635473 92222010092238137614226605)
        ·
          refine ⟨34583253784589301605334977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92222010092238137614226605 34583253784589301605334977)
          ·
            refine ⟨25937440338441976204001233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34583253784589301605334977 25937440338441976204001233)
            ·
              refine ⟨19453080253831482153000925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25937440338441976204001233 19453080253831482153000925)
              ·
                refine ⟨7294905095186805807375347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19453080253831482153000925 7294905095186805807375347)
                ·
                  refine ⟨10942357642780208711063021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294905095186805807375347 10942357642780208711063021)
                  ·
                    refine ⟨4103384116042578266648633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10942357642780208711063021 4103384116042578266648633)
                    ·
                      refine ⟨3077538087031933699986475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103384116042578266648633 3077538087031933699986475)
                      ·
                        rfl

theorem cell23_5993484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_5993484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993484 prefixEnd_5993484 := by exact prefixLift 5993484
  have htrace : WordTrace (prefixWord ++ tailWord_5993484) baseStart_5993484 baseEnd_5993484 := by
    simpa [prefixWord, tailWord_5993484, baseEnd_5993484] using wordTrace_append hprefix tailTrace_5993484
  have hstable : (prefixWord ++ tailWord_5993484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993484).length < 2 ^ (prefixWord ++ tailWord_5993484).sum := by decide
  have hdescent : baseEnd_5993484 < baseStart_5993484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993508 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5993508 : Nat := 118140960795 + 5993508 * 2 ^ 59
def prefixEnd_5993508 : Nat := 4983230072969 + 3 ^ 40 * 5993508 * 2
def baseEnd_5993508 : Nat := 3077550410567641606086365

theorem tailTrace_5993508 : CollatzResearch.WordTrace tailWord_5993508 prefixEnd_5993508 3077550410567641606086365 := by
  unfold tailWord_5993508
  simp only [CollatzResearch.WordTrace]
  refine ⟨109300597785275800258890589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145734130380367733678520785 109300597785275800258890589)
  ·
    refine ⟨40987724169478425097083971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109300597785275800258890589 40987724169478425097083971)
    ·
      refine ⟨61481586254217637645625957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40987724169478425097083971 61481586254217637645625957)
      ·
        refine ⟨11527797422665807058554867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61481586254217637645625957 11527797422665807058554867)
        ·
          refine ⟨17291696133998710587832301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11527797422665807058554867 17291696133998710587832301)
          ·
            refine ⟨6484386050249516470437113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17291696133998710587832301 6484386050249516470437113)
            ·
              refine ⟨4863289537687137352827835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484386050249516470437113 4863289537687137352827835)
              ·
                refine ⟨7294934306530706029241753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863289537687137352827835 7294934306530706029241753)
                ·
                  refine ⟨5471200729898029521931315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294934306530706029241753 5471200729898029521931315)
                  ·
                    refine ⟨8206801094847044282896973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471200729898029521931315 8206801094847044282896973)
                    ·
                      refine ⟨3077550410567641606086365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206801094847044282896973 3077550410567641606086365)
                      ·
                        rfl

theorem cell23_5993508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5993508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993508 prefixEnd_5993508 := by exact prefixLift 5993508
  have htrace : WordTrace (prefixWord ++ tailWord_5993508) baseStart_5993508 baseEnd_5993508 := by
    simpa [prefixWord, tailWord_5993508, baseEnd_5993508] using wordTrace_append hprefix tailTrace_5993508
  have hstable : (prefixWord ++ tailWord_5993508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993508).length < 2 ^ (prefixWord ++ tailWord_5993508).sum := by decide
  have hdescent : baseEnd_5993508 < baseStart_5993508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993554 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_5993554 : Nat := 118140960795 + 5993554 * 2 ^ 59
def prefixEnd_5993554 : Nat := 4983230072969 + 3 ^ 40 * 5993554 * 2
def baseEnd_5993554 : Nat := 341952670075305380679017

theorem tailTrace_5993554 : CollatzResearch.WordTrace tailWord_5993554 prefixEnd_5993554 341952670075305380679017 := by
  unfold tailWord_5993554
  simp only [CollatzResearch.WordTrace]
  refine ⟨54650718332096237593488929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145735248885589966915970477 54650718332096237593488929)
  ·
    refine ⟨40988038749072178195116697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54650718332096237593488929 40988038749072178195116697)
    ·
      refine ⟨30741029061804133646337523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40988038749072178195116697 30741029061804133646337523)
      ·
        refine ⟨46111543592706200469506285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30741029061804133646337523 46111543592706200469506285)
        ·
          refine ⟨17291828847264825176064857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46111543592706200469506285 17291828847264825176064857)
          ·
            refine ⟨12968871635448618882048643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17291828847264825176064857 12968871635448618882048643)
            ·
              refine ⟨19453307453172928323072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968871635448618882048643 19453307453172928323072965)
              ·
                refine ⟨3647495147469924060576181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19453307453172928323072965 3647495147469924060576181)
                ·
                  refine ⟨341952670075305380679017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647495147469924060576181 341952670075305380679017)
                  ·
                    rfl

theorem cell23_5993554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_5993554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993554 prefixEnd_5993554 := by exact prefixLift 5993554
  have htrace : WordTrace (prefixWord ++ tailWord_5993554) baseStart_5993554 baseEnd_5993554 := by
    simpa [prefixWord, tailWord_5993554, baseEnd_5993554] using wordTrace_append hprefix tailTrace_5993554
  have hstable : (prefixWord ++ tailWord_5993554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993554).length < 2 ^ (prefixWord ++ tailWord_5993554).sum := by decide
  have hdescent : baseEnd_5993554 < baseStart_5993554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993557 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5993557 : Nat := 118140960795 + 5993557 * 2 ^ 59
def prefixEnd_5993557 : Nat := 4983230072969 + 3 ^ 40 * 5993557 * 2
def baseEnd_5993557 : Nat := 3077575571119711914373639

theorem tailTrace_5993557 : CollatzResearch.WordTrace tailWord_5993557 prefixEnd_5993557 3077575571119711914373639 := by
  unfold tailWord_5993557
  simp only [CollatzResearch.WordTrace]
  refine ⟨218602982747374081886314925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145735321831582721257543283 218602982747374081886314925)
  ·
    refine ⟨81976118530265280707368097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218602982747374081886314925 81976118530265280707368097)
    ·
      refine ⟨61482088897698960530526073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81976118530265280707368097 61482088897698960530526073)
      ·
        refine ⟨46111566673274220397894555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61482088897698960530526073 46111566673274220397894555)
        ·
          refine ⟨69167350009911330596841833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46111566673274220397894555 69167350009911330596841833)
          ·
            refine ⟨51875512507433497947631375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69167350009911330596841833 51875512507433497947631375)
            ·
              refine ⟨77813268761150246921447063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51875512507433497947631375 77813268761150246921447063)
              ·
                refine ⟨116719903141725370382170595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77813268761150246921447063 116719903141725370382170595)
                ·
                  refine ⟨175079854712588055573255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116719903141725370382170595 175079854712588055573255893)
                  ·
                    refine ⟨4103434094826282552498185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175079854712588055573255893 4103434094826282552498185)
                    ·
                      refine ⟨3077575571119711914373639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103434094826282552498185 3077575571119711914373639)
                      ·
                        rfl

theorem cell23_5993557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5993557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993557 prefixEnd_5993557 := by exact prefixLift 5993557
  have htrace : WordTrace (prefixWord ++ tailWord_5993557) baseStart_5993557 baseEnd_5993557 := by
    simpa [prefixWord, tailWord_5993557, baseEnd_5993557] using wordTrace_append hprefix tailTrace_5993557
  have hstable : (prefixWord ++ tailWord_5993557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993557).length < 2 ^ (prefixWord ++ tailWord_5993557).sum := by decide
  have hdescent : baseEnd_5993557 < baseStart_5993557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993560 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_5993560 : Nat := 118140960795 + 5993560 * 2 ^ 59
def prefixEnd_5993560 : Nat := 4983230072969 + 3 ^ 40 * 5993560 * 2
def baseEnd_5993560 : Nat := 3077577111561675402636125

theorem tailTrace_5993560 : CollatzResearch.WordTrace tailWord_5993560 prefixEnd_5993560 3077577111561675402636125 := by
  unfold tailWord_5993560
  simp only [CollatzResearch.WordTrace]
  refine ⟨109301546083181606699337067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145735394777575475599116089 109301546083181606699337067)
  ·
    refine ⟨163952319124772410049005601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109301546083181606699337067 163952319124772410049005601)
    ·
      refine ⟨122964239343579307536754201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163952319124772410049005601 122964239343579307536754201)
      ·
        refine ⟨92223179507684480652565651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122964239343579307536754201 92223179507684480652565651)
        ·
          refine ⟨138334769261526720978848477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92223179507684480652565651 138334769261526720978848477)
          ·
            refine ⟨51875538473072520367068179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138334769261526720978848477 51875538473072520367068179)
            ·
              refine ⟨77813307709608780550602269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51875538473072520367068179 77813307709608780550602269)
              ·
                refine ⟨29179990391103292706475851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77813307709608780550602269 29179990391103292706475851)
                ·
                  refine ⟨43769985586654939059713777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29179990391103292706475851 43769985586654939059713777)
                  ·
                    refine ⟨32827489189991204294785333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43769985586654939059713777 32827489189991204294785333)
                    ·
                      refine ⟨3077577111561675402636125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32827489189991204294785333 3077577111561675402636125)
                      ·
                        rfl

theorem cell23_5993560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_5993560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993560 prefixEnd_5993560 := by exact prefixLift 5993560
  have htrace : WordTrace (prefixWord ++ tailWord_5993560) baseStart_5993560 baseEnd_5993560 := by
    simpa [prefixWord, tailWord_5993560, baseEnd_5993560] using wordTrace_append hprefix tailTrace_5993560
  have hstable : (prefixWord ++ tailWord_5993560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993560).length < 2 ^ (prefixWord ++ tailWord_5993560).sum := by decide
  have hdescent : baseEnd_5993560 < baseStart_5993560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993597 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5993597 : Nat := 118140960795 + 5993597 * 2 ^ 59
def prefixEnd_5993597 : Nat := 4983230072969 + 3 ^ 40 * 5993597 * 2
def baseEnd_5993597 : Nat := 1025865370115297252624485

theorem tailTrace_5993597 : CollatzResearch.WordTrace tailWord_5993597 prefixEnd_5993597 1025865370115297252624485 := by
  unfold tailWord_5993597
  simp only [CollatzResearch.WordTrace]
  refine ⟨218604441667229168717771045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145736294444819445811847363 218604441667229168717771045)
  ·
    refine ⟨40988332812605469134582071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218604441667229168717771045 40988332812605469134582071)
    ·
      refine ⟨61482499218908203701873107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40988332812605469134582071 61482499218908203701873107)
      ·
        refine ⟨92223748828362305552809661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61482499218908203701873107 92223748828362305552809661)
        ·
          refine ⟨34583905810635864582303623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92223748828362305552809661 34583905810635864582303623)
          ·
            refine ⟨51875858715953796873455435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34583905810635864582303623 51875858715953796873455435)
            ·
              refine ⟨77813788073930695310183153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51875858715953796873455435 77813788073930695310183153)
              ·
                refine ⟨58360341055448021482637365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77813788073930695310183153 58360341055448021482637365)
                ·
                  refine ⟨5471281973948252013997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58360341055448021482637365 5471281973948252013997253)
                  ·
                    refine ⟨1025865370115297252624485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471281973948252013997253 1025865370115297252624485)
                    ·
                      rfl

theorem cell23_5993597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5993597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993597 prefixEnd_5993597 := by exact prefixLift 5993597
  have htrace : WordTrace (prefixWord ++ tailWord_5993597) baseStart_5993597 baseEnd_5993597 := by
    simpa [prefixWord, tailWord_5993597, baseEnd_5993597] using wordTrace_append hprefix tailTrace_5993597
  have hstable : (prefixWord ++ tailWord_5993597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993597).length < 2 ^ (prefixWord ++ tailWord_5993597).sum := by decide
  have hdescent : baseEnd_5993597 < baseStart_5993597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993600 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_5993600 : Nat := 118140960795 + 5993600 * 2 ^ 59
def prefixEnd_5993600 : Nat := 4983230072969 + 3 ^ 40 * 5993600 * 2
def baseEnd_5993600 : Nat := 3077597650787855246135941

theorem tailTrace_5993600 : CollatzResearch.WordTrace tailWord_5993600 prefixEnd_5993600 3077597650787855246135941 := by
  unfold tailWord_5993600
  simp only [CollatzResearch.WordTrace]
  refine ⟨109302275543109150115065127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145736367390812200153420169 109302275543109150115065127)
  ·
    refine ⟨163953413314663725172597691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109302275543109150115065127 163953413314663725172597691)
    ·
      refine ⟨245930119971995587758896537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163953413314663725172597691 245930119971995587758896537)
      ·
        refine ⟨184447589978996690819172403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245930119971995587758896537 184447589978996690819172403)
        ·
          refine ⟨276671384968495036228758605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184447589978996690819172403 276671384968495036228758605)
          ·
            refine ⟨103751769363185638585784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276671384968495036228758605 103751769363185638585784477)
            ·
              refine ⟨38906913511194614469669179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103751769363185638585784477 38906913511194614469669179)
              ·
                refine ⟨58360370266791921704503769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38906913511194614469669179 58360370266791921704503769)
                ·
                  refine ⟨43770277700093941278377827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58360370266791921704503769 43770277700093941278377827)
                  ·
                    refine ⟨65655416550140911917566741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43770277700093941278377827 65655416550140911917566741)
                    ·
                      refine ⟨3077597650787855246135941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65655416550140911917566741 3077597650787855246135941)
                      ·
                        rfl

theorem cell23_5993600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_5993600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993600 prefixEnd_5993600 := by exact prefixLift 5993600
  have htrace : WordTrace (prefixWord ++ tailWord_5993600) baseStart_5993600 baseEnd_5993600 := by
    simpa [prefixWord, tailWord_5993600, baseEnd_5993600] using wordTrace_append hprefix tailTrace_5993600
  have hstable : (prefixWord ++ tailWord_5993600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993600).length < 2 ^ (prefixWord ++ tailWord_5993600).sum := by decide
  have hdescent : baseEnd_5993600 < baseStart_5993600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993604 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5993604 : Nat := 118140960795 + 5993604 * 2 ^ 59
def prefixEnd_5993604 : Nat := 4983230072969 + 3 ^ 40 * 5993604 * 2
def baseEnd_5993604 : Nat := 3077599704710473230485923

theorem tailTrace_5993604 : CollatzResearch.WordTrace tailWord_5993604 prefixEnd_5993604 3077599704710473230485923 := by
  unfold tailWord_5993604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109302348489101904456637933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145736464652135872608850577 109302348489101904456637933)
  ·
    refine ⟨40988380683413214171239225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109302348489101904456637933 40988380683413214171239225)
    ·
      refine ⟨30741285512559910628429419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40988380683413214171239225 30741285512559910628429419)
      ·
        refine ⟨46111928268839865942644129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30741285512559910628429419 46111928268839865942644129)
        ·
          refine ⟨34583946201629899456983097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46111928268839865942644129 34583946201629899456983097)
          ·
            refine ⟨25937959651222424592737323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34583946201629899456983097 25937959651222424592737323)
            ·
              refine ⟨38906939476833636889105985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25937959651222424592737323 38906939476833636889105985)
              ·
                refine ⟨29180204607625227666829489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38906939476833636889105985 29180204607625227666829489)
                ·
                  refine ⟨21885153455718920750122117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29180204607625227666829489 21885153455718920750122117)
                  ·
                    refine ⟨4103466272947297640647897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21885153455718920750122117 4103466272947297640647897)
                    ·
                      refine ⟨3077599704710473230485923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103466272947297640647897 3077599704710473230485923)
                      ·
                        rfl

theorem cell23_5993604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5993604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993604 prefixEnd_5993604 := by exact prefixLift 5993604
  have htrace : WordTrace (prefixWord ++ tailWord_5993604) baseStart_5993604 baseEnd_5993604 := by
    simpa [prefixWord, tailWord_5993604, baseEnd_5993604] using wordTrace_append hprefix tailTrace_5993604
  have hstable : (prefixWord ++ tailWord_5993604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993604).length < 2 ^ (prefixWord ++ tailWord_5993604).sum := by decide
  have hdescent : baseEnd_5993604 < baseStart_5993604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993607 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_5993607 : Nat := 118140960795 + 5993607 * 2 ^ 59
def prefixEnd_5993607 : Nat := 4983230072969 + 3 ^ 40 * 5993607 * 2
def baseEnd_5993607 : Nat := 3077601245152436718748409

theorem tailTrace_5993607 : CollatzResearch.WordTrace tailWord_5993607 prefixEnd_5993607 3077601245152436718748409 := by
  unfold tailWord_5993607
  simp only [CollatzResearch.WordTrace]
  refine ⟨218604806397192940425635075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145736537598128626950423383 218604806397192940425635075)
  ·
    refine ⟨327907209595789410638452613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218604806397192940425635075 327907209595789410638452613)
    ·
      refine ⟨61482601799210514494709865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327907209595789410638452613 61482601799210514494709865)
      ·
        refine ⟨46111951349407885871032399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61482601799210514494709865 46111951349407885871032399)
        ·
          refine ⟨69167927024111828806548599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46111951349407885871032399 69167927024111828806548599)
          ·
            refine ⟨103751890536167743209822899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69167927024111828806548599 103751890536167743209822899)
            ·
              refine ⟨155627835804251614814734349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103751890536167743209822899 155627835804251614814734349)
              ·
                refine ⟨58360438426594355555525381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155627835804251614814734349 58360438426594355555525381)
                ·
                  refine ⟨10942582204986441666661009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58360438426594355555525381 10942582204986441666661009)
                  ·
                    refine ⟨8206936653739831249995757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10942582204986441666661009 8206936653739831249995757)
                    ·
                      refine ⟨3077601245152436718748409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8206936653739831249995757 3077601245152436718748409)
                      ·
                        rfl

theorem cell23_5993607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_5993607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993607 prefixEnd_5993607 := by exact prefixLift 5993607
  have htrace : WordTrace (prefixWord ++ tailWord_5993607) baseStart_5993607 baseEnd_5993607 := by
    simpa [prefixWord, tailWord_5993607, baseEnd_5993607] using wordTrace_append hprefix tailTrace_5993607
  have hstable : (prefixWord ++ tailWord_5993607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993607).length < 2 ^ (prefixWord ++ tailWord_5993607).sum := by decide
  have hdescent : baseEnd_5993607 < baseStart_5993607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993614 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_5993614 : Nat := 118140960795 + 5993614 * 2 ^ 59
def prefixEnd_5993614 : Nat := 4983230072969 + 3 ^ 40 * 5993614 * 2
def baseEnd_5993614 : Nat := 1025868279839006063786959

theorem tailTrace_5993614 : CollatzResearch.WordTrace tailWord_5993614 prefixEnd_5993614 1025868279839006063786959 := by
  unfold tailWord_5993614
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325632713520947577642487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145736707805445053747426597 27325632713520947577642487)
  ·
    refine ⟨40988449070281421366463731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27325632713520947577642487 40988449070281421366463731)
    ·
      refine ⟨61482673605422132049695597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40988449070281421366463731 61482673605422132049695597)
      ·
        refine ⟨23056002602033299518635849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61482673605422132049695597 23056002602033299518635849)
        ·
          refine ⟨17292001951524974638976887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23056002602033299518635849 17292001951524974638976887)
          ·
            refine ⟨25938002927287461958465331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17292001951524974638976887 25938002927287461958465331)
            ·
              refine ⟨38907004390931192937697997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25938002927287461958465331 38907004390931192937697997)
              ·
                refine ⟨14590126646599197351636749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38907004390931192937697997 14590126646599197351636749)
                ·
                  refine ⟨5471297492474699006863781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14590126646599197351636749 5471297492474699006863781)
                  ·
                    refine ⟨1025868279839006063786959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471297492474699006863781 1025868279839006063786959)
                    ·
                      rfl

theorem cell23_5993614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_5993614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993614 prefixEnd_5993614 := by exact prefixLift 5993614
  have htrace : WordTrace (prefixWord ++ tailWord_5993614) baseStart_5993614 baseEnd_5993614 := by
    simpa [prefixWord, tailWord_5993614, baseEnd_5993614] using wordTrace_append hprefix tailTrace_5993614
  have hstable : (prefixWord ++ tailWord_5993614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993614).length < 2 ^ (prefixWord ++ tailWord_5993614).sum := by decide
  have hdescent : baseEnd_5993614 < baseStart_5993614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993665 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5993665 : Nat := 118140960795 + 5993665 * 2 ^ 59
def prefixEnd_5993665 : Nat := 4983230072969 + 3 ^ 40 * 5993665 * 2
def baseEnd_5993665 : Nat := 1025877009010132497274381

theorem tailTrace_5993665 : CollatzResearch.WordTrace tailWord_5993665 prefixEnd_5993665 1025877009010132497274381 := by
  unfold tailWord_5993665
  simp only [CollatzResearch.WordTrace]
  refine ⟨218606921830982816331246449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145737947887321877554164299 218606921830982816331246449)
  ·
    refine ⟨163955191373237112248434837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218606921830982816331246449 163955191373237112248434837)
    ·
      refine ⟨7685399595620489636645383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163955191373237112248434837 7685399595620489636645383)
      ·
        refine ⟨11528099393430734454968075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685399595620489636645383 11528099393430734454968075)
        ·
          refine ⟨17292149090146101682452113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528099393430734454968075 17292149090146101682452113)
          ·
            refine ⟨12969111817609576261839085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17292149090146101682452113 12969111817609576261839085)
            ·
              refine ⟨4863416931603591098189657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12969111817609576261839085 4863416931603591098189657)
              ·
                refine ⟨3647562698702693323642243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863416931603591098189657 3647562698702693323642243)
                ·
                  refine ⟨5471344048054039985463365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647562698702693323642243 5471344048054039985463365)
                  ·
                    refine ⟨1025877009010132497274381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471344048054039985463365 1025877009010132497274381)
                    ·
                      rfl

theorem cell23_5993665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5993665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993665 prefixEnd_5993665 := by exact prefixLift 5993665
  have htrace : WordTrace (prefixWord ++ tailWord_5993665) baseStart_5993665 baseEnd_5993665 := by
    simpa [prefixWord, tailWord_5993665, baseEnd_5993665] using wordTrace_append hprefix tailTrace_5993665
  have hstable : (prefixWord ++ tailWord_5993665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993665).length < 2 ^ (prefixWord ++ tailWord_5993665).sum := by decide
  have hdescent : baseEnd_5993665 < baseStart_5993665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_5993671 : Nat := 118140960795 + 5993671 * 2 ^ 59
def prefixEnd_5993671 : Nat := 4983230072969 + 3 ^ 40 * 5993671 * 2
def baseEnd_5993671 : Nat := 3077634107914324468348115

theorem tailTrace_5993671 : CollatzResearch.WordTrace tailWord_5993671 prefixEnd_5993671 3077634107914324468348115 := by
  unfold tailWord_5993671
  simp only [CollatzResearch.WordTrace]
  refine ⟨218607140668961079355964867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145738093779307386237309911 218607140668961079355964867)
  ·
    refine ⟨327910711003441619033947301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218607140668961079355964867 327910711003441619033947301)
    ·
      refine ⟨61483258313145303568865119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 327910711003441619033947301 61483258313145303568865119)
      ·
        refine ⟨92224887469717955353297679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61483258313145303568865119 92224887469717955353297679)
        ·
          refine ⟨138337331204576933029946519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92224887469717955353297679 138337331204576933029946519)
          ·
            refine ⟨207505996806865399544919779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138337331204576933029946519 207505996806865399544919779)
            ·
              refine ⟨311258995210298099317379669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207505996806865399544919779 311258995210298099317379669)
              ·
                refine ⟨3647566350120680851375543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 311258995210298099317379669 3647566350120680851375543)
                ·
                  refine ⟨5471349525181021277063315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647566350120680851375543 5471349525181021277063315)
                  ·
                    refine ⟨8207024287771531915594973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471349525181021277063315 8207024287771531915594973)
                    ·
                      refine ⟨3077634107914324468348115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207024287771531915594973 3077634107914324468348115)
                      ·
                        rfl

theorem cell23_5993671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_5993671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993671 prefixEnd_5993671 := by exact prefixLift 5993671
  have htrace : WordTrace (prefixWord ++ tailWord_5993671) baseStart_5993671 baseEnd_5993671 := by
    simpa [prefixWord, tailWord_5993671, baseEnd_5993671] using wordTrace_append hprefix tailTrace_5993671
  have hstable : (prefixWord ++ tailWord_5993671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993671).length < 2 ^ (prefixWord ++ tailWord_5993671).sum := by decide
  have hdescent : baseEnd_5993671 < baseStart_5993671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993678 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_5993678 : Nat := 118140960795 + 5993678 * 2 ^ 59
def prefixEnd_5993678 : Nat := 4983230072969 + 3 ^ 40 * 5993678 * 2
def baseEnd_5993678 : Nat := 341959744697656215662287

theorem tailTrace_5993678 : CollatzResearch.WordTrace tailWord_5993678 prefixEnd_5993678 341959744697656215662287 := by
  unfold tailWord_5993678
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325924497491964943933711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145738263986623813034313125 27325924497491964943933711)
  ·
    refine ⟨40988886746237947415900567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27325924497491964943933711 40988886746237947415900567)
    ·
      refine ⟨61483330119356921123850851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40988886746237947415900567 61483330119356921123850851)
      ·
        refine ⟨92224995179035381685776277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61483330119356921123850851 92224995179035381685776277)
        ·
          refine ⟨4323046649017283516520763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92224995179035381685776277 4323046649017283516520763)
          ·
            refine ⟨6484569973525925274781145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323046649017283516520763 6484569973525925274781145)
            ·
              refine ⟨4863427480144443956085859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484569973525925274781145 4863427480144443956085859)
              ·
                refine ⟨7295141220216665934128789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863427480144443956085859 7295141220216665934128789)
                ·
                  refine ⟨341959744697656215662287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7295141220216665934128789 341959744697656215662287)
                  ·
                    rfl

theorem cell23_5993678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_5993678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993678 prefixEnd_5993678 := by exact prefixLift 5993678
  have htrace : WordTrace (prefixWord ++ tailWord_5993678) baseStart_5993678 baseEnd_5993678 := by
    simpa [prefixWord, tailWord_5993678, baseEnd_5993678] using wordTrace_append hprefix tailTrace_5993678
  have hstable : (prefixWord ++ tailWord_5993678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993678).length < 2 ^ (prefixWord ++ tailWord_5993678).sum := by decide
  have hdescent : baseEnd_5993678 < baseStart_5993678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993707 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_5993707 : Nat := 118140960795 + 5993707 * 2 ^ 59
def prefixEnd_5993707 : Nat := 4983230072969 + 3 ^ 40 * 5993707 * 2
def baseEnd_5993707 : Nat := 3077652593217886327497949

theorem tailTrace_5993707 : CollatzResearch.WordTrace tailWord_5993707 prefixEnd_5993707 3077652593217886327497949 := by
  unfold tailWord_5993707
  simp only [CollatzResearch.WordTrace]
  refine ⟨218608453696830657504275375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145738969131220438336183583 218608453696830657504275375)
  ·
    refine ⟨327912680545245986256413063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218608453696830657504275375 327912680545245986256413063)
    ·
      refine ⟨491869020817868979384619595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327912680545245986256413063 491869020817868979384619595)
      ·
        refine ⟨737803531226803469076929393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491869020817868979384619595 737803531226803469076929393)
        ·
          refine ⟨553352648420102601807697045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737803531226803469076929393 553352648420102601807697045)
          ·
            refine ⟨25938405394692309459735799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 553352648420102601807697045 25938405394692309459735799)
            ·
              refine ⟨38907608092038464189603699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25938405394692309459735799 38907608092038464189603699)
              ·
                refine ⟨58361412138057696284405549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38907608092038464189603699 58361412138057696284405549)
                ·
                  refine ⟨21885529551771636106652081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58361412138057696284405549 21885529551771636106652081)
                  ·
                    refine ⟨16414147163828727079989061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21885529551771636106652081 16414147163828727079989061)
                    ·
                      refine ⟨3077652593217886327497949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16414147163828727079989061 3077652593217886327497949)
                      ·
                        rfl

theorem cell23_5993707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_5993707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993707 prefixEnd_5993707 := by exact prefixLift 5993707
  have htrace : WordTrace (prefixWord ++ tailWord_5993707) baseStart_5993707 baseEnd_5993707 := by
    simpa [prefixWord, tailWord_5993707, baseEnd_5993707] using wordTrace_append hprefix tailTrace_5993707
  have hstable : (prefixWord ++ tailWord_5993707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993707).length < 2 ^ (prefixWord ++ tailWord_5993707).sum := by decide
  have hdescent : baseEnd_5993707 < baseStart_5993707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993716 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5993716 : Nat := 118140960795 + 5993716 * 2 ^ 59
def prefixEnd_5993716 : Nat := 4983230072969 + 3 ^ 40 * 5993716 * 2
def baseEnd_5993716 : Nat := 1025885738181258930761803

theorem tailTrace_5993716 : CollatzResearch.WordTrace tailWord_5993716 prefixEnd_5993716 1025885738181258930761803 := by
  unfold tailWord_5993716
  simp only [CollatzResearch.WordTrace]
  refine ⟨109304390976899026020676501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145739187969198701360902001 109304390976899026020676501)
  ·
    refine ⟨5123643327042141844719211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109304390976899026020676501 5123643327042141844719211)
    ·
      refine ⟨7685464990563212767078817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123643327042141844719211 7685464990563212767078817)
      ·
        refine ⟨5764098742922409575309113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7685464990563212767078817 5764098742922409575309113)
        ·
          refine ⟨4323074057191807181481835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764098742922409575309113 4323074057191807181481835)
          ·
            refine ⟨6484611085787710772222753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323074057191807181481835 6484611085787710772222753)
            ·
              refine ⟨4863458314340783079167065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484611085787710772222753 4863458314340783079167065)
              ·
                refine ⟨3647593735755587309375299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863458314340783079167065 3647593735755587309375299)
                ·
                  refine ⟨5471390603633380964062949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647593735755587309375299 5471390603633380964062949)
                  ·
                    refine ⟨1025885738181258930761803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471390603633380964062949 1025885738181258930761803)
                    ·
                      rfl

theorem cell23_5993716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5993716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993716 prefixEnd_5993716 := by exact prefixLift 5993716
  have htrace : WordTrace (prefixWord ++ tailWord_5993716) baseStart_5993716 baseEnd_5993716 := by
    simpa [prefixWord, tailWord_5993716, baseEnd_5993716] using wordTrace_append hprefix tailTrace_5993716
  have hstable : (prefixWord ++ tailWord_5993716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993716).length < 2 ^ (prefixWord ++ tailWord_5993716).sum := by decide
  have hdescent : baseEnd_5993716 < baseStart_5993716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993762 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_5993762 : Nat := 118140960795 + 5993762 * 2 ^ 59
def prefixEnd_5993762 : Nat := 4983230072969 + 3 ^ 40 * 5993762 * 2
def baseEnd_5993762 : Nat := 3077680834653883612310197

theorem tailTrace_5993762 : CollatzResearch.WordTrace tailWord_5993762 prefixEnd_5993762 3077680834653883612310197 := by
  unfold tailWord_5993762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652614927907850474381885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145740306474420934598351693 54652614927907850474381885)
  ·
    refine ⟨20494730597965443927893207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54652614927907850474381885 20494730597965443927893207)
    ·
      refine ⟨30742095896948165891839811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20494730597965443927893207 30742095896948165891839811)
      ·
        refine ⟨46113143845422248837759717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30742095896948165891839811 46113143845422248837759717)
        ·
          refine ⟨8646214471016671657079947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46113143845422248837759717 8646214471016671657079947)
          ·
            refine ⟨12969321706525007485619921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646214471016671657079947 12969321706525007485619921)
            ·
              refine ⟨9726991279893755614214941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12969321706525007485619921 9726991279893755614214941)
              ·
                refine ⟨3647621729960158355330603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9726991279893755614214941 3647621729960158355330603)
                ·
                  refine ⟨5471432594940237532995905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647621729960158355330603 5471432594940237532995905)
                  ·
                    refine ⟨4103574446205178149746929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471432594940237532995905 4103574446205178149746929)
                    ·
                      refine ⟨3077680834653883612310197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103574446205178149746929 3077680834653883612310197)
                      ·
                        rfl

theorem cell23_5993762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_5993762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993762 prefixEnd_5993762 := by exact prefixLift 5993762
  have htrace : WordTrace (prefixWord ++ tailWord_5993762) baseStart_5993762 baseEnd_5993762 := by
    simpa [prefixWord, tailWord_5993762, baseEnd_5993762] using wordTrace_append hprefix tailTrace_5993762
  have hstable : (prefixWord ++ tailWord_5993762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993762).length < 2 ^ (prefixWord ++ tailWord_5993762).sum := by decide
  have hdescent : baseEnd_5993762 < baseStart_5993762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993778 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_5993778 : Nat := 118140960795 + 5993778 * 2 ^ 59
def prefixEnd_5993778 : Nat := 4983230072969 + 3 ^ 40 * 5993778 * 2
def baseEnd_5993778 : Nat := 3077689050344355549710123

theorem tailTrace_5993778 : CollatzResearch.WordTrace tailWord_5993778 prefixEnd_5993778 3077689050344355549710123 := by
  unfold tailWord_5993778
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652760819893359157527497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145740695519715624420073325 54652760819893359157527497)
  ·
    refine ⟨40989570614920019368145623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54652760819893359157527497 40989570614920019368145623)
    ·
      refine ⟨61484355922380029052218435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40989570614920019368145623 61484355922380029052218435)
      ·
        refine ⟨92226533883570043578327653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61484355922380029052218435 92226533883570043578327653)
        ·
          refine ⟨17292475103169383170936435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92226533883570043578327653 17292475103169383170936435)
          ·
            refine ⟨25938712654754074756404653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17292475103169383170936435 25938712654754074756404653)
            ·
              refine ⟨9727017245532778033651745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25938712654754074756404653 9727017245532778033651745)
              ·
                refine ⟨7295262934149583525238809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727017245532778033651745 7295262934149583525238809)
                ·
                  refine ⟨5471447200612187643929107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295262934149583525238809 5471447200612187643929107)
                  ·
                    refine ⟨8207170800918281465893661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471447200612187643929107 8207170800918281465893661)
                    ·
                      refine ⟨3077689050344355549710123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207170800918281465893661 3077689050344355549710123)
                      ·
                        rfl

theorem cell23_5993778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_5993778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993778 prefixEnd_5993778 := by exact prefixLift 5993778
  have htrace : WordTrace (prefixWord ++ tailWord_5993778) baseStart_5993778 baseEnd_5993778 := by
    simpa [prefixWord, tailWord_5993778, baseEnd_5993778] using wordTrace_append hprefix tailTrace_5993778
  have hstable : (prefixWord ++ tailWord_5993778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993778).length < 2 ^ (prefixWord ++ tailWord_5993778).sum := by decide
  have hdescent : baseEnd_5993778 < baseStart_5993778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993801 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 4, 2]
def baseStart_5993801 : Nat := 118140960795 + 5993801 * 2 ^ 59
def prefixEnd_5993801 : Nat := 4983230072969 + 3 ^ 40 * 5993801 * 2
def baseEnd_5993801 : Nat := 3077700860399408959722517

theorem tailTrace_5993801 : CollatzResearch.WordTrace tailWord_5993801 prefixEnd_5993801 3077700860399408959722517 := by
  unfold tailWord_5993801
  simp only [CollatzResearch.WordTrace]
  refine ⟨218611882158490111558197257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145741254772326741038798171 218611882158490111558197257)
  ·
    refine ⟨163958911618867583668647943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218611882158490111558197257 163958911618867583668647943)
    ·
      refine ⟨245938367428301375502971915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163958911618867583668647943 245938367428301375502971915)
      ·
        refine ⟨368907551142452063254457873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245938367428301375502971915 368907551142452063254457873)
        ·
          refine ⟨276680663356839047440843405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368907551142452063254457873 276680663356839047440843405)
          ·
            refine ⟨103755248758814642790316277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276680663356839047440843405 103755248758814642790316277)
            ·
              refine ⟨9727054571138872761592151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103755248758814642790316277 9727054571138872761592151)
              ·
                refine ⟨14590581856708309142388227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727054571138872761592151 14590581856708309142388227)
                ·
                  refine ⟨21885872785062463713582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14590581856708309142388227 21885872785062463713582341)
                  ·
                    refine ⟨4103601147199211946296689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21885872785062463713582341 4103601147199211946296689)
                    ·
                      refine ⟨3077700860399408959722517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103601147199211946296689 3077700860399408959722517)
                      ·
                        rfl

theorem cell23_5993801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4, 2].length) (baseStart_5993801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993801 prefixEnd_5993801 := by exact prefixLift 5993801
  have htrace : WordTrace (prefixWord ++ tailWord_5993801) baseStart_5993801 baseEnd_5993801 := by
    simpa [prefixWord, tailWord_5993801, baseEnd_5993801] using wordTrace_append hprefix tailTrace_5993801
  have hstable : (prefixWord ++ tailWord_5993801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993801).length < 2 ^ (prefixWord ++ tailWord_5993801).sum := by decide
  have hdescent : baseEnd_5993801 < baseStart_5993801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993891 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 4, 2]
def baseStart_5993891 : Nat := 118140960795 + 5993891 * 2 ^ 59
def prefixEnd_5993891 : Nat := 4983230072969 + 3 ^ 40 * 5993891 * 2
def baseEnd_5993891 : Nat := 3077747073658313607597103

theorem tailTrace_5993891 : CollatzResearch.WordTrace tailWord_5993891 prefixEnd_5993891 3077747073658313607597103 := by
  unfold tailWord_5993891
  simp only [CollatzResearch.WordTrace]
  refine ⟨218615164728164056928973527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145743443152109371285982351 218615164728164056928973527)
  ·
    refine ⟨327922747092246085393460291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218615164728164056928973527 327922747092246085393460291)
    ·
      refine ⟨491884120638369128090190437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327922747092246085393460291 491884120638369128090190437)
      ·
        refine ⟨92228272619694211516910707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 491884120638369128090190437 92228272619694211516910707)
        ·
          refine ⟨138342408929541317275366061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92228272619694211516910707 138342408929541317275366061)
          ·
            refine ⟨51878403348577993978262273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138342408929541317275366061 51878403348577993978262273)
            ·
              refine ⟨38908802511433495483696705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51878403348577993978262273 38908802511433495483696705)
              ·
                refine ⟨29181601883575121612772529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38908802511433495483696705 29181601883575121612772529)
                ·
                  refine ⟨21886201412681341209579397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29181601883575121612772529 21886201412681341209579397)
                  ·
                    refine ⟨4103662764877751476796137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21886201412681341209579397 4103662764877751476796137)
                    ·
                      refine ⟨3077747073658313607597103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103662764877751476796137 3077747073658313607597103)
                      ·
                        rfl

theorem cell23_5993891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_5993891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993891 prefixEnd_5993891 := by exact prefixLift 5993891
  have htrace : WordTrace (prefixWord ++ tailWord_5993891) baseStart_5993891 baseEnd_5993891 := by
    simpa [prefixWord, tailWord_5993891, baseEnd_5993891] using wordTrace_append hprefix tailTrace_5993891
  have hstable : (prefixWord ++ tailWord_5993891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993891).length < 2 ^ (prefixWord ++ tailWord_5993891).sum := by decide
  have hdescent : baseEnd_5993891 < baseStart_5993891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993922 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5993922 : Nat := 118140960795 + 5993922 * 2 ^ 59
def prefixEnd_5993922 : Nat := 4983230072969 + 3 ^ 40 * 5993922 * 2
def baseEnd_5993922 : Nat := 1025920997186200995436487

theorem tailTrace_5993922 : CollatzResearch.WordTrace tailWord_5993922 prefixEnd_5993922 1025920997186200995436487 := by
  unfold tailWord_5993922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54654073847762937305838005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145744196927367832815568013 54654073847762937305838005)
  ·
    refine ⟨5123819423227775372422313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54654073847762937305838005 5123819423227775372422313)
    ·
      refine ⟨3842864567420831529316735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5123819423227775372422313 3842864567420831529316735)
      ·
        refine ⟨5764296851131247293975103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842864567420831529316735 5764296851131247293975103)
        ·
          refine ⟨8646445276696870940962655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764296851131247293975103 8646445276696870940962655)
          ·
            refine ⟨12969667915045306411443983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646445276696870940962655 12969667915045306411443983)
            ·
              refine ⟨19454501872567959617165975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12969667915045306411443983 19454501872567959617165975)
              ·
                refine ⟨29181752808851939425748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19454501872567959617165975 29181752808851939425748963)
                ·
                  refine ⟨43772629213277909138623445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29181752808851939425748963 43772629213277909138623445)
                  ·
                    refine ⟨1025920997186200995436487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43772629213277909138623445 1025920997186200995436487)
                    ·
                      rfl

theorem cell23_5993922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5993922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993922 prefixEnd_5993922 := by exact prefixLift 5993922
  have htrace : WordTrace (prefixWord ++ tailWord_5993922) baseStart_5993922 baseEnd_5993922 := by
    simpa [prefixWord, tailWord_5993922, baseEnd_5993922] using wordTrace_append hprefix tailTrace_5993922
  have hstable : (prefixWord ++ tailWord_5993922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993922).length < 2 ^ (prefixWord ++ tailWord_5993922).sum := by decide
  have hdescent : baseEnd_5993922 < baseStart_5993922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993964 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_5993964 : Nat := 118140960795 + 5993964 * 2 ^ 59
def prefixEnd_5993964 : Nat := 4983230072969 + 3 ^ 40 * 5993964 * 2
def baseEnd_5993964 : Nat := 3077784557746091821984267

theorem tailTrace_5993964 : CollatzResearch.WordTrace tailWord_5993964 prefixEnd_5993964 3077784557746091821984267 := by
  unfold tailWord_5993964
  simp only [CollatzResearch.WordTrace]
  refine ⟨109308913628449795198190473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145745218171266393597587297 109308913628449795198190473)
  ·
    refine ⟨81981685221337346398642855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109308913628449795198190473 81981685221337346398642855)
    ·
      refine ⟨122972527832006019597964283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81981685221337346398642855 122972527832006019597964283)
      ·
        refine ⟨184458791748009029396946425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122972527832006019597964283 184458791748009029396946425)
        ·
          refine ⟨138344093811006772047709819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184458791748009029396946425 138344093811006772047709819)
          ·
            refine ⟨207516140716510158071564729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138344093811006772047709819 207516140716510158071564729)
            ·
              refine ⟨155637105537382618553673547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207516140716510158071564729 155637105537382618553673547)
              ·
                refine ⟨233455658306073927830510321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155637105537382618553673547 233455658306073927830510321)
                ·
                  refine ⟨175091743729555445872882741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233455658306073927830510321 175091743729555445872882741)
                  ·
                    refine ⟨16414850974645823050582757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175091743729555445872882741 16414850974645823050582757)
                    ·
                      refine ⟨3077784557746091821984267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16414850974645823050582757 3077784557746091821984267)
                      ·
                        rfl

theorem cell23_5993964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_5993964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993964 prefixEnd_5993964 := by exact prefixLift 5993964
  have htrace : WordTrace (prefixWord ++ tailWord_5993964) baseStart_5993964 baseEnd_5993964 := by
    simpa [prefixWord, tailWord_5993964, baseEnd_5993964] using wordTrace_append hprefix tailTrace_5993964
  have hstable : (prefixWord ++ tailWord_5993964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993964).length < 2 ^ (prefixWord ++ tailWord_5993964).sum := by decide
  have hdescent : baseEnd_5993964 < baseStart_5993964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5993965 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5993965 : Nat := 118140960795 + 5993965 * 2 ^ 59
def prefixEnd_5993965 : Nat := 4983230072969 + 3 ^ 40 * 5993965 * 2
def baseEnd_5993965 : Nat := 341976119025194035341307

theorem tailTrace_5993965 : CollatzResearch.WordTrace tailWord_5993965 prefixEnd_5993965 341976119025194035341307 := by
  unfold tailWord_5993965
  simp only [CollatzResearch.WordTrace]
  refine ⟨218617863729895967567167349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145745242486597311711444899 218617863729895967567167349)
  ·
    refine ⟨20495424724677746959421939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218617863729895967567167349 20495424724677746959421939)
    ·
      refine ⟨30743137087016620439132909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20495424724677746959421939 30743137087016620439132909)
      ·
        refine ⟨11528676407631232664674841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30743137087016620439132909 11528676407631232664674841)
        ·
          refine ⟨8646507305723424498506131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11528676407631232664674841 8646507305723424498506131)
          ·
            refine ⟨12969760958585136747759197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646507305723424498506131 12969760958585136747759197)
            ·
              refine ⟨4863660359469426280409699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12969760958585136747759197 4863660359469426280409699)
              ·
                refine ⟨7295490539204139420614549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863660359469426280409699 7295490539204139420614549)
                ·
                  refine ⟨341976119025194035341307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7295490539204139420614549 341976119025194035341307)
                  ·
                    rfl

theorem cell23_5993965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5993965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5993965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5993965 prefixEnd_5993965 := by exact prefixLift 5993965
  have htrace : WordTrace (prefixWord ++ tailWord_5993965) baseStart_5993965 baseEnd_5993965 := by
    simpa [prefixWord, tailWord_5993965, baseEnd_5993965] using wordTrace_append hprefix tailTrace_5993965
  have hstable : (prefixWord ++ tailWord_5993965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5993965).length < 2 ^ (prefixWord ++ tailWord_5993965).sum := by decide
  have hdescent : baseEnd_5993965 < baseStart_5993965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5993965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994001 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_5994001 : Nat := 118140960795 + 5994001 * 2 ^ 59
def prefixEnd_5994001 : Nat := 4983230072969 + 3 ^ 40 * 5994001 * 2
def baseEnd_5994001 : Nat := 3077803556530308177221597

theorem tailTrace_5994001 : CollatzResearch.WordTrace tailWord_5994001 prefixEnd_5994001 3077803556530308177221597 := by
  unfold tailWord_5994001
  simp only [CollatzResearch.WordTrace]
  refine ⟨218619176757765545715477857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145746117838510363810318571 218619176757765545715477857)
  ·
    refine ⟨163964382568324159286608393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218619176757765545715477857 163964382568324159286608393)
    ·
      refine ⟨122973286926243119464956295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163964382568324159286608393 122973286926243119464956295)
      ·
        refine ⟨184459930389364679197434443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122973286926243119464956295 184459930389364679197434443)
        ·
          refine ⟨276689895584047018796151665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184459930389364679197434443 276689895584047018796151665)
          ·
            refine ⟨207517421688035264097113749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276689895584047018796151665 207517421688035264097113749)
            ·
              refine ⟨9727379141626653004552207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207517421688035264097113749 9727379141626653004552207)
              ·
                refine ⟨14591068712439979506828311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727379141626653004552207 14591068712439979506828311)
                ·
                  refine ⟨21886603068659969260242467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14591068712439979506828311 21886603068659969260242467)
                  ·
                    refine ⟨32829904602989953890363701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21886603068659969260242467 32829904602989953890363701)
                    ·
                      refine ⟨3077803556530308177221597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32829904602989953890363701 3077803556530308177221597)
                      ·
                        rfl

theorem cell23_5994001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_5994001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994001 prefixEnd_5994001 := by exact prefixLift 5994001
  have htrace : WordTrace (prefixWord ++ tailWord_5994001) baseStart_5994001 baseEnd_5994001 := by
    simpa [prefixWord, tailWord_5994001, baseEnd_5994001] using wordTrace_append hprefix tailTrace_5994001
  have hstable : (prefixWord ++ tailWord_5994001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994001).length < 2 ^ (prefixWord ++ tailWord_5994001).sum := by decide
  have hdescent : baseEnd_5994001 < baseStart_5994001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994015 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 3, 2, 2]
def baseStart_5994015 : Nat := 118140960795 + 5994015 * 2 ^ 59
def prefixEnd_5994015 : Nat := 4983230072969 + 3 ^ 40 * 5994015 * 2
def baseEnd_5994015 : Nat := 3077810745259471122446533

theorem tailTrace_5994015 : CollatzResearch.WordTrace tailWord_5994015 prefixEnd_5994015 3077810745259471122446533 := by
  unfold tailWord_5994015
  simp only [CollatzResearch.WordTrace]
  refine ⟨218619687379714826106487499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145746458253143217404324999 218619687379714826106487499)
  ·
    refine ⟨327929531069572239159731249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218619687379714826106487499 327929531069572239159731249)
    ·
      refine ⟨245947148302179179369798437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327929531069572239159731249 245947148302179179369798437)
      ·
        refine ⟨46115090306658596131837207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245947148302179179369798437 46115090306658596131837207)
        ·
          refine ⟨69172635459987894197755811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46115090306658596131837207 69172635459987894197755811)
          ·
            refine ⟨103758953189981841296633717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69172635459987894197755811 103758953189981841296633717)
            ·
              refine ⟨9727401861560797621559411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103758953189981841296633717 9727401861560797621559411)
              ·
                refine ⟨14591102792341196432339117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727401861560797621559411 14591102792341196432339117)
                ·
                  refine ⟨5471663547127948662127169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14591102792341196432339117 5471663547127948662127169)
                  ·
                    refine ⟨4103747660345961496595377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471663547127948662127169 4103747660345961496595377)
                    ·
                      refine ⟨3077810745259471122446533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103747660345961496595377 3077810745259471122446533)
                      ·
                        rfl

theorem cell23_5994015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_5994015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994015 prefixEnd_5994015 := by exact prefixLift 5994015
  have htrace : WordTrace (prefixWord ++ tailWord_5994015) baseStart_5994015 baseEnd_5994015 := by
    simpa [prefixWord, tailWord_5994015, baseEnd_5994015] using wordTrace_append hprefix tailTrace_5994015
  have hstable : (prefixWord ++ tailWord_5994015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994015).length < 2 ^ (prefixWord ++ tailWord_5994015).sum := by decide
  have hdescent : baseEnd_5994015 < baseStart_5994015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994035 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 3]
def baseStart_5994035 : Nat := 118140960795 + 5994035 * 2 ^ 59
def prefixEnd_5994035 : Nat := 4983230072969 + 3 ^ 40 * 5994035 * 2
def baseEnd_5994035 : Nat := 3077821014872561044196441

theorem tailTrace_5994035 : CollatzResearch.WordTrace tailWord_5994035 prefixEnd_5994035 3077821014872561044196441 := by
  unfold tailWord_5994035
  simp only [CollatzResearch.WordTrace]
  refine ⟨218620416839642369522215559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145746944559761579681477039 218620416839642369522215559)
  ·
    refine ⟨327930625259463554283323339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218620416839642369522215559 327930625259463554283323339)
    ·
      refine ⟨491895937889195331424985009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327930625259463554283323339 491895937889195331424985009)
      ·
        refine ⟨368921953416896498568738757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491895937889195331424985009 368921953416896498568738757)
        ·
          refine ⟨69172866265668093481638517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368921953416896498568738757 69172866265668093481638517)
          ·
            refine ⟨6484956212406383763903611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69172866265668093481638517 6484956212406383763903611)
            ·
              refine ⟨9727434318609575645855417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484956212406383763903611 9727434318609575645855417)
              ·
                refine ⟨7295575738957181734391563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727434318609575645855417 7295575738957181734391563)
                ·
                  refine ⟨10943363608435772601587345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295575738957181734391563 10943363608435772601587345)
                  ·
                    refine ⟨8207522706326829451190509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10943363608435772601587345 8207522706326829451190509)
                    ·
                      refine ⟨3077821014872561044196441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207522706326829451190509 3077821014872561044196441)
                      ·
                        rfl

theorem cell23_5994035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_5994035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994035 prefixEnd_5994035 := by exact prefixLift 5994035
  have htrace : WordTrace (prefixWord ++ tailWord_5994035) baseStart_5994035 baseEnd_5994035 := by
    simpa [prefixWord, tailWord_5994035, baseEnd_5994035] using wordTrace_append hprefix tailTrace_5994035
  have hstable : (prefixWord ++ tailWord_5994035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994035).length < 2 ^ (prefixWord ++ tailWord_5994035).sum := by decide
  have hdescent : baseEnd_5994035 < baseStart_5994035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994065 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_5994065 : Nat := 118140960795 + 5994065 * 2 ^ 59
def prefixEnd_5994065 : Nat := 4983230072969 + 3 ^ 40 * 5994065 * 2
def baseEnd_5994065 : Nat := 3077836419292195926821303

theorem tailTrace_5994065 : CollatzResearch.WordTrace tailWord_5994065 prefixEnd_5994065 3077836419292195926821303 := by
  unfold tailWord_5994065
  simp only [CollatzResearch.WordTrace]
  refine ⟨218621511029533684645807649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145747674019689123097205099 218621511029533684645807649)
  ·
    refine ⟨163966133272150263484355737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218621511029533684645807649 163966133272150263484355737)
    ·
      refine ⟨122974599954112697613266803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163966133272150263484355737 122974599954112697613266803)
      ·
        refine ⟨184461899931169046419900205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122974599954112697613266803 184461899931169046419900205)
        ·
          refine ⟨69173212474188392407462577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184461899931169046419900205 69173212474188392407462577)
          ·
            refine ⟨51879909355641294305596933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69173212474188392407462577 51879909355641294305596933)
            ·
              refine ⟨9727483004182742682299425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51879909355641294305596933 9727483004182742682299425)
              ·
                refine ⟨7295612253137057011724569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727483004182742682299425 7295612253137057011724569)
                ·
                  refine ⟨5471709189852792758793427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295612253137057011724569 5471709189852792758793427)
                  ·
                    refine ⟨8207563784779189138190141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471709189852792758793427 8207563784779189138190141)
                    ·
                      refine ⟨3077836419292195926821303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207563784779189138190141 3077836419292195926821303)
                      ·
                        rfl

theorem cell23_5994065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_5994065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994065 prefixEnd_5994065 := by exact prefixLift 5994065
  have htrace : WordTrace (prefixWord ++ tailWord_5994065) baseStart_5994065 baseEnd_5994065 := by
    simpa [prefixWord, tailWord_5994065, baseEnd_5994065] using wordTrace_append hprefix tailTrace_5994065
  have hstable : (prefixWord ++ tailWord_5994065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994065).length < 2 ^ (prefixWord ++ tailWord_5994065).sum := by decide
  have hdescent : baseEnd_5994065 < baseStart_5994065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994066 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_5994066 : Nat := 118140960795 + 5994066 * 2 ^ 59
def prefixEnd_5994066 : Nat := 4983230072969 + 3 ^ 40 * 5994066 * 2
def baseEnd_5994066 : Nat := 3077836932772850422908799

theorem tailTrace_5994066 : CollatzResearch.WordTrace tailWord_5994066 prefixEnd_5994066 3077836932772850422908799 := by
  unfold tailWord_5994066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54655386875632515454148513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145747698335020041211062701 54655386875632515454148513)
  ·
    refine ⟨40991540156724386590611385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54655386875632515454148513 40991540156724386590611385)
    ·
      refine ⟨30743655117543289942958539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40991540156724386590611385 30743655117543289942958539)
      ·
        refine ⟨46115482676314934914437809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30743655117543289942958539 46115482676314934914437809)
        ·
          refine ⟨34586612007236201185828357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46115482676314934914437809 34586612007236201185828357)
          ·
            refine ⟨6484989751356787722342817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34586612007236201185828357 6484989751356787722342817)
            ·
              refine ⟨4863742313517590791757113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484989751356787722342817 4863742313517590791757113)
              ·
                refine ⟨3647806735138193093817835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863742313517590791757113 3647806735138193093817835)
                ·
                  refine ⟨5471710102707289640726753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647806735138193093817835 5471710102707289640726753)
                  ·
                    refine ⟨4103782577030467230545065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471710102707289640726753 4103782577030467230545065)
                    ·
                      refine ⟨3077836932772850422908799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103782577030467230545065 3077836932772850422908799)
                      ·
                        rfl

theorem cell23_5994066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_5994066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994066 prefixEnd_5994066 := by exact prefixLift 5994066
  have htrace : WordTrace (prefixWord ++ tailWord_5994066) baseStart_5994066 baseEnd_5994066 := by
    simpa [prefixWord, tailWord_5994066, baseEnd_5994066] using wordTrace_append hprefix tailTrace_5994066
  have hstable : (prefixWord ++ tailWord_5994066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994066).length < 2 ^ (prefixWord ++ tailWord_5994066).sum := by decide
  have hdescent : baseEnd_5994066 < baseStart_5994066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994071 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_5994071 : Nat := 118140960795 + 5994071 * 2 ^ 59
def prefixEnd_5994071 : Nat := 4983230072969 + 3 ^ 40 * 5994071 * 2
def baseEnd_5994071 : Nat := 3077839500176122903346275

theorem tailTrace_5994071 : CollatzResearch.WordTrace tailWord_5994071 prefixEnd_5994071 3077839500176122903346275 := by
  unfold tailWord_5994071
  simp only [CollatzResearch.WordTrace]
  refine ⟨218621729867511947670526067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145747819911674631780350711 218621729867511947670526067)
  ·
    refine ⟨327932594801267921505789101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218621729867511947670526067 327932594801267921505789101)
    ·
      refine ⟨122974723050475470564670913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327932594801267921505789101 122974723050475470564670913)
      ·
        refine ⟨92231042287856602923503185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122974723050475470564670913 92231042287856602923503185)
        ·
          refine ⟨69173281715892452192627389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92231042287856602923503185 69173281715892452192627389)
          ·
            refine ⟨25939980643459669572235271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69173281715892452192627389 25939980643459669572235271)
            ·
              refine ⟨38909970965189504358352907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25939980643459669572235271 38909970965189504358352907)
              ·
                refine ⟨58364956447784256537529361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38909970965189504358352907 58364956447784256537529361)
                ·
                  refine ⟨43773717335838192403147021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58364956447784256537529361 43773717335838192403147021)
                  ·
                    refine ⟨16415144000939322151180133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43773717335838192403147021 16415144000939322151180133)
                    ·
                      refine ⟨3077839500176122903346275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16415144000939322151180133 3077839500176122903346275)
                      ·
                        rfl

theorem cell23_5994071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_5994071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994071 prefixEnd_5994071 := by exact prefixLift 5994071
  have htrace : WordTrace (prefixWord ++ tailWord_5994071) baseStart_5994071 baseEnd_5994071 := by
    simpa [prefixWord, tailWord_5994071, baseEnd_5994071] using wordTrace_append hprefix tailTrace_5994071
  have hstable : (prefixWord ++ tailWord_5994071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994071).length < 2 ^ (prefixWord ++ tailWord_5994071).sum := by decide
  have hdescent : baseEnd_5994071 < baseStart_5994071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994081 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_5994081 : Nat := 118140960795 + 5994081 * 2 ^ 59
def prefixEnd_5994081 : Nat := 4983230072969 + 3 ^ 40 * 5994081 * 2
def baseEnd_5994081 : Nat := 1025948211660889288073743

theorem tailTrace_5994081 : CollatzResearch.WordTrace tailWord_5994081 prefixEnd_5994081 1025948211660889288073743 := by
  unfold tailWord_5994081
  simp only [CollatzResearch.WordTrace]
  refine ⟨218622094597475719378390097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145748063064983812918926731 218622094597475719378390097)
  ·
    refine ⟨163966570948106789533792573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218622094597475719378390097 163966570948106789533792573)
    ·
      refine ⟨61487464105540046075172215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163966570948106789533792573 61487464105540046075172215)
      ·
        refine ⟨92231196158310069112758323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61487464105540046075172215 92231196158310069112758323)
        ·
          refine ⟨138346794237465103669137485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92231196158310069112758323 138346794237465103669137485)
          ·
            refine ⟨51880047839049413875926557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138346794237465103669137485 51880047839049413875926557)
            ·
              refine ⟨19455017939643530203472459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51880047839049413875926557 19455017939643530203472459)
              ·
                refine ⟨29182526909465295305208689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19455017939643530203472459 29182526909465295305208689)
                ·
                  refine ⟨21886895182098971478906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29182526909465295305208689 21886895182098971478906517)
                  ·
                    refine ⟨1025948211660889288073743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21886895182098971478906517 1025948211660889288073743)
                    ·
                      rfl

theorem cell23_5994081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_5994081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994081 prefixEnd_5994081 := by exact prefixLift 5994081
  have htrace : WordTrace (prefixWord ++ tailWord_5994081) baseStart_5994081 baseEnd_5994081 := by
    simpa [prefixWord, tailWord_5994081, baseEnd_5994081] using wordTrace_append hprefix tailTrace_5994081
  have hstable : (prefixWord ++ tailWord_5994081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994081).length < 2 ^ (prefixWord ++ tailWord_5994081).sum := by decide
  have hdescent : baseEnd_5994081 < baseStart_5994081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994105 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 4, 2, 2]
def baseStart_5994105 : Nat := 118140960795 + 5994105 * 2 ^ 59
def prefixEnd_5994105 : Nat := 4983230072969 + 3 ^ 40 * 5994105 * 2
def baseEnd_5994105 : Nat := 3077856958518375770321119

theorem tailTrace_5994105 : CollatzResearch.WordTrace tailWord_5994105 prefixEnd_5994105 3077856958518375770321119 := by
  unfold tailWord_5994105
  simp only [CollatzResearch.WordTrace]
  refine ⟨218622969949388771477263769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145748646632925847651509179 218622969949388771477263769)
  ·
    refine ⟨163967227462041578607947827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218622969949388771477263769 163967227462041578607947827)
    ·
      refine ⟨245950841193062367911921741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163967227462041578607947827 245950841193062367911921741)
      ·
        refine ⟨92231565447398387966970653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245950841193062367911921741 92231565447398387966970653)
        ·
          refine ⟨34586837042774395487613995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92231565447398387966970653 34586837042774395487613995)
          ·
            refine ⟨51880255564161593231420993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34586837042774395487613995 51880255564161593231420993)
            ·
              refine ⟨38910191673121194923565745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51880255564161593231420993 38910191673121194923565745)
              ·
                refine ⟨29182643754840896192674309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38910191673121194923565745 29182643754840896192674309)
                ·
                  refine ⟨5471745704032668036126433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29182643754840896192674309 5471745704032668036126433)
                  ·
                    refine ⟨4103809278024501027094825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471745704032668036126433 4103809278024501027094825)
                    ·
                      refine ⟨3077856958518375770321119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103809278024501027094825 3077856958518375770321119)
                      ·
                        rfl

theorem cell23_5994105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_5994105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994105 prefixEnd_5994105 := by exact prefixLift 5994105
  have htrace : WordTrace (prefixWord ++ tailWord_5994105) baseStart_5994105 baseEnd_5994105 := by
    simpa [prefixWord, tailWord_5994105, baseEnd_5994105] using wordTrace_append hprefix tailTrace_5994105
  have hstable : (prefixWord ++ tailWord_5994105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994105).length < 2 ^ (prefixWord ++ tailWord_5994105).sum := by decide
  have hdescent : baseEnd_5994105 < baseStart_5994105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994109 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_5994109 : Nat := 118140960795 + 5994109 * 2 ^ 59
def prefixEnd_5994109 : Nat := 4983230072969 + 3 ^ 40 * 5994109 * 2
def baseEnd_5994109 : Nat := 3077859012440993754671101

theorem tailTrace_5994109 : CollatzResearch.WordTrace tailWord_5994109 prefixEnd_5994109 3077859012440993754671101 := by
  unfold tailWord_5994109
  simp only [CollatzResearch.WordTrace]
  refine ⟨218623115841374280160409381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145748743894249520106939587 218623115841374280160409381)
  ·
    refine ⟨40991834220257677530076759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218623115841374280160409381 40991834220257677530076759)
    ·
      refine ⟨61487751330386516295115139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40991834220257677530076759 61487751330386516295115139)
      ·
        refine ⟨92231626995579774442672709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61487751330386516295115139 92231626995579774442672709)
        ·
          refine ⟨17293430061671207708001133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92231626995579774442672709 17293430061671207708001133)
          ·
            refine ⟨6485036273126702890500425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17293430061671207708001133 6485036273126702890500425)
            ·
              refine ⟨4863777204845027167875319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485036273126702890500425 4863777204845027167875319)
              ·
                refine ⟨7295665807267540751812979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863777204845027167875319 7295665807267540751812979)
                ·
                  refine ⟨10943498710901311127719469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295665807267540751812979 10943498710901311127719469)
                  ·
                    refine ⟨4103812016587991672894801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10943498710901311127719469 4103812016587991672894801)
                    ·
                      refine ⟨3077859012440993754671101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103812016587991672894801 3077859012440993754671101)
                      ·
                        rfl

theorem cell23_5994109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_5994109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994109 prefixEnd_5994109 := by exact prefixLift 5994109
  have htrace : WordTrace (prefixWord ++ tailWord_5994109) baseStart_5994109 baseEnd_5994109 := by
    simpa [prefixWord, tailWord_5994109, baseEnd_5994109] using wordTrace_append hprefix tailTrace_5994109
  have hstable : (prefixWord ++ tailWord_5994109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994109).length < 2 ^ (prefixWord ++ tailWord_5994109).sum := by decide
  have hdescent : baseEnd_5994109 < baseStart_5994109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994122 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5994122 : Nat := 118140960795 + 5994122 * 2 ^ 59
def prefixEnd_5994122 : Nat := 4983230072969 + 3 ^ 40 * 5994122 * 2
def baseEnd_5994122 : Nat := 3077865687689502203808541

theorem tailTrace_5994122 : CollatzResearch.WordTrace tailWord_5994122 prefixEnd_5994122 3077865687689502203808541 := by
  unfold tailWord_5994122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54655897497581795845158155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145749059993551455587088413 54655897497581795845158155)
  ·
    refine ⟨81983846246372693767737233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54655897497581795845158155 81983846246372693767737233)
    ·
      refine ⟨61487884684779520325802925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81983846246372693767737233 61487884684779520325802925)
      ·
        refine ⟨23057956756792320122176097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61487884684779520325802925 23057956756792320122176097)
        ·
          refine ⟨17293467567594240091632073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23057956756792320122176097 17293467567594240091632073)
          ·
            refine ⟨12970100675695680068724055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17293467567594240091632073 12970100675695680068724055)
            ·
              refine ⟨19455151013543520103086083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12970100675695680068724055 19455151013543520103086083)
              ·
                refine ⟨29182726520315280154629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19455151013543520103086083 29182726520315280154629125)
                ·
                  refine ⟨5471761222559115028992961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29182726520315280154629125 5471761222559115028992961)
                  ·
                    refine ⟨4103820916919336271744721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471761222559115028992961 4103820916919336271744721)
                    ·
                      refine ⟨3077865687689502203808541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103820916919336271744721 3077865687689502203808541)
                      ·
                        rfl

theorem cell23_5994122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5994122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994122 prefixEnd_5994122 := by exact prefixLift 5994122
  have htrace : WordTrace (prefixWord ++ tailWord_5994122) baseStart_5994122 baseEnd_5994122 := by
    simpa [prefixWord, tailWord_5994122, baseEnd_5994122] using wordTrace_append hprefix tailTrace_5994122
  have hstable : (prefixWord ++ tailWord_5994122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994122).length < 2 ^ (prefixWord ++ tailWord_5994122).sum := by decide
  have hdescent : baseEnd_5994122 < baseStart_5994122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994181 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_5994181 : Nat := 118140960795 + 5994181 * 2 ^ 59
def prefixEnd_5994181 : Nat := 4983230072969 + 3 ^ 40 * 5994181 * 2
def baseEnd_5994181 : Nat := 3077895983048117472970769

theorem tailTrace_5994181 : CollatzResearch.WordTrace tailWord_5994181 prefixEnd_5994181 3077895983048117472970769 := by
  unfold tailWord_5994181
  simp only [CollatzResearch.WordTrace]
  refine ⟨218625741897113436457030397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145750494598075624304686931 218625741897113436457030397)
  ·
    refine ⟨81984653211417538671386399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218625741897113436457030397 81984653211417538671386399)
    ·
      refine ⟨122976979817126308007079599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81984653211417538671386399 122976979817126308007079599)
      ·
        refine ⟨184465469725689462010619399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122976979817126308007079599 184465469725689462010619399)
        ·
          refine ⟨276698204588534193015929099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184465469725689462010619399 276698204588534193015929099)
          ·
            refine ⟨415047306882801289523893649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276698204588534193015929099 415047306882801289523893649)
            ·
              refine ⟨311285480162100967142920237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415047306882801289523893649 311285480162100967142920237)
              ·
                refine ⟨116732055060787862678595089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311285480162100967142920237 116732055060787862678595089)
                ·
                  refine ⟨87549041295590897008946317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116732055060787862678595089 87549041295590897008946317)
                  ·
                    refine ⟨32830890485846586378354869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87549041295590897008946317 32830890485846586378354869)
                    ·
                      refine ⟨3077895983048117472970769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32830890485846586378354869 3077895983048117472970769)
                      ·
                        rfl

theorem cell23_5994181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_5994181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994181 prefixEnd_5994181 := by exact prefixLift 5994181
  have htrace : WordTrace (prefixWord ++ tailWord_5994181) baseStart_5994181 baseEnd_5994181 := by
    simpa [prefixWord, tailWord_5994181, baseEnd_5994181] using wordTrace_append hprefix tailTrace_5994181
  have hstable : (prefixWord ++ tailWord_5994181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994181).length < 2 ^ (prefixWord ++ tailWord_5994181).sum := by decide
  have hdescent : baseEnd_5994181 < baseStart_5994181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994191 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_5994191 : Nat := 118140960795 + 5994191 * 2 ^ 59
def prefixEnd_5994191 : Nat := 4983230072969 + 3 ^ 40 * 5994191 * 2
def baseEnd_5994191 : Nat := 3077901117854662433845723

theorem tailTrace_5994191 : CollatzResearch.WordTrace tailWord_5994191 prefixEnd_5994191 3077901117854662433845723 := by
  unfold tailWord_5994191
  simp only [CollatzResearch.WordTrace]
  refine ⟨218626106627077208164894427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145750737751384805443262951 218626106627077208164894427)
  ·
    refine ⟨327939159940615812247341641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218626106627077208164894427 327939159940615812247341641)
    ·
      refine ⟨245954369955461859185506231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327939159940615812247341641 245954369955461859185506231)
      ·
        refine ⟨368931554933192788778259347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245954369955461859185506231 368931554933192788778259347)
        ·
          refine ⟨553397332399789183167389021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368931554933192788778259347 553397332399789183167389021)
          ·
            refine ⟨207523999649920943687770883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553397332399789183167389021 207523999649920943687770883)
            ·
              refine ⟨311285999474881415531656325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207523999649920943687770883 311285999474881415531656325)
              ·
                refine ⟨58366124901540265412185561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311285999474881415531656325 58366124901540265412185561)
                ·
                  refine ⟨43774593676155199059139171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58366124901540265412185561 43774593676155199059139171)
                  ·
                    refine ⟨65661890514232798588708757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43774593676155199059139171 65661890514232798588708757)
                    ·
                      refine ⟨3077901117854662433845723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65661890514232798588708757 3077901117854662433845723)
                      ·
                        rfl

theorem cell23_5994191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_5994191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994191 prefixEnd_5994191 := by exact prefixLift 5994191
  have htrace : WordTrace (prefixWord ++ tailWord_5994191) baseStart_5994191 baseEnd_5994191 := by
    simpa [prefixWord, tailWord_5994191, baseEnd_5994191] using wordTrace_append hprefix tailTrace_5994191
  have hstable : (prefixWord ++ tailWord_5994191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994191).length < 2 ^ (prefixWord ++ tailWord_5994191).sum := by decide
  have hdescent : baseEnd_5994191 < baseStart_5994191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994222 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_5994222 : Nat := 118140960795 + 5994222 * 2 ^ 59
def prefixEnd_5994222 : Nat := 4983230072969 + 3 ^ 40 * 5994222 * 2
def baseEnd_5994222 : Nat := 1025972345251650604186027

theorem tailTrace_5994222 : CollatzResearch.WordTrace tailWord_5994222 prefixEnd_5994222 1025972345251650604186027 := by
  unfold tailWord_5994222
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328404661245612557409115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145751491526643266972848613 27328404661245612557409115)
  ·
    refine ⟨40992606991868418836113673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27328404661245612557409115 40992606991868418836113673)
    ·
      refine ⟨30744455243901314127085255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40992606991868418836113673 30744455243901314127085255)
      ·
        refine ⟨46116682865851971190627883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30744455243901314127085255 46116682865851971190627883)
        ·
          refine ⟨69175024298777956785941825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46116682865851971190627883 69175024298777956785941825)
          ·
            refine ⟨51881268224083467589456369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69175024298777956785941825 51881268224083467589456369)
            ·
              refine ⟨38910951168062600692092277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51881268224083467589456369 38910951168062600692092277)
              ·
                refine ⟨3647901672005868814883651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38910951168062600692092277 3647901672005868814883651)
                ·
                  refine ⟨5471852508008803222325477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647901672005868814883651 5471852508008803222325477)
                  ·
                    refine ⟨1025972345251650604186027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471852508008803222325477 1025972345251650604186027)
                    ·
                      rfl

theorem cell23_5994222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_5994222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994222 prefixEnd_5994222 := by exact prefixLift 5994222
  have htrace : WordTrace (prefixWord ++ tailWord_5994222) baseStart_5994222 baseEnd_5994222 := by
    simpa [prefixWord, tailWord_5994222, baseEnd_5994222] using wordTrace_append hprefix tailTrace_5994222
  have hstable : (prefixWord ++ tailWord_5994222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994222).length < 2 ^ (prefixWord ++ tailWord_5994222).sum := by decide
  have hdescent : baseEnd_5994222 < baseStart_5994222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994248 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_5994248 : Nat := 118140960795 + 5994248 * 2 ^ 59
def prefixEnd_5994248 : Nat := 4983230072969 + 3 ^ 40 * 5994248 * 2
def baseEnd_5994248 : Nat := 1025976795417322903610987

theorem tailTrace_5994248 : CollatzResearch.WordTrace tailWord_5994248 prefixEnd_5994248 1025976795417322903610987 := by
  unfold tailWord_5994248
  simp only [CollatzResearch.WordTrace]
  refine ⟨109314092793935353449859699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145752123725247137933146265 109314092793935353449859699)
  ·
    refine ⟨163971139190903030174789549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109314092793935353449859699 163971139190903030174789549)
    ·
      refine ⟨61489177196588636315546081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163971139190903030174789549 61489177196588636315546081)
      ·
        refine ⟨46116882897441477236659561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61489177196588636315546081 46116882897441477236659561)
        ·
          refine ⟨34587662173081107927494671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46116882897441477236659561 34587662173081107927494671)
          ·
            refine ⟨51881493259621661891242007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34587662173081107927494671 51881493259621661891242007)
            ·
              refine ⟨77822239889432492836863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51881493259621661891242007 77822239889432492836863011)
              ·
                refine ⟨116733359834148739255294517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77822239889432492836863011 116733359834148739255294517)
                ·
                  refine ⟨10943752484451444305183861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116733359834148739255294517 10943752484451444305183861)
                  ·
                    refine ⟨1025976795417322903610987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10943752484451444305183861 1025976795417322903610987)
                    ·
                      rfl

theorem cell23_5994248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_5994248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994248 prefixEnd_5994248 := by exact prefixLift 5994248
  have htrace : WordTrace (prefixWord ++ tailWord_5994248) baseStart_5994248 baseEnd_5994248 := by
    simpa [prefixWord, tailWord_5994248, baseEnd_5994248] using wordTrace_append hprefix tailTrace_5994248
  have hstable : (prefixWord ++ tailWord_5994248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994248).length < 2 ^ (prefixWord ++ tailWord_5994248).sum := by decide
  have hdescent : baseEnd_5994248 < baseStart_5994248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994295 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 2, 4]
def baseStart_5994295 : Nat := 118140960795 + 5994295 * 2 ^ 59
def prefixEnd_5994295 : Nat := 4983230072969 + 3 ^ 40 * 5994295 * 2
def baseEnd_5994295 : Nat := 1025984839947576675648415

theorem tailTrace_5994295 : CollatzResearch.WordTrace tailWord_5994295 prefixEnd_5994295 1025984839947576675648415 := by
  unfold tailWord_5994295
  simp only [CollatzResearch.WordTrace]
  refine ⟨218629899818700433926680339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145753266545800289284453559 218629899818700433926680339)
  ·
    refine ⟨327944849728050650890020509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218629899818700433926680339 327944849728050650890020509)
    ·
      refine ⟨122979318648018994083757691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327944849728050650890020509 122979318648018994083757691)
      ·
        refine ⟨184468977972028491125636537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122979318648018994083757691 184468977972028491125636537)
        ·
          refine ⟨138351733479021368344227403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184468977972028491125636537 138351733479021368344227403)
          ·
            refine ⟨207527600218532052516341105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138351733479021368344227403 207527600218532052516341105)
            ·
              refine ⟨155645700163899039387255829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207527600218532052516341105 155645700163899039387255829)
              ·
                refine ⟨7295892195182767471277617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155645700163899039387255829 7295892195182767471277617)
                ·
                  refine ⟨5471919146387075603458213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295892195182767471277617 5471919146387075603458213)
                  ·
                    refine ⟨1025984839947576675648415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471919146387075603458213 1025984839947576675648415)
                    ·
                      rfl

theorem cell23_5994295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_5994295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994295 prefixEnd_5994295 := by exact prefixLift 5994295
  have htrace : WordTrace (prefixWord ++ tailWord_5994295) baseStart_5994295 baseEnd_5994295 := by
    simpa [prefixWord, tailWord_5994295, baseEnd_5994295] using wordTrace_append hprefix tailTrace_5994295
  have hstable : (prefixWord ++ tailWord_5994295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994295).length < 2 ^ (prefixWord ++ tailWord_5994295).sum := by decide
  have hdescent : baseEnd_5994295 < baseStart_5994295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994322 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_5994322 : Nat := 118140960795 + 5994322 * 2 ^ 59
def prefixEnd_5994322 : Nat := 4983230072969 + 3 ^ 40 * 5994322 * 2
def baseEnd_5994322 : Nat := 3077968383820401421307621

theorem tailTrace_5994322 : CollatzResearch.WordTrace tailWord_5994322 prefixEnd_5994322 3077968383820401421307621 := by
  unfold tailWord_5994322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657721147400654384478305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145753923059735078358608813 54657721147400654384478305)
  ·
    refine ⟨40993290860550490788358729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54657721147400654384478305 40993290860550490788358729)
    ·
      refine ⟨30744968145412868091269047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40993290860550490788358729 30744968145412868091269047)
      ·
        refine ⟨46117452218119302136903571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30744968145412868091269047 46117452218119302136903571)
        ·
          refine ⟨69176178327178953205355357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46117452218119302136903571 69176178327178953205355357)
          ·
            refine ⟨25941066872692107452008259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69176178327178953205355357 25941066872692107452008259)
            ·
              refine ⟨38911600309038161178012389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25941066872692107452008259 38911600309038161178012389)
              ·
                refine ⟨7295925057944655220877323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38911600309038161178012389 7295925057944655220877323)
                ·
                  refine ⟨10943887586916982831315985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295925057944655220877323 10943887586916982831315985)
                  ·
                    refine ⟨8207915690187737123486989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10943887586916982831315985 8207915690187737123486989)
                    ·
                      refine ⟨3077968383820401421307621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207915690187737123486989 3077968383820401421307621)
                      ·
                        rfl

theorem cell23_5994322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_5994322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994322 prefixEnd_5994322 := by exact prefixLift 5994322
  have htrace : WordTrace (prefixWord ++ tailWord_5994322) baseStart_5994322 baseEnd_5994322 := by
    simpa [prefixWord, tailWord_5994322, baseEnd_5994322] using wordTrace_append hprefix tailTrace_5994322
  have hstable : (prefixWord ++ tailWord_5994322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994322).length < 2 ^ (prefixWord ++ tailWord_5994322).sum := by decide
  have hdescent : baseEnd_5994322 < baseStart_5994322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994325 : List Nat := [1, 3, 2, 2, 2, 2, 4, 7]
def baseStart_5994325 : Nat := 118140960795 + 5994325 * 2 ^ 59
def prefixEnd_5994325 : Nat := 4983230072969 + 3 ^ 40 * 5994325 * 2
def baseEnd_5994325 : Nat := 113998886083791292947041

theorem tailTrace_5994325 : CollatzResearch.WordTrace tailWord_5994325 prefixEnd_5994325 113998886083791292947041 := by
  unfold tailWord_5994325
  simp only [CollatzResearch.WordTrace]
  refine ⟨218630994008591749050272429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145753996005727832700181619 218630994008591749050272429)
  ·
    refine ⟨81986622753221905893852161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218630994008591749050272429 81986622753221905893852161)
    ·
      refine ⟨61489967064916429420389121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81986622753221905893852161 61489967064916429420389121)
      ·
        refine ⟨46117475298687322065291841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61489967064916429420389121 46117475298687322065291841)
        ·
          refine ⟨34588106474015491548968881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46117475298687322065291841 34588106474015491548968881)
          ·
            refine ⟨25941079855511618661726661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34588106474015491548968881 25941079855511618661726661)
            ·
              refine ⟨4863952472908428499073749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25941079855511618661726661 4863952472908428499073749)
              ·
                refine ⟨113998886083791292947041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4863952472908428499073749 113998886083791292947041)
                ·
                  rfl

theorem cell23_5994325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 7].length) (baseStart_5994325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994325 prefixEnd_5994325 := by exact prefixLift 5994325
  have htrace : WordTrace (prefixWord ++ tailWord_5994325) baseStart_5994325 baseEnd_5994325 := by
    simpa [prefixWord, tailWord_5994325, baseEnd_5994325] using wordTrace_append hprefix tailTrace_5994325
  have hstable : (prefixWord ++ tailWord_5994325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994325).length < 2 ^ (prefixWord ++ tailWord_5994325).sum := by decide
  have hdescent : baseEnd_5994325 < baseStart_5994325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994336 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 1, 2, 2]
def baseStart_5994336 : Nat := 118140960795 + 5994336 * 2 ^ 59
def prefixEnd_5994336 : Nat := 4983230072969 + 3 ^ 40 * 5994336 * 2
def baseEnd_5994336 : Nat := 3077975572549564366532557

theorem tailTrace_5994336 : CollatzResearch.WordTrace tailWord_5994336 prefixEnd_5994336 3077975572549564366532557 := by
  unfold tailWord_5994336
  simp only [CollatzResearch.WordTrace]
  refine ⟨109315697605775948964461431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145754263474367931952615241 109315697605775948964461431)
  ·
    refine ⟨163973546408663923446692147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109315697605775948964461431 163973546408663923446692147)
    ·
      refine ⟨245960319612995885170038221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163973546408663923446692147 245960319612995885170038221)
      ·
        refine ⟨92235119854873456938764333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245960319612995885170038221 92235119854873456938764333)
        ·
          refine ⟨34588169945577546352036625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92235119854873456938764333 34588169945577546352036625)
          ·
            refine ⟨25941127459183159764027469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34588169945577546352036625 25941127459183159764027469)
            ·
              refine ⟨9727922797193684911510301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25941127459183159764027469 9727922797193684911510301)
              ·
                refine ⟨3647971048947631841816363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9727922797193684911510301 3647971048947631841816363)
                ·
                  refine ⟨5471956573421447762724545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647971048947631841816363 5471956573421447762724545)
                  ·
                    refine ⟨4103967430066085822043409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471956573421447762724545 4103967430066085822043409)
                    ·
                      refine ⟨3077975572549564366532557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4103967430066085822043409 3077975572549564366532557)
                      ·
                        rfl

theorem cell23_5994336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_5994336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994336 prefixEnd_5994336 := by exact prefixLift 5994336
  have htrace : WordTrace (prefixWord ++ tailWord_5994336) baseStart_5994336 baseEnd_5994336 := by
    simpa [prefixWord, tailWord_5994336, baseEnd_5994336] using wordTrace_append hprefix tailTrace_5994336
  have hstable : (prefixWord ++ tailWord_5994336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994336).length < 2 ^ (prefixWord ++ tailWord_5994336).sum := by decide
  have hdescent : baseEnd_5994336 < baseStart_5994336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994352 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_5994352 : Nat := 118140960795 + 5994352 * 2 ^ 59
def prefixEnd_5994352 : Nat := 4983230072969 + 3 ^ 40 * 5994352 * 2
def baseEnd_5994352 : Nat := 3077983788240036303932483

theorem tailTrace_5994352 : CollatzResearch.WordTrace tailWord_5994352 prefixEnd_5994352 3077983788240036303932483 := by
  unfold tailWord_5994352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109315989389746966330752655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145754652519662621774336873 109315989389746966330752655)
  ·
    refine ⟨163973984084620449496128983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109315989389746966330752655 163973984084620449496128983)
    ·
      refine ⟨245960976126930674244193475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163973984084620449496128983 245960976126930674244193475)
      ·
        refine ⟨368941464190396011366290213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245960976126930674244193475 368941464190396011366290213)
        ·
          refine ⟨69176524535699252131179415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368941464190396011366290213 69176524535699252131179415)
          ·
            refine ⟨103764786803548878196769123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69176524535699252131179415 103764786803548878196769123)
            ·
              refine ⟨155647180205323317295153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103764786803548878196769123 155647180205323317295153685)
              ·
                refine ⟨7295961572124530498210329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155647180205323317295153685 7295961572124530498210329)
                ·
                  refine ⟨5471971179093397873657747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295961572124530498210329 5471971179093397873657747)
                  ·
                    refine ⟨8207956768640096810486621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471971179093397873657747 8207956768640096810486621)
                    ·
                      refine ⟨3077983788240036303932483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207956768640096810486621 3077983788240036303932483)
                      ·
                        rfl

theorem cell23_5994352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_5994352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994352 prefixEnd_5994352 := by exact prefixLift 5994352
  have htrace : WordTrace (prefixWord ++ tailWord_5994352) baseStart_5994352 baseEnd_5994352 := by
    simpa [prefixWord, tailWord_5994352, baseEnd_5994352] using wordTrace_append hprefix tailTrace_5994352
  have hstable : (prefixWord ++ tailWord_5994352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994352).length < 2 ^ (prefixWord ++ tailWord_5994352).sum := by decide
  have hdescent : baseEnd_5994352 < baseStart_5994352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994368 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_5994368 : Nat := 118140960795 + 5994368 * 2 ^ 59
def prefixEnd_5994368 : Nat := 4983230072969 + 3 ^ 40 * 5994368 * 2
def baseEnd_5994368 : Nat := 1025997334643502747110803

theorem tailTrace_5994368 : CollatzResearch.WordTrace tailWord_5994368 prefixEnd_5994368 1025997334643502747110803 := by
  unfold tailWord_5994368
  simp only [CollatzResearch.WordTrace]
  refine ⟨109316281173717983697043879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145755041564957311596058505 109316281173717983697043879)
  ·
    refine ⟨163974421760576975545565819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109316281173717983697043879 163974421760576975545565819)
    ·
      refine ⟨245961632640865463318348729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163974421760576975545565819 245961632640865463318348729)
      ·
        refine ⟨184471224480649097488761547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245961632640865463318348729 184471224480649097488761547)
        ·
          refine ⟨276706836720973646233142321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184471224480649097488761547 276706836720973646233142321)
          ·
            refine ⟨207530127540730234674856741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276706836720973646233142321 207530127540730234674856741)
            ·
              refine ⟨38911898913886919001535639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207530127540730234674856741 38911898913886919001535639)
              ·
                refine ⟨58367848370830378502303459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38911898913886919001535639 58367848370830378502303459)
                ·
                  refine ⟨87551772556245567753455189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58367848370830378502303459 87551772556245567753455189)
                  ·
                    refine ⟨1025997334643502747110803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87551772556245567753455189 1025997334643502747110803)
                    ·
                      rfl

theorem cell23_5994368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_5994368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994368 prefixEnd_5994368 := by exact prefixLift 5994368
  have htrace : WordTrace (prefixWord ++ tailWord_5994368) baseStart_5994368 baseEnd_5994368 := by
    simpa [prefixWord, tailWord_5994368, baseEnd_5994368] using wordTrace_append hprefix tailTrace_5994368
  have hstable : (prefixWord ++ tailWord_5994368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994368).length < 2 ^ (prefixWord ++ tailWord_5994368).sum := by decide
  have hdescent : baseEnd_5994368 < baseStart_5994368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994390 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5994390 : Nat := 118140960795 + 5994390 * 2 ^ 59
def prefixEnd_5994390 : Nat := 4983230072969 + 3 ^ 40 * 5994390 * 2
def baseEnd_5994390 : Nat := 3078003300504907155257309

theorem tailTrace_5994390 : CollatzResearch.WordTrace tailWord_5994390 prefixEnd_5994390 3078003300504907155257309 := by
  unfold tailWord_5994390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13664585297084766571961789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145755576502237510100925749 13664585297084766571961789)
  ·
    refine ⟨5124219486406787464485671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13664585297084766571961789 5124219486406787464485671)
    ·
      refine ⟨7686329229610181196728507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124219486406787464485671 7686329229610181196728507)
      ·
        refine ⟨11529493844415271795092761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686329229610181196728507 11529493844415271795092761)
        ·
          refine ⟨8647120383311453846319571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11529493844415271795092761 8647120383311453846319571)
          ·
            refine ⟨12970680574967180769479357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647120383311453846319571 12970680574967180769479357)
            ·
              refine ⟨4864005215612692788554759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12970680574967180769479357 4864005215612692788554759)
              ·
                refine ⟨7296007823419039182832139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864005215612692788554759 7296007823419039182832139)
                ·
                  refine ⟨10944011735128558774248209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296007823419039182832139 10944011735128558774248209)
                  ·
                    refine ⟨8208008801346419080686157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10944011735128558774248209 8208008801346419080686157)
                    ·
                      refine ⟨3078003300504907155257309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208008801346419080686157 3078003300504907155257309)
                      ·
                        rfl

theorem cell23_5994390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5994390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994390 prefixEnd_5994390 := by exact prefixLift 5994390
  have htrace : WordTrace (prefixWord ++ tailWord_5994390) baseStart_5994390 baseEnd_5994390 := by
    simpa [prefixWord, tailWord_5994390, baseEnd_5994390] using wordTrace_append hprefix tailTrace_5994390
  have hstable : (prefixWord ++ tailWord_5994390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994390).length < 2 ^ (prefixWord ++ tailWord_5994390).sum := by decide
  have hdescent : baseEnd_5994390 < baseStart_5994390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994460 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5994460 : Nat := 118140960795 + 5994460 * 2 ^ 59
def prefixEnd_5994460 : Nat := 4983230072969 + 3 ^ 40 * 5994460 * 2
def baseEnd_5994460 : Nat := 3078039244150721881381987

theorem tailTrace_5994460 : CollatzResearch.WordTrace tailWord_5994460 prefixEnd_5994460 3078039244150721881381987 := by
  unfold tailWord_5994460
  simp only [CollatzResearch.WordTrace]
  refine ⟨109317958931551333553218417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145757278575401778070957889 109317958931551333553218417)
  ·
    refine ⟨81988469198663500164913813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109317958931551333553218417 81988469198663500164913813)
    ·
      refine ⟨3843209493687351570230335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81988469198663500164913813 3843209493687351570230335)
      ·
        refine ⟨5764814240531027355345503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843209493687351570230335 5764814240531027355345503)
        ·
          refine ⟨8647221360796541033018255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764814240531027355345503 8647221360796541033018255)
          ·
            refine ⟨12970832041194811549527383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647221360796541033018255 12970832041194811549527383)
            ·
              refine ⟨19456248061792217324291075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12970832041194811549527383 19456248061792217324291075)
              ·
                refine ⟨29184372092688325986436613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19456248061792217324291075 29184372092688325986436613)
                ·
                  refine ⟨5472069767379061122456865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29184372092688325986436613 5472069767379061122456865)
                  ·
                    refine ⟨4104052325534295841842649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472069767379061122456865 4104052325534295841842649)
                    ·
                      refine ⟨3078039244150721881381987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104052325534295841842649 3078039244150721881381987)
                      ·
                        rfl

theorem cell23_5994460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5994460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994460 prefixEnd_5994460 := by exact prefixLift 5994460
  have htrace : WordTrace (prefixWord ++ tailWord_5994460) baseStart_5994460 baseEnd_5994460 := by
    simpa [prefixWord, tailWord_5994460, baseEnd_5994460] using wordTrace_append hprefix tailTrace_5994460
  have hstable : (prefixWord ++ tailWord_5994460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994460).length < 2 ^ (prefixWord ++ tailWord_5994460).sum := by decide
  have hdescent : baseEnd_5994460 < baseStart_5994460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994492 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_5994492 : Nat := 118140960795 + 5994492 * 2 ^ 59
def prefixEnd_5994492 : Nat := 4983230072969 + 3 ^ 40 * 5994492 * 2
def baseEnd_5994492 : Nat := 1026018558510555252060613

theorem tailTrace_5994492 : CollatzResearch.WordTrace tailWord_5994492 prefixEnd_5994492 1026018558510555252060613 := by
  unfold tailWord_5994492
  simp only [CollatzResearch.WordTrace]
  refine ⟨109318542499493368285800865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145758056665991157714401153 109318542499493368285800865)
  ·
    refine ⟨81988906874620026214350649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109318542499493368285800865 81988906874620026214350649)
    ·
      refine ⟨61491680155965019660762987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81988906874620026214350649 61491680155965019660762987)
      ·
        refine ⟨92237520233947529491144481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61491680155965019660762987 92237520233947529491144481)
        ·
          refine ⟨69178140175460647118358361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92237520233947529491144481 69178140175460647118358361)
          ·
            refine ⟨51883605131595485338768771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69178140175460647118358361 51883605131595485338768771)
            ·
              refine ⟨77825407697393228008153157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51883605131595485338768771 77825407697393228008153157)
              ·
                refine ⟨14592263943261230251528717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77825407697393228008153157 14592263943261230251528717)
                ·
                  refine ⟨5472098978722961344323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14592263943261230251528717 5472098978722961344323269)
                  ·
                    refine ⟨1026018558510555252060613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472098978722961344323269 1026018558510555252060613)
                    ·
                      rfl

theorem cell23_5994492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_5994492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994492 prefixEnd_5994492 := by exact prefixLift 5994492
  have htrace : WordTrace (prefixWord ++ tailWord_5994492) baseStart_5994492 baseEnd_5994492 := by
    simpa [prefixWord, tailWord_5994492, baseEnd_5994492] using wordTrace_append hprefix tailTrace_5994492
  have hstable : (prefixWord ++ tailWord_5994492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994492).length < 2 ^ (prefixWord ++ tailWord_5994492).sum := by decide
  have hdescent : baseEnd_5994492 < baseStart_5994492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994549 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_5994549 : Nat := 118140960795 + 5994549 * 2 ^ 59
def prefixEnd_5994549 : Nat := 4983230072969 + 3 ^ 40 * 5994549 * 2
def baseEnd_5994549 : Nat := 3078084943928972033169077

theorem tailTrace_5994549 : CollatzResearch.WordTrace tailWord_5994549 prefixEnd_5994549 3078084943928972033169077 := by
  unfold tailWord_5994549
  simp only [CollatzResearch.WordTrace]
  refine ⟨218639163959780235306426701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145759442639853490204284467 218639163959780235306426701)
  ·
    refine ⟨81989686484917588239910013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218639163959780235306426701 81989686484917588239910013)
    ·
      refine ⟨30746132431844095589966255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81989686484917588239910013 30746132431844095589966255)
      ·
        refine ⟨46119198647766143384949383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30746132431844095589966255 46119198647766143384949383)
        ·
          refine ⟨69178797971649215077424075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46119198647766143384949383 69178797971649215077424075)
          ·
            refine ⟨103768196957473822616136113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69178797971649215077424075 103768196957473822616136113)
            ·
              refine ⟨77826147718105366962102085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103768196957473822616136113 77826147718105366962102085)
              ·
                refine ⟨14592402697144756305394141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77826147718105366962102085 14592402697144756305394141)
                ·
                  refine ⟨5472151011429283614522803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14592402697144756305394141 5472151011429283614522803)
                  ·
                    refine ⟨8208226517143925421784205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472151011429283614522803 8208226517143925421784205)
                    ·
                      refine ⟨3078084943928972033169077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208226517143925421784205 3078084943928972033169077)
                      ·
                        rfl

theorem cell23_5994549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_5994549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994549 prefixEnd_5994549 := by exact prefixLift 5994549
  have htrace : WordTrace (prefixWord ++ tailWord_5994549) baseStart_5994549 baseEnd_5994549 := by
    simpa [prefixWord, tailWord_5994549, baseEnd_5994549] using wordTrace_append hprefix tailTrace_5994549
  have hstable : (prefixWord ++ tailWord_5994549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994549).length < 2 ^ (prefixWord ++ tailWord_5994549).sum := by decide
  have hdescent : baseEnd_5994549 < baseStart_5994549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994555 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_5994555 : Nat := 118140960795 + 5994555 * 2 ^ 59
def prefixEnd_5994555 : Nat := 4983230072969 + 3 ^ 40 * 5994555 * 2
def baseEnd_5994555 : Nat := 3078088024812899009694049

theorem tailTrace_5994555 : CollatzResearch.WordTrace tailWord_5994555 prefixEnd_5994555 3078088024812899009694049 := by
  unfold tailWord_5994555
  simp only [CollatzResearch.WordTrace]
  refine ⟨218639382797758498331145119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145759588531838998887430079 218639382797758498331145119)
  ·
    refine ⟨327959074196637747496717679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218639382797758498331145119 327959074196637747496717679)
    ·
      refine ⟨491938611294956621245076519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327959074196637747496717679 491938611294956621245076519)
      ·
        refine ⟨737907916942434931867614779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491938611294956621245076519 737907916942434931867614779)
        ·
          refine ⟨1106861875413652397801422169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737907916942434931867614779 1106861875413652397801422169)
          ·
            refine ⟨830146406560239298351066627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106861875413652397801422169 830146406560239298351066627)
            ·
              refine ⟨1245219609840358947526599941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830146406560239298351066627 1245219609840358947526599941)
              ·
                refine ⟨233478676845067302661237489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1245219609840358947526599941 233478676845067302661237489)
                ·
                  refine ⟨175109007633800476995928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233478676845067302661237489 175109007633800476995928117)
                  ·
                    refine ⟨16416469465668794718368261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175109007633800476995928117 16416469465668794718368261)
                    ·
                      refine ⟨3078088024812899009694049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16416469465668794718368261 3078088024812899009694049)
                      ·
                        rfl

theorem cell23_5994555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_5994555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994555 prefixEnd_5994555 := by exact prefixLift 5994555
  have htrace : WordTrace (prefixWord ++ tailWord_5994555) baseStart_5994555 baseEnd_5994555 := by
    simpa [prefixWord, tailWord_5994555, baseEnd_5994555] using wordTrace_append hprefix tailTrace_5994555
  have hstable : (prefixWord ++ tailWord_5994555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994555).length < 2 ^ (prefixWord ++ tailWord_5994555).sum := by decide
  have hdescent : baseEnd_5994555 < baseStart_5994555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994559 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 2, 3, 2]
def baseStart_5994559 : Nat := 118140960795 + 5994559 * 2 ^ 59
def prefixEnd_5994559 : Nat := 4983230072969 + 3 ^ 40 * 5994559 * 2
def baseEnd_5994559 : Nat := 3078090078735516994044031

theorem tailTrace_5994559 : CollatzResearch.WordTrace tailWord_5994559 prefixEnd_5994559 3078090078735516994044031 := by
  unfold tailWord_5994559
  simp only [CollatzResearch.WordTrace]
  refine ⟨218639528689744007014290731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145759685793162671342860487 218639528689744007014290731)
  ·
    refine ⟨327959293034616010521436097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218639528689744007014290731 327959293034616010521436097)
    ·
      refine ⟨245969469775962007891077073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327959293034616010521436097 245969469775962007891077073)
      ·
        refine ⟨184477102331971505918307805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245969469775962007891077073 184477102331971505918307805)
        ·
          refine ⟨69178913374489314719365427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184477102331971505918307805 69178913374489314719365427)
          ·
            refine ⟨103768370061733972079048141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69178913374489314719365427 103768370061733972079048141)
            ·
              refine ⟨38913138773150239529643053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103768370061733972079048141 38913138773150239529643053)
              ·
                refine ⟨14592427039931339823616145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38913138773150239529643053 14592427039931339823616145)
                ·
                  refine ⟨10944320279948504867712109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14592427039931339823616145 10944320279948504867712109)
                  ·
                    refine ⟨4104120104980689325392041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10944320279948504867712109 4104120104980689325392041)
                    ·
                      refine ⟨3078090078735516994044031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104120104980689325392041 3078090078735516994044031)
                      ·
                        rfl

theorem cell23_5994559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_5994559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994559 prefixEnd_5994559 := by exact prefixLift 5994559
  have htrace : WordTrace (prefixWord ++ tailWord_5994559) baseStart_5994559 baseEnd_5994559 := by
    simpa [prefixWord, tailWord_5994559, baseEnd_5994559] using wordTrace_append hprefix tailTrace_5994559
  have hstable : (prefixWord ++ tailWord_5994559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994559).length < 2 ^ (prefixWord ++ tailWord_5994559).sum := by decide
  have hdescent : baseEnd_5994559 < baseStart_5994559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994569 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_5994569 : Nat := 118140960795 + 5994569 * 2 ^ 59
def prefixEnd_5994569 : Nat := 4983230072969 + 3 ^ 40 * 5994569 * 2
def baseEnd_5994569 : Nat := 1026031737847353984972995

theorem tailTrace_5994569 : CollatzResearch.WordTrace tailWord_5994569 prefixEnd_5994569 1026031737847353984972995 := by
  unfold tailWord_5994569
  simp only [CollatzResearch.WordTrace]
  refine ⟨218639893419707778722154761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145759928946471852481436507 218639893419707778722154761)
  ·
    refine ⟨163979920064780834041616071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218639893419707778722154761 163979920064780834041616071)
    ·
      refine ⟨245969880097171251062424107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163979920064780834041616071 245969880097171251062424107)
      ·
        refine ⟨368954820145756876593636161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245969880097171251062424107 368954820145756876593636161)
        ·
          refine ⟨276716115109317657445227121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368954820145756876593636161 276716115109317657445227121)
          ·
            refine ⟨207537086331988243083920341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276716115109317657445227121 207537086331988243083920341)
            ·
              refine ⟨4864150460905974447279383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207537086331988243083920341 4864150460905974447279383)
              ·
                refine ⟨7296225691358961670919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864150460905974447279383 7296225691358961670919075)
                ·
                  refine ⟨10944338537038442506378613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296225691358961670919075 10944338537038442506378613)
                  ·
                    refine ⟨1026031737847353984972995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10944338537038442506378613 1026031737847353984972995)
                    ·
                      rfl

theorem cell23_5994569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_5994569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994569 prefixEnd_5994569 := by exact prefixLift 5994569
  have htrace : WordTrace (prefixWord ++ tailWord_5994569) baseStart_5994569 baseEnd_5994569 := by
    simpa [prefixWord, tailWord_5994569, baseEnd_5994569] using wordTrace_append hprefix tailTrace_5994569
  have hstable : (prefixWord ++ tailWord_5994569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994569).length < 2 ^ (prefixWord ++ tailWord_5994569).sum := by decide
  have hdescent : baseEnd_5994569 < baseStart_5994569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994583 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_5994583 : Nat := 118140960795 + 5994583 * 2 ^ 59
def prefixEnd_5994583 : Nat := 4983230072969 + 3 ^ 40 * 5994583 * 2
def baseEnd_5994583 : Nat := 3078102402271224900143921

theorem tailTrace_5994583 : CollatzResearch.WordTrace tailWord_5994583 prefixEnd_5994583 3078102402271224900143921 := by
  unfold tailWord_5994583
  simp only [CollatzResearch.WordTrace]
  refine ⟨218640404041657059113164403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145760269361104706075442935 218640404041657059113164403)
  ·
    refine ⟨327960606062485588669746605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218640404041657059113164403 327960606062485588669746605)
    ·
      refine ⟨122985227273432095751154977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327960606062485588669746605 122985227273432095751154977)
      ·
        refine ⟨92238920455074071813366233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122985227273432095751154977 92238920455074071813366233)
        ·
          refine ⟨69179190341305553860024675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92238920455074071813366233 69179190341305553860024675)
          ·
            refine ⟨103768785511958330790037013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69179190341305553860024675 103768785511958330790037013)
            ·
              refine ⟨4864161820873046755782985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103768785511958330790037013 4864161820873046755782985)
              ·
                refine ⟨3648121365654785066837239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864161820873046755782985 3648121365654785066837239)
                ·
                  refine ⟨5472182048482177600255859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648121365654785066837239 5472182048482177600255859)
                  ·
                    refine ⟨8208273072723266400383789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472182048482177600255859 8208273072723266400383789)
                    ·
                      refine ⟨3078102402271224900143921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208273072723266400383789 3078102402271224900143921)
                      ·
                        rfl

theorem cell23_5994583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_5994583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994583 prefixEnd_5994583 := by exact prefixLift 5994583
  have htrace : WordTrace (prefixWord ++ tailWord_5994583) baseStart_5994583 baseEnd_5994583 := by
    simpa [prefixWord, tailWord_5994583, baseEnd_5994583] using wordTrace_append hprefix tailTrace_5994583
  have hstable : (prefixWord ++ tailWord_5994583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994583).length < 2 ^ (prefixWord ++ tailWord_5994583).sum := by decide
  have hdescent : baseEnd_5994583 < baseStart_5994583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994599 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5994599 : Nat := 118140960795 + 5994599 * 2 ^ 59
def prefixEnd_5994599 : Nat := 4983230072969 + 3 ^ 40 * 5994599 * 2
def baseEnd_5994599 : Nat := 1026036872653898945847949

theorem tailTrace_5994599 : CollatzResearch.WordTrace tailWord_5994599 prefixEnd_5994599 1026036872653898945847949 := by
  unfold tailWord_5994599
  simp only [CollatzResearch.WordTrace]
  refine ⟨218640987609599093845746851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145760658406399395897164567 218640987609599093845746851)
  ·
    refine ⟨327961481414398640768620277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218640987609599093845746851 327961481414398640768620277)
    ·
      refine ⟨30746388882599872572058151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327961481414398640768620277 30746388882599872572058151)
      ·
        refine ⟨46119583323899808858087227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30746388882599872572058151 46119583323899808858087227)
        ·
          refine ⟨69179374985849713287130841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46119583323899808858087227 69179374985849713287130841)
          ·
            refine ⟨51884531239387284965348131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69179374985849713287130841 51884531239387284965348131)
            ·
              refine ⟨77826796859080927448022197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51884531239387284965348131 77826796859080927448022197)
              ·
                refine ⟨7296262205538836948252081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77826796859080927448022197 7296262205538836948252081)
                ·
                  refine ⟨5472196654154127711189061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7296262205538836948252081 5472196654154127711189061)
                  ·
                    refine ⟨1026036872653898945847949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472196654154127711189061 1026036872653898945847949)
                    ·
                      rfl

theorem cell23_5994599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5994599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994599 prefixEnd_5994599 := by exact prefixLift 5994599
  have htrace : WordTrace (prefixWord ++ tailWord_5994599) baseStart_5994599 baseEnd_5994599 := by
    simpa [prefixWord, tailWord_5994599, baseEnd_5994599] using wordTrace_append hprefix tailTrace_5994599
  have hstable : (prefixWord ++ tailWord_5994599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994599).length < 2 ^ (prefixWord ++ tailWord_5994599).sum := by decide
  have hdescent : baseEnd_5994599 < baseStart_5994599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994609 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_5994609 : Nat := 118140960795 + 5994609 * 2 ^ 59
def prefixEnd_5994609 : Nat := 4983230072969 + 3 ^ 40 * 5994609 * 2
def baseEnd_5994609 : Nat := 3078115752768241798418801

theorem tailTrace_5994609 : CollatzResearch.WordTrace tailWord_5994609 prefixEnd_5994609 3078115752768241798418801 := by
  unfold tailWord_5994609
  simp only [CollatzResearch.WordTrace]
  refine ⟨218641352339562865553610881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145760901559708577035740587 218641352339562865553610881)
  ·
    refine ⟨163981014254672149165208161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218641352339562865553610881 163981014254672149165208161)
    ·
      refine ⟨122985760691004111873906121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163981014254672149165208161 122985760691004111873906121)
      ·
        refine ⟨92239320518253083905429591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122985760691004111873906121 92239320518253083905429591)
        ·
          refine ⟨138358980777379625858144387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92239320518253083905429591 138358980777379625858144387)
          ·
            refine ⟨207538471166069438787216581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138358980777379625858144387 207538471166069438787216581)
            ·
              refine ⟨38913463343638019772603109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207538471166069438787216581 38913463343638019772603109)
              ·
                refine ⟨7296274376932128707363083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38913463343638019772603109 7296274376932128707363083)
                ·
                  refine ⟨10944411565398193061044625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296274376932128707363083 10944411565398193061044625)
                  ·
                    refine ⟨8208308674048644795783469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10944411565398193061044625 8208308674048644795783469)
                    ·
                      refine ⟨3078115752768241798418801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208308674048644795783469 3078115752768241798418801)
                      ·
                        rfl

theorem cell23_5994609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_5994609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994609 prefixEnd_5994609 := by exact prefixLift 5994609
  have htrace : WordTrace (prefixWord ++ tailWord_5994609) baseStart_5994609 baseEnd_5994609 := by
    simpa [prefixWord, tailWord_5994609, baseEnd_5994609] using wordTrace_append hprefix tailTrace_5994609
  have hstable : (prefixWord ++ tailWord_5994609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994609).length < 2 ^ (prefixWord ++ tailWord_5994609).sum := by decide
  have hdescent : baseEnd_5994609 < baseStart_5994609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994649 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 5, 3, 2]
def baseStart_5994649 : Nat := 118140960795 + 5994649 * 2 ^ 59
def prefixEnd_5994649 : Nat := 4983230072969 + 3 ^ 40 * 5994649 * 2
def baseEnd_5994649 : Nat := 3078136291994421641918617

theorem tailTrace_5994649 : CollatzResearch.WordTrace tailWord_5994649 prefixEnd_5994649 3078136291994421641918617 := by
  unfold tailWord_5994649
  simp only [CollatzResearch.WordTrace]
  refine ⟨218642811259417952385067001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145761874172945301590044667 218642811259417952385067001)
  ·
    refine ⟨163982108444563464288800251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218642811259417952385067001 163982108444563464288800251)
    ·
      refine ⟨245973162666845196433200377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163982108444563464288800251 245973162666845196433200377)
      ·
        refine ⟨184479872000133897324900283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245973162666845196433200377 184479872000133897324900283)
        ·
          refine ⟨276719808000200845987350425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184479872000133897324900283 276719808000200845987350425)
          ·
            refine ⟨207539856000150634490512819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276719808000200845987350425 207539856000150634490512819)
            ·
              refine ⟨311309784000225951735769229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207539856000150634490512819 311309784000225951735769229)
              ·
                refine ⟨116741169000084731900913461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311309784000225951735769229 116741169000084731900913461)
                ·
                  refine ⟨10944484593757943615710637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116741169000084731900913461 10944484593757943615710637)
                  ·
                    refine ⟨4104181722659228855891489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10944484593757943615710637 4104181722659228855891489)
                    ·
                      refine ⟨3078136291994421641918617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104181722659228855891489 3078136291994421641918617)
                      ·
                        rfl

theorem cell23_5994649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_5994649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994649 prefixEnd_5994649 := by exact prefixLift 5994649
  have htrace : WordTrace (prefixWord ++ tailWord_5994649) baseStart_5994649 baseEnd_5994649 := by
    simpa [prefixWord, tailWord_5994649, baseEnd_5994649] using wordTrace_append hprefix tailTrace_5994649
  have hstable : (prefixWord ++ tailWord_5994649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994649).length < 2 ^ (prefixWord ++ tailWord_5994649).sum := by decide
  have hdescent : baseEnd_5994649 < baseStart_5994649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994656 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_5994656 : Nat := 118140960795 + 5994656 * 2 ^ 59
def prefixEnd_5994656 : Nat := 4983230072969 + 3 ^ 40 * 5994656 * 2
def baseEnd_5994656 : Nat := 3078139886359003114531085

theorem tailTrace_5994656 : CollatzResearch.WordTrace tailWord_5994656 prefixEnd_5994656 3078139886359003114531085 := by
  unfold tailWord_5994656
  simp only [CollatzResearch.WordTrace]
  refine ⟨109321533285196296290285911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145762044380261728387047881 109321533285196296290285911)
  ·
    refine ⟨163982299927794444435428867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109321533285196296290285911 163982299927794444435428867)
    ·
      refine ⟨245973449891691666653143301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163982299927794444435428867 245973449891691666653143301)
      ·
        refine ⟨46120021854692187497464369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245973449891691666653143301 46120021854692187497464369)
        ·
          refine ⟨34590016391019140623098277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46120021854692187497464369 34590016391019140623098277)
          ·
            refine ⟨6485628073316088866830927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34590016391019140623098277 6485628073316088866830927)
            ·
              refine ⟨9728442109974133300246391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485628073316088866830927 9728442109974133300246391)
              ·
                refine ⟨14592663164961199950369587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9728442109974133300246391 14592663164961199950369587)
                ·
                  refine ⟨21888994747441799925554381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14592663164961199950369587 21888994747441799925554381)
                  ·
                    refine ⟨8208373030290674972082893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21888994747441799925554381 8208373030290674972082893)
                    ·
                      refine ⟨3078139886359003114531085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208373030290674972082893 3078139886359003114531085)
                      ·
                        rfl

theorem cell23_5994656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_5994656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994656 prefixEnd_5994656 := by exact prefixLift 5994656
  have htrace : WordTrace (prefixWord ++ tailWord_5994656) baseStart_5994656 baseEnd_5994656 := by
    simpa [prefixWord, tailWord_5994656, baseEnd_5994656] using wordTrace_append hprefix tailTrace_5994656
  have hstable : (prefixWord ++ tailWord_5994656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994656).length < 2 ^ (prefixWord ++ tailWord_5994656).sum := by decide
  have hdescent : baseEnd_5994656 < baseStart_5994656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994663 : List Nat := [1, 1, 6, 2, 3, 1, 2, 7]
def baseStart_5994663 : Nat := 118140960795 + 5994663 * 2 ^ 59
def prefixEnd_5994663 : Nat := 4983230072969 + 3 ^ 40 * 5994663 * 2
def baseEnd_5994663 : Nat := 114005314100873503227539

theorem tailTrace_5994663 : CollatzResearch.WordTrace tailWord_5994663 prefixEnd_5994663 114005314100873503227539 := by
  unfold tailWord_5994663
  simp only [CollatzResearch.WordTrace]
  refine ⟨218643321881367232776076643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145762214587578155184051095 218643321881367232776076643)
  ·
    refine ⟨327964982822050849164114965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218643321881367232776076643 327964982822050849164114965)
    ·
      refine ⟨15373358569783633554567889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 327964982822050849164114965 15373358569783633554567889)
      ·
        refine ⟨11530018927337725165925917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15373358569783633554567889 11530018927337725165925917)
        ·
          refine ⟨4323757097751646937222219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11530018927337725165925917 4323757097751646937222219)
          ·
            refine ⟨6485635646627470405833329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323757097751646937222219 6485635646627470405833329)
            ·
              refine ⟨4864226734970602804374997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485635646627470405833329 4864226734970602804374997)
              ·
                refine ⟨114005314100873503227539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4864226734970602804374997 114005314100873503227539)
                ·
                  rfl

theorem cell23_5994663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 7].length) (baseStart_5994663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994663 prefixEnd_5994663 := by exact prefixLift 5994663
  have htrace : WordTrace (prefixWord ++ tailWord_5994663) baseStart_5994663 baseEnd_5994663 := by
    simpa [prefixWord, tailWord_5994663, baseEnd_5994663] using wordTrace_append hprefix tailTrace_5994663
  have hstable : (prefixWord ++ tailWord_5994663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994663).length < 2 ^ (prefixWord ++ tailWord_5994663).sum := by decide
  have hdescent : baseEnd_5994663 < baseStart_5994663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994669 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5994669 : Nat := 118140960795 + 5994669 * 2 ^ 59
def prefixEnd_5994669 : Nat := 4983230072969 + 3 ^ 40 * 5994669 * 2
def baseEnd_5994669 : Nat := 3078146561607511563668525

theorem tailTrace_5994669 : CollatzResearch.WordTrace tailWord_5994669 prefixEnd_5994669 3078146561607511563668525 := by
  unfold tailWord_5994669
  simp only [CollatzResearch.WordTrace]
  refine ⟨218643540719345495800795061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145762360479563663867196707 218643540719345495800795061)
  ·
    refine ⟨20497831942438640231324537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218643540719345495800795061 20497831942438640231324537)
    ·
      refine ⟨15373373956828980173493403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20497831942438640231324537 15373373956828980173493403)
      ·
        refine ⟨23060060935243470260240105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373373956828980173493403 23060060935243470260240105)
        ·
          refine ⟨17295045701432602695180079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23060060935243470260240105 17295045701432602695180079)
          ·
            refine ⟨25942568552148904042770119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295045701432602695180079 25942568552148904042770119)
            ·
              refine ⟨38913852828223356064155179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25942568552148904042770119 38913852828223356064155179)
              ·
                refine ⟨58370779242335034096232769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38913852828223356064155179 58370779242335034096232769)
                ·
                  refine ⟨43778084431751275572174577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58370779242335034096232769 43778084431751275572174577)
                  ·
                    refine ⟨32833563323813456679130933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43778084431751275572174577 32833563323813456679130933)
                    ·
                      refine ⟨3078146561607511563668525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32833563323813456679130933 3078146561607511563668525)
                      ·
                        rfl

theorem cell23_5994669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5994669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994669 prefixEnd_5994669 := by exact prefixLift 5994669
  have htrace : WordTrace (prefixWord ++ tailWord_5994669) baseStart_5994669 baseEnd_5994669 := by
    simpa [prefixWord, tailWord_5994669, baseEnd_5994669] using wordTrace_append hprefix tailTrace_5994669
  have hstable : (prefixWord ++ tailWord_5994669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994669).length < 2 ^ (prefixWord ++ tailWord_5994669).sum := by decide
  have hdescent : baseEnd_5994669 < baseStart_5994669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994682 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_5994682 : Nat := 118140960795 + 5994682 * 2 ^ 59
def prefixEnd_5994682 : Nat := 4983230072969 + 3 ^ 40 * 5994682 * 2
def baseEnd_5994682 : Nat := 3078153236856020012805965

theorem tailTrace_5994682 : CollatzResearch.WordTrace tailWord_5994682 prefixEnd_5994682 3078153236856020012805965 := by
  unfold tailWord_5994682
  simp only [CollatzResearch.WordTrace]
  refine ⟨54661003717074599755254575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145762676578865599347345533 54661003717074599755254575)
  ·
    refine ⟨81991505575611899632881863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54661003717074599755254575 81991505575611899632881863)
    ·
      refine ⟨122987258363417849449322795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81991505575611899632881863 122987258363417849449322795)
      ·
        refine ⟨184480887545126774173984193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122987258363417849449322795 184480887545126774173984193)
        ·
          refine ⟨138360665658845080630488145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184480887545126774173984193 138360665658845080630488145)
          ·
            refine ⟨103770499244133810472866109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138360665658845080630488145 103770499244133810472866109)
            ·
              refine ⟨38913937216550178927324791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103770499244133810472866109 38913937216550178927324791)
              ·
                refine ⟨58370905824825268390987187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38913937216550178927324791 58370905824825268390987187)
                ·
                  refine ⟨87556358737237902586480781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58370905824825268390987187 87556358737237902586480781)
                  ·
                    refine ⟨32833634526464213469930293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87556358737237902586480781 32833634526464213469930293)
                    ·
                      refine ⟨3078153236856020012805965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32833634526464213469930293 3078153236856020012805965)
                      ·
                        rfl

theorem cell23_5994682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_5994682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994682 prefixEnd_5994682 := by exact prefixLift 5994682
  have htrace : WordTrace (prefixWord ++ tailWord_5994682) baseStart_5994682 baseEnd_5994682 := by
    simpa [prefixWord, tailWord_5994682, baseEnd_5994682] using wordTrace_append hprefix tailTrace_5994682
  have hstable : (prefixWord ++ tailWord_5994682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994682).length < 2 ^ (prefixWord ++ tailWord_5994682).sum := by decide
  have hdescent : baseEnd_5994682 < baseStart_5994682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994690 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5994690 : Nat := 118140960795 + 5994690 * 2 ^ 59
def prefixEnd_5994690 : Nat := 4983230072969 + 3 ^ 40 * 5994690 * 2
def baseEnd_5994690 : Nat := 3078157344701255981505929

theorem tailTrace_5994690 : CollatzResearch.WordTrace tailWord_5994690 prefixEnd_5994690 3078157344701255981505929 := by
  unfold tailWord_5994690
  simp only [CollatzResearch.WordTrace]
  refine ⟨54661076663067354096827381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145762871101512944258206349 54661076663067354096827381)
  ·
    refine ⟨5124475937162564446577567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54661076663067354096827381 5124475937162564446577567)
    ·
      refine ⟨7686713905743846669866351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124475937162564446577567 7686713905743846669866351)
      ·
        refine ⟨11530070858615770004799527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686713905743846669866351 11530070858615770004799527)
        ·
          refine ⟨17295106287923655007199291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11530070858615770004799527 17295106287923655007199291)
          ·
            refine ⟨25942659431885482510798937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295106287923655007199291 25942659431885482510798937)
            ·
              refine ⟨19456994573914111883099203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25942659431885482510798937 19456994573914111883099203)
              ·
                refine ⟨29185491860871167824648805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19456994573914111883099203 29185491860871167824648805)
                ·
                  refine ⟨5472279723913343967121651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29185491860871167824648805 5472279723913343967121651)
                  ·
                    refine ⟨8208419585870015950682477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472279723913343967121651 8208419585870015950682477)
                    ·
                      refine ⟨3078157344701255981505929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208419585870015950682477 3078157344701255981505929)
                      ·
                        rfl

theorem cell23_5994690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5994690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994690 prefixEnd_5994690 := by exact prefixLift 5994690
  have htrace : WordTrace (prefixWord ++ tailWord_5994690) baseStart_5994690 baseEnd_5994690 := by
    simpa [prefixWord, tailWord_5994690, baseEnd_5994690] using wordTrace_append hprefix tailTrace_5994690
  have hstable : (prefixWord ++ tailWord_5994690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994690).length < 2 ^ (prefixWord ++ tailWord_5994690).sum := by decide
  have hdescent : baseEnd_5994690 < baseStart_5994690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994779 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 5, 4]
def baseStart_5994779 : Nat := 118140960795 + 5994779 * 2 ^ 59
def prefixEnd_5994779 : Nat := 4983230072969 + 3 ^ 40 * 5994779 * 2
def baseEnd_5994779 : Nat := 1026067681493168711097673

theorem tailTrace_5994779 : CollatzResearch.WordTrace tailWord_5994779 prefixEnd_5994779 1026067681493168711097673 := by
  unfold tailWord_5994779
  simp only [CollatzResearch.WordTrace]
  refine ⟨218647552748946984587299391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145765035165964656391532927 218647552748946984587299391)
  ·
    refine ⟨327971329123420476880949087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218647552748946984587299391 327971329123420476880949087)
    ·
      refine ⟨491956993685130715321423631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327971329123420476880949087 491956993685130715321423631)
      ·
        refine ⟨737935490527696072982135447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491956993685130715321423631 737935490527696072982135447)
        ·
          refine ⟨1106903235791544109473203171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737935490527696072982135447 1106903235791544109473203171)
          ·
            refine ⟨1660354853687316164209804757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106903235791544109473203171 1660354853687316164209804757)
            ·
              refine ⟨38914566883296472598667299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1660354853687316164209804757 38914566883296472598667299)
              ·
                refine ⟨58371850324944708898000949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38914566883296472598667299 58371850324944708898000949)
                ·
                  refine ⟨5472360967963566459187589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58371850324944708898000949 5472360967963566459187589)
                  ·
                    refine ⟨1026067681493168711097673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472360967963566459187589 1026067681493168711097673)
                    ·
                      rfl

theorem cell23_5994779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 4].length) (baseStart_5994779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994779 prefixEnd_5994779 := by exact prefixLift 5994779
  have htrace : WordTrace (prefixWord ++ tailWord_5994779) baseStart_5994779 baseEnd_5994779 := by
    simpa [prefixWord, tailWord_5994779, baseEnd_5994779] using wordTrace_append hprefix tailTrace_5994779
  have hstable : (prefixWord ++ tailWord_5994779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994779).length < 2 ^ (prefixWord ++ tailWord_5994779).sum := by decide
  have hdescent : baseEnd_5994779 < baseStart_5994779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994786 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_5994786 : Nat := 118140960795 + 5994786 * 2 ^ 59
def prefixEnd_5994786 : Nat := 4983230072969 + 3 ^ 40 * 5994786 * 2
def baseEnd_5994786 : Nat := 3078206638844087605905487

theorem tailTrace_5994786 : CollatzResearch.WordTrace tailWord_5994786 prefixEnd_5994786 3078206638844087605905487 := by
  unfold tailWord_5994786
  simp only [CollatzResearch.WordTrace]
  refine ⟨54661952014980406195701053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145765205373281083188536141 54661952014980406195701053)
  ·
    refine ⟨20498232005617652323387895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54661952014980406195701053 20498232005617652323387895)
    ·
      refine ⟨30747348008426478485081843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20498232005617652323387895 30747348008426478485081843)
      ·
        refine ⟨46121022012639717727622765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30747348008426478485081843 46121022012639717727622765)
        ·
          refine ⟨17295383254739894147858537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46121022012639717727622765 17295383254739894147858537)
          ·
            refine ⟨12971537441054920610893903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17295383254739894147858537 12971537441054920610893903)
            ·
              refine ⟨19457306161582380916340855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12971537441054920610893903 19457306161582380916340855)
              ·
                refine ⟨29185959242373571374511283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19457306161582380916340855 29185959242373571374511283)
                ·
                  refine ⟨43778938863560357061766925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29185959242373571374511283 43778938863560357061766925)
                  ·
                    refine ⟨16417102073835133898162597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43778938863560357061766925 16417102073835133898162597)
                    ·
                      refine ⟨3078206638844087605905487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16417102073835133898162597 3078206638844087605905487)
                      ·
                        rfl

theorem cell23_5994786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_5994786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994786 prefixEnd_5994786 := by exact prefixLift 5994786
  have htrace : WordTrace (prefixWord ++ tailWord_5994786) baseStart_5994786 baseEnd_5994786 := by
    simpa [prefixWord, tailWord_5994786, baseEnd_5994786] using wordTrace_append hprefix tailTrace_5994786
  have hstable : (prefixWord ++ tailWord_5994786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994786).length < 2 ^ (prefixWord ++ tailWord_5994786).sum := by decide
  have hdescent : baseEnd_5994786 < baseStart_5994786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994876 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_5994876 : Nat := 118140960795 + 5994876 * 2 ^ 59
def prefixEnd_5994876 : Nat := 4983230072969 + 3 ^ 40 * 5994876 * 2
def baseEnd_5994876 : Nat := 3078252852102992253780073

theorem tailTrace_5994876 : CollatzResearch.WordTrace tailWord_5994876 prefixEnd_5994876 3078252852102992253780073 := by
  unfold tailWord_5994876
  simp only [CollatzResearch.WordTrace]
  refine ⟨109325545314797785076790241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145767393753063713435720321 109325545314797785076790241)
  ·
    refine ⟨81994158986098338807592681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109325545314797785076790241 81994158986098338807592681)
    ·
      refine ⟨61495619239573754105694511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81994158986098338807592681 61495619239573754105694511)
      ·
        refine ⟨92243428859360631158541767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61495619239573754105694511 92243428859360631158541767)
        ·
          refine ⟨138365143289040946737812651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92243428859360631158541767 138365143289040946737812651)
          ·
            refine ⟨207547714933561420106718977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138365143289040946737812651 207547714933561420106718977)
            ·
              refine ⟨155660786200171065080039233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207547714933561420106718977 155660786200171065080039233)
              ·
                refine ⟨116745589650128298810029425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155660786200171065080039233 116745589650128298810029425)
                ·
                  refine ⟨87559192237596224107522069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116745589650128298810029425 87559192237596224107522069)
                  ·
                    refine ⟨4104337136137323005040097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87559192237596224107522069 4104337136137323005040097)
                    ·
                      refine ⟨3078252852102992253780073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104337136137323005040097 3078252852102992253780073)
                      ·
                        rfl

theorem cell23_5994876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_5994876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994876 prefixEnd_5994876 := by exact prefixLift 5994876
  have htrace : WordTrace (prefixWord ++ tailWord_5994876) baseStart_5994876 baseEnd_5994876 := by
    simpa [prefixWord, tailWord_5994876, baseEnd_5994876] using wordTrace_append hprefix tailTrace_5994876
  have hstable : (prefixWord ++ tailWord_5994876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994876).length < 2 ^ (prefixWord ++ tailWord_5994876).sum := by decide
  have hdescent : baseEnd_5994876 < baseStart_5994876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994906 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5994906 : Nat := 118140960795 + 5994906 * 2 ^ 59
def prefixEnd_5994906 : Nat := 4983230072969 + 3 ^ 40 * 5994906 * 2
def baseEnd_5994906 : Nat := 3078268256522627136404935

theorem tailTrace_5994906 : CollatzResearch.WordTrace tailWord_5994906 prefixEnd_5994906 3078268256522627136404935 := by
  unfold tailWord_5994906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54663046204871721319293143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145768123212991256851448381 54663046204871721319293143)
  ·
    refine ⟨81994569307307581978939715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54663046204871721319293143 81994569307307581978939715)
    ·
      refine ⟨122991853960961372968409573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81994569307307581978939715 122991853960961372968409573)
      ·
        refine ⟨23060972617680257431576795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122991853960961372968409573 23060972617680257431576795)
        ·
          refine ⟨34591458926520386147365193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23060972617680257431576795 34591458926520386147365193)
          ·
            refine ⟨25943594194890289610523895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34591458926520386147365193 25943594194890289610523895)
            ·
              refine ⟨38915391292335434415785843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25943594194890289610523895 38915391292335434415785843)
              ·
                refine ⟨58373086938503151623678765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38915391292335434415785843 58373086938503151623678765)
                ·
                  refine ⟨21889907601938681858879537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58373086938503151623678765 21889907601938681858879537)
                  ·
                    refine ⟨16417430701454011394159653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21889907601938681858879537 16417430701454011394159653)
                    ·
                      refine ⟨3078268256522627136404935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16417430701454011394159653 3078268256522627136404935)
                      ·
                        rfl

theorem cell23_5994906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5994906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994906 prefixEnd_5994906 := by exact prefixLift 5994906
  have htrace : WordTrace (prefixWord ++ tailWord_5994906) baseStart_5994906 baseEnd_5994906 := by
    simpa [prefixWord, tailWord_5994906, baseEnd_5994906] using wordTrace_append hprefix tailTrace_5994906
  have hstable : (prefixWord ++ tailWord_5994906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994906).length < 2 ^ (prefixWord ++ tailWord_5994906).sum := by decide
  have hdescent : baseEnd_5994906 < baseStart_5994906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994920 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5994920 : Nat := 118140960795 + 5994920 * 2 ^ 59
def prefixEnd_5994920 : Nat := 4983230072969 + 3 ^ 40 * 5994920 * 2
def baseEnd_5994920 : Nat := 1026091815083930027209957

theorem tailTrace_5994920 : CollatzResearch.WordTrace tailWord_5994920 prefixEnd_5994920 1026091815083930027209957 := by
  unfold tailWord_5994920
  simp only [CollatzResearch.WordTrace]
  refine ⟨109326347720718082834091107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145768463627624110445454809 109326347720718082834091107)
  ·
    refine ⟨163989521581077124251136661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109326347720718082834091107 163989521581077124251136661)
    ·
      refine ⟨7687008824112990199272031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163989521581077124251136661 7687008824112990199272031)
      ·
        refine ⟨11530513236169485298908047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7687008824112990199272031 11530513236169485298908047)
        ·
          refine ⟨17295769854254227948362071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11530513236169485298908047 17295769854254227948362071)
          ·
            refine ⟨25943654781381341922543107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295769854254227948362071 25943654781381341922543107)
            ·
              refine ⟨38915482172072012883814661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25943654781381341922543107 38915482172072012883814661)
              ·
                refine ⟨7296652907263502415715249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38915482172072012883814661 7296652907263502415715249)
                ·
                  refine ⟨5472489680447626811786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7296652907263502415715249 5472489680447626811786437)
                  ·
                    refine ⟨1026091815083930027209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472489680447626811786437 1026091815083930027209957)
                    ·
                      rfl

theorem cell23_5994920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5994920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994920 prefixEnd_5994920 := by exact prefixLift 5994920
  have htrace : WordTrace (prefixWord ++ tailWord_5994920) baseStart_5994920 baseEnd_5994920 := by
    simpa [prefixWord, tailWord_5994920, baseEnd_5994920] using wordTrace_append hprefix tailTrace_5994920
  have hstable : (prefixWord ++ tailWord_5994920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994920).length < 2 ^ (prefixWord ++ tailWord_5994920).sum := by decide
  have hdescent : baseEnd_5994920 < baseStart_5994920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994933 : List Nat := [1, 3, 3, 2, 3, 2, 1, 8]
def baseStart_5994933 : Nat := 118140960795 + 5994933 * 2 ^ 59
def prefixEnd_5994933 : Nat := 4983230072969 + 3 ^ 40 * 5994933 * 2
def baseEnd_5994933 : Nat := 114010448907418464102493

theorem tailTrace_5994933 : CollatzResearch.WordTrace tailWord_5994933 prefixEnd_5994933 114010448907418464102493 := by
  unfold tailWord_5994933
  simp only [CollatzResearch.WordTrace]
  refine ⟨218653169590389068888405453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145768779726926045925603635 218653169590389068888405453)
  ·
    refine ⟨81994938596395900833152045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218653169590389068888405453 81994938596395900833152045)
    ·
      refine ⟨30748101973648462812432017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81994938596395900833152045 30748101973648462812432017)
      ·
        refine ⟨23061076480236347109324013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30748101973648462812432017 23061076480236347109324013)
        ·
          refine ⟨8647903680088630165996505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23061076480236347109324013 8647903680088630165996505)
          ·
            refine ⟨6485927760066472624497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8647903680088630165996505 6485927760066472624497379)
            ·
              refine ⟨9728891640099708936746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485927760066472624497379 9728891640099708936746069)
              ·
                refine ⟨114010448907418464102493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9728891640099708936746069 114010448907418464102493)
                ·
                  rfl

theorem cell23_5994933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 8].length) (baseStart_5994933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994933 prefixEnd_5994933 := by exact prefixLift 5994933
  have htrace : WordTrace (prefixWord ++ tailWord_5994933) baseStart_5994933 baseEnd_5994933 := by
    simpa [prefixWord, tailWord_5994933, baseEnd_5994933] using wordTrace_append hprefix tailTrace_5994933
  have hstable : (prefixWord ++ tailWord_5994933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994933).length < 2 ^ (prefixWord ++ tailWord_5994933).sum := by decide
  have hdescent : baseEnd_5994933 < baseStart_5994933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994939 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_5994939 : Nat := 118140960795 + 5994939 * 2 ^ 59
def prefixEnd_5994939 : Nat := 4983230072969 + 3 ^ 40 * 5994939 * 2
def baseEnd_5994939 : Nat := 3078285201384225507292283

theorem tailTrace_5994939 : CollatzResearch.WordTrace tailWord_5994939 prefixEnd_5994939 3078285201384225507292283 := by
  unfold tailWord_5994939
  simp only [CollatzResearch.WordTrace]
  refine ⟨218653388428367331913123871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145768925618911554608749247 218653388428367331913123871)
  ·
    refine ⟨327980082642550997869685807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218653388428367331913123871 327980082642550997869685807)
    ·
      refine ⟨491970123963826496804528711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327980082642550997869685807 491970123963826496804528711)
      ·
        refine ⟨737955185945739745206793067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491970123963826496804528711 737955185945739745206793067)
        ·
          refine ⟨1106932778918609617810189601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737955185945739745206793067 1106932778918609617810189601)
          ·
            refine ⟨830199584188957213357642201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106932778918609617810189601 830199584188957213357642201)
            ·
              refine ⟨622649688141717910018231651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830199584188957213357642201 622649688141717910018231651)
              ·
                refine ⟨933974532212576865027347477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622649688141717910018231651 933974532212576865027347477)
                ·
                  refine ⟨43780056197464540548156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 933974532212576865027347477 43780056197464540548156913)
                  ·
                    refine ⟨32835042148098405411117685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43780056197464540548156913 32835042148098405411117685)
                    ·
                      refine ⟨3078285201384225507292283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32835042148098405411117685 3078285201384225507292283)
                      ·
                        rfl

theorem cell23_5994939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_5994939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994939 prefixEnd_5994939 := by exact prefixLift 5994939
  have htrace : WordTrace (prefixWord ++ tailWord_5994939) baseStart_5994939 baseEnd_5994939 := by
    simpa [prefixWord, tailWord_5994939, baseEnd_5994939] using wordTrace_append hprefix tailTrace_5994939
  have hstable : (prefixWord ++ tailWord_5994939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994939).length < 2 ^ (prefixWord ++ tailWord_5994939).sum := by decide
  have hdescent : baseEnd_5994939 < baseStart_5994939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994953 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 3, 3, 2]
def baseStart_5994953 : Nat := 118140960795 + 5994953 * 2 ^ 59
def prefixEnd_5994953 : Nat := 4983230072969 + 3 ^ 40 * 5994953 * 2
def baseEnd_5994953 : Nat := 3078292390113388452517219

theorem tailTrace_5994953 : CollatzResearch.WordTrace tailWord_5994953 prefixEnd_5994953 3078292390113388452517219 := by
  unfold tailWord_5994953
  simp only [CollatzResearch.WordTrace]
  refine ⟨218653899050316612304133513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145769266033544408202755675 218653899050316612304133513)
  ·
    refine ⟨163990424287737459228100135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218653899050316612304133513 163990424287737459228100135)
    ·
      refine ⟨245985636431606188842150203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163990424287737459228100135 245985636431606188842150203)
      ·
        refine ⟨368978454647409283263225305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245985636431606188842150203 368978454647409283263225305)
        ·
          refine ⟨276733840985556962447418979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368978454647409283263225305 276733840985556962447418979)
          ·
            refine ⟨415100761478335443671128469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276733840985556962447418979 415100761478335443671128469)
            ·
              refine ⟨19457848194296973922084147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 415100761478335443671128469 19457848194296973922084147)
              ·
                refine ⟨29186772291445460883126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19457848194296973922084147 29186772291445460883126221)
                ·
                  refine ⟨10945039609292047831172333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29186772291445460883126221 10945039609292047831172333)
                  ·
                    refine ⟨4104389853484517936689625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10945039609292047831172333 4104389853484517936689625)
                    ·
                      refine ⟨3078292390113388452517219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104389853484517936689625 3078292390113388452517219)
                      ·
                        rfl

theorem cell23_5994953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3, 2].length) (baseStart_5994953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994953 prefixEnd_5994953 := by exact prefixLift 5994953
  have htrace : WordTrace (prefixWord ++ tailWord_5994953) baseStart_5994953 baseEnd_5994953 := by
    simpa [prefixWord, tailWord_5994953, baseEnd_5994953] using wordTrace_append hprefix tailTrace_5994953
  have hstable : (prefixWord ++ tailWord_5994953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994953).length < 2 ^ (prefixWord ++ tailWord_5994953).sum := by decide
  have hdescent : baseEnd_5994953 < baseStart_5994953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994959 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 8]
def baseStart_5994959 : Nat := 118140960795 + 5994959 * 2 ^ 59
def prefixEnd_5994959 : Nat := 4983230072969 + 3 ^ 40 * 5994959 * 2
def baseEnd_5994959 : Nat := 1026098490332438476347397

theorem tailTrace_5994959 : CollatzResearch.WordTrace tailWord_5994959 prefixEnd_5994959 1026098490332438476347397 := by
  unfold tailWord_5994959
  simp only [CollatzResearch.WordTrace]
  refine ⟨218654117888294875328851931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145769411925529916885901287 218654117888294875328851931)
  ·
    refine ⟨327981176832442312993277897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218654117888294875328851931 327981176832442312993277897)
    ·
      refine ⟨245985882624331734744958423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327981176832442312993277897 245985882624331734744958423)
      ·
        refine ⟨368978823936497602117437635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245985882624331734744958423 368978823936497602117437635)
        ·
          refine ⟨553468235904746403176156453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368978823936497602117437635 553468235904746403176156453)
          ·
            refine ⟨103775294232139950595529335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 553468235904746403176156453 103775294232139950595529335)
            ·
              refine ⟨155662941348209925893294003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103775294232139950595529335 155662941348209925893294003)
              ·
                refine ⟨233494412022314888839941005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155662941348209925893294003 233494412022314888839941005)
                ·
                  refine ⟨87560404508368083314977877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233494412022314888839941005 87560404508368083314977877)
                  ·
                    refine ⟨1026098490332438476347397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87560404508368083314977877 1026098490332438476347397)
                    ·
                      rfl

theorem cell23_5994959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_5994959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994959 prefixEnd_5994959 := by exact prefixLift 5994959
  have htrace : WordTrace (prefixWord ++ tailWord_5994959) baseStart_5994959 baseEnd_5994959 := by
    simpa [prefixWord, tailWord_5994959, baseEnd_5994959] using wordTrace_append hprefix tailTrace_5994959
  have hstable : (prefixWord ++ tailWord_5994959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994959).length < 2 ^ (prefixWord ++ tailWord_5994959).sum := by decide
  have hdescent : baseEnd_5994959 < baseStart_5994959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994970 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_5994970 : Nat := 118140960795 + 5994970 * 2 ^ 59
def prefixEnd_5994970 : Nat := 4983230072969 + 3 ^ 40 * 5994970 * 2
def baseEnd_5994970 : Nat := 3078301119284514886004641

theorem tailTrace_5994970 : CollatzResearch.WordTrace tailWord_5994970 prefixEnd_5994970 3078301119284514886004641 := by
  unfold tailWord_5994970
  simp only [CollatzResearch.WordTrace]
  refine ⟨54663629772813756051875591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145769679394170016138334909 54663629772813756051875591)
  ·
    refine ⟨81995444659220634077813387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54663629772813756051875591 81995444659220634077813387)
    ·
      refine ⟨122993166988830951116720081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81995444659220634077813387 122993166988830951116720081)
      ·
        refine ⟨92244875241623213337540061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122993166988830951116720081 92244875241623213337540061)
        ·
          refine ⟨34591828215608705001577523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92244875241623213337540061 34591828215608705001577523)
          ·
            refine ⟨51887742323413057502366285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34591828215608705001577523 51887742323413057502366285)
            ·
              refine ⟨19457903371279896563387357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51887742323413057502366285 19457903371279896563387357)
              ·
                refine ⟨7296713764229961211270259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19457903371279896563387357 7296713764229961211270259)
                ·
                  refine ⟨10945070646344941816905389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296713764229961211270259 10945070646344941816905389)
                  ·
                    refine ⟨4104401492379353181339521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10945070646344941816905389 4104401492379353181339521)
                    ·
                      refine ⟨3078301119284514886004641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104401492379353181339521 3078301119284514886004641)
                      ·
                        rfl

theorem cell23_5994970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_5994970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994970 prefixEnd_5994970 := by exact prefixLift 5994970
  have htrace : WordTrace (prefixWord ++ tailWord_5994970) baseStart_5994970 baseEnd_5994970 := by
    simpa [prefixWord, tailWord_5994970, baseEnd_5994970] using wordTrace_append hprefix tailTrace_5994970
  have hstable : (prefixWord ++ tailWord_5994970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994970).length < 2 ^ (prefixWord ++ tailWord_5994970).sum := by decide
  have hdescent : baseEnd_5994970 < baseStart_5994970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994994 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5994994 : Nat := 118140960795 + 5994994 * 2 ^ 59
def prefixEnd_5994994 : Nat := 4983230072969 + 3 ^ 40 * 5994994 * 2
def baseEnd_5994994 : Nat := 3078313442820222792104531

theorem tailTrace_5994994 : CollatzResearch.WordTrace tailWord_5994994 prefixEnd_5994994 3078313442820222792104531 := by
  unfold tailWord_5994994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54663848610792019076594009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145770262962112050870917357 54663848610792019076594009)
  ·
    refine ⟨40997886458094014307445507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54663848610792019076594009 40997886458094014307445507)
    ·
      refine ⟨61496829687141021461168261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40997886458094014307445507 61496829687141021461168261)
      ·
        refine ⟨11530655566338941523969049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61496829687141021461168261 11530655566338941523969049)
        ·
          refine ⟨8647991674754206142976787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11530655566338941523969049 8647991674754206142976787)
          ·
            refine ⟨12971987512131309214465181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647991674754206142976787 12971987512131309214465181)
            ·
              refine ⟨4864495317049240955424443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12971987512131309214465181 4864495317049240955424443)
              ·
                refine ⟨7296742975573861433136665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864495317049240955424443 7296742975573861433136665)
                ·
                  refine ⟨5472557231680396074852499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7296742975573861433136665 5472557231680396074852499)
                  ·
                    refine ⟨8208835847520594112278749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472557231680396074852499 8208835847520594112278749)
                    ·
                      refine ⟨3078313442820222792104531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8208835847520594112278749 3078313442820222792104531)
                      ·
                        rfl

theorem cell23_5994994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5994994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994994 prefixEnd_5994994 := by exact prefixLift 5994994
  have htrace : WordTrace (prefixWord ++ tailWord_5994994) baseStart_5994994 baseEnd_5994994 := by
    simpa [prefixWord, tailWord_5994994, baseEnd_5994994] using wordTrace_append hprefix tailTrace_5994994
  have hstable : (prefixWord ++ tailWord_5994994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994994).length < 2 ^ (prefixWord ++ tailWord_5994994).sum := by decide
  have hdescent : baseEnd_5994994 < baseStart_5994994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995040 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 7]
def baseStart_5995040 : Nat := 118140960795 + 5995040 * 2 ^ 59
def prefixEnd_5995040 : Nat := 4983230072969 + 3 ^ 40 * 5995040 * 2
def baseEnd_5995040 : Nat := 342037451436703290236591

theorem tailTrace_5995040 : CollatzResearch.WordTrace tailWord_5995040 prefixEnd_5995040 342037451436703290236591 := by
  unfold tailWord_5995040
  simp only [CollatzResearch.WordTrace]
  refine ⟨109328536100500713081275287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145771381467334284108367049 109328536100500713081275287)
  ·
    refine ⟨163992804150751069621912931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109328536100500713081275287 163992804150751069621912931)
    ·
      refine ⟨245989206226126604432869397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163992804150751069621912931 245989206226126604432869397)
      ·
        refine ⟨11530744041849684582790753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245989206226126604432869397 11530744041849684582790753)
        ·
          refine ⟨8648058031387263437093065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11530744041849684582790753 8648058031387263437093065)
          ·
            refine ⟨6486043523540447577819799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8648058031387263437093065 6486043523540447577819799)
            ·
              refine ⟨9729065285310671366729699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486043523540447577819799 9729065285310671366729699)
              ·
                refine ⟨14593597927966007050094549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729065285310671366729699 14593597927966007050094549)
                ·
                  refine ⟨342037451436703290236591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14593597927966007050094549 342037451436703290236591)
                  ·
                    rfl

theorem cell23_5995040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_5995040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995040 prefixEnd_5995040 := by exact prefixLift 5995040
  have htrace : WordTrace (prefixWord ++ tailWord_5995040) baseStart_5995040 baseEnd_5995040 := by
    simpa [prefixWord, tailWord_5995040, baseEnd_5995040] using wordTrace_append hprefix tailTrace_5995040
  have hstable : (prefixWord ++ tailWord_5995040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995040).length < 2 ^ (prefixWord ++ tailWord_5995040).sum := by decide
  have hdescent : baseEnd_5995040 < baseStart_5995040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995056 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_5995056 : Nat := 118140960795 + 5995056 * 2 ^ 59
def prefixEnd_5995056 : Nat := 4983230072969 + 3 ^ 40 * 5995056 * 2
def baseEnd_5995056 : Nat := 3078345278620801549529245

theorem tailTrace_5995056 : CollatzResearch.WordTrace tailWord_5995056 prefixEnd_5995056 3078345278620801549529245 := by
  unfold tailWord_5995056
  simp only [CollatzResearch.WordTrace]
  refine ⟨109328827884471730447566511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145771770512628973930088681 109328827884471730447566511)
  ·
    refine ⟨163993241826707595671349767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109328827884471730447566511 163993241826707595671349767)
    ·
      refine ⟨245989862740061393507024651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163993241826707595671349767 245989862740061393507024651)
      ·
        refine ⟨368984794110092090260536977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245989862740061393507024651 368984794110092090260536977)
        ·
          refine ⟨276738595582569067695402733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368984794110092090260536977 276738595582569067695402733)
          ·
            refine ⟨103776973343463400385776025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276738595582569067695402733 103776973343463400385776025)
            ·
              refine ⟨77832730007597550289332019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103776973343463400385776025 77832730007597550289332019)
              ·
                refine ⟨116749095011396325433998029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77832730007597550289332019 116749095011396325433998029)
                ·
                  refine ⟨43780910629273622037749261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116749095011396325433998029 43780910629273622037749261)
                  ·
                    refine ⟨16417841485977608264155973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43780910629273622037749261 16417841485977608264155973)
                    ·
                      refine ⟨3078345278620801549529245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16417841485977608264155973 3078345278620801549529245)
                      ·
                        rfl

theorem cell23_5995056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_5995056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995056 prefixEnd_5995056 := by exact prefixLift 5995056
  have htrace : WordTrace (prefixWord ++ tailWord_5995056) baseStart_5995056 baseEnd_5995056 := by
    simpa [prefixWord, tailWord_5995056, baseEnd_5995056] using wordTrace_append hprefix tailTrace_5995056
  have hstable : (prefixWord ++ tailWord_5995056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995056).length < 2 ^ (prefixWord ++ tailWord_5995056).sum := by decide
  have hdescent : baseEnd_5995056 < baseStart_5995056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995090 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_5995090 : Nat := 118140960795 + 5995090 * 2 ^ 59
def prefixEnd_5995090 : Nat := 4983230072969 + 3 ^ 40 * 5995090 * 2
def baseEnd_5995090 : Nat := 3078362736963054416504089

theorem tailTrace_5995090 : CollatzResearch.WordTrace tailWord_5995090 prefixEnd_5995090 3078362736963054416504089 := by
  unfold tailWord_5995090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664723962705071175467681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145772597233880189801247149 54664723962705071175467681)
  ·
    refine ⟨40998542972028803381600761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54664723962705071175467681 40998542972028803381600761)
    ·
      refine ⟨30748907229021602536200571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40998542972028803381600761 30748907229021602536200571)
      ·
        refine ⟨46123360843532403804300857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30748907229021602536200571 46123360843532403804300857)
        ·
          refine ⟨34592520632649302853225643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46123360843532403804300857 34592520632649302853225643)
          ·
            refine ⟨51888780948973954279838465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34592520632649302853225643 51888780948973954279838465)
            ·
              refine ⟨38916585711730465709878849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51888780948973954279838465 38916585711730465709878849)
              ·
                refine ⟨29187439283797849282409137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38916585711730465709878849 29187439283797849282409137)
                ·
                  refine ⟨21890579462848386961806853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29187439283797849282409137 21890579462848386961806853)
                  ·
                    refine ⟨4104483649284072555338785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21890579462848386961806853 4104483649284072555338785)
                    ·
                      refine ⟨3078362736963054416504089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104483649284072555338785 3078362736963054416504089)
                      ·
                        rfl

theorem cell23_5995090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_5995090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995090 prefixEnd_5995090 := by exact prefixLift 5995090
  have htrace : WordTrace (prefixWord ++ tailWord_5995090) baseStart_5995090 baseEnd_5995090 := by
    simpa [prefixWord, tailWord_5995090, baseEnd_5995090] using wordTrace_append hprefix tailTrace_5995090
  have hstable : (prefixWord ++ tailWord_5995090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995090).length < 2 ^ (prefixWord ++ tailWord_5995090).sum := by decide
  have hdescent : baseEnd_5995090 < baseStart_5995090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995096 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 8]
def baseStart_5995096 : Nat := 118140960795 + 5995096 * 2 ^ 59
def prefixEnd_5995096 : Nat := 4983230072969 + 3 ^ 40 * 5995096 * 2
def baseEnd_5995096 : Nat := 342040646427442377003229

theorem tailTrace_5995096 : CollatzResearch.WordTrace tailWord_5995096 prefixEnd_5995096 342040646427442377003229 := by
  unfold tailWord_5995096
  simp only [CollatzResearch.WordTrace]
  refine ⟨109329557344399273863294571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145772743125865698484392761 109329557344399273863294571)
  ·
    refine ⟨163994336016598910794941857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109329557344399273863294571 163994336016598910794941857)
    ·
      refine ⟨122995752012449183096206393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163994336016598910794941857 122995752012449183096206393)
      ·
        refine ⟨92246814009336887322154795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122995752012449183096206393 92246814009336887322154795)
        ·
          refine ⟨138370221014005330983232193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92246814009336887322154795 138370221014005330983232193)
          ·
            refine ⟨103777665760503998237424145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138370221014005330983232193 103777665760503998237424145)
            ·
              refine ⟨77833249320377998678068109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103777665760503998237424145 77833249320377998678068109)
              ·
                refine ⟨29187468495141749504275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77833249320377998678068109 29187468495141749504275541)
                ·
                  refine ⟨342040646427442377003229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29187468495141749504275541 342040646427442377003229)
                  ·
                    rfl

theorem cell23_5995096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_5995096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995096 prefixEnd_5995096 := by exact prefixLift 5995096
  have htrace : WordTrace (prefixWord ++ tailWord_5995096) baseStart_5995096 baseEnd_5995096 := by
    simpa [prefixWord, tailWord_5995096, baseEnd_5995096] using wordTrace_append hprefix tailTrace_5995096
  have hstable : (prefixWord ++ tailWord_5995096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995096).length < 2 ^ (prefixWord ++ tailWord_5995096).sum := by decide
  have hdescent : baseEnd_5995096 < baseStart_5995096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995191 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_5995191 : Nat := 118140960795 + 5995191 * 2 ^ 59
def prefixEnd_5995191 : Nat := 4983230072969 + 3 ^ 40 * 5995191 * 2
def baseEnd_5995191 : Nat := 3078414598509158521341125

theorem tailTrace_5995191 : CollatzResearch.WordTrace tailWord_5995191 prefixEnd_5995191 3078414598509158521341125 := by
  unfold tailWord_5995191
  simp only [CollatzResearch.WordTrace]
  refine ⟨218662579623454378951297427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145775053082302919300864951 218662579623454378951297427)
  ·
    refine ⟨327993869435181568426946141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218662579623454378951297427 327993869435181568426946141)
    ·
      refine ⟨122997701038193088160104803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327993869435181568426946141 122997701038193088160104803)
      ·
        refine ⟨184496551557289632240157205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122997701038193088160104803 184496551557289632240157205)
        ·
          refine ⟨8648275854247951511257369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184496551557289632240157205 8648275854247951511257369)
          ·
            refine ⟨6486206890685963633443027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8648275854247951511257369 6486206890685963633443027)
            ·
              refine ⟨9729310336028945450164541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486206890685963633443027 9729310336028945450164541)
              ·
                refine ⟨3648491376010854543811703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9729310336028945450164541 3648491376010854543811703)
                ·
                  refine ⟨5472737064016281815717555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648491376010854543811703 5472737064016281815717555)
                  ·
                    refine ⟨8209105596024422723576333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472737064016281815717555 8209105596024422723576333)
                    ·
                      refine ⟨3078414598509158521341125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8209105596024422723576333 3078414598509158521341125)
                      ·
                        rfl

theorem cell23_5995191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_5995191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995191 prefixEnd_5995191 := by exact prefixLift 5995191
  have htrace : WordTrace (prefixWord ++ tailWord_5995191) baseStart_5995191 baseEnd_5995191 := by
    simpa [prefixWord, tailWord_5995191, baseEnd_5995191] using wordTrace_append hprefix tailTrace_5995191
  have hstable : (prefixWord ++ tailWord_5995191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995191).length < 2 ^ (prefixWord ++ tailWord_5995191).sum := by decide
  have hdescent : baseEnd_5995191 < baseStart_5995191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995193 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5995193 : Nat := 118140960795 + 5995193 * 2 ^ 59
def prefixEnd_5995193 : Nat := 4983230072969 + 3 ^ 40 * 5995193 * 2
def baseEnd_5995193 : Nat := 3078415625470467513516115

theorem tailTrace_5995193 : CollatzResearch.WordTrace tailWord_5995193 prefixEnd_5995193 3078415625470467513516115 := by
  unfold tailWord_5995193
  simp only [CollatzResearch.WordTrace]
  refine ⟨218662652569447133292870233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145775101712964755528580155 218662652569447133292870233)
  ·
    refine ⟨163996989427085349969652675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218662652569447133292870233 163996989427085349969652675)
    ·
      refine ⟨245995484140628024954479013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163996989427085349969652675 245995484140628024954479013)
      ·
        refine ⟨46124153276367754678964815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245995484140628024954479013 46124153276367754678964815)
        ·
          refine ⟨69186229914551632018447223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46124153276367754678964815 69186229914551632018447223)
          ·
            refine ⟨103779344871827448027670835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69186229914551632018447223 103779344871827448027670835)
            ·
              refine ⟨155669017307741172041506253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103779344871827448027670835 155669017307741172041506253)
              ·
                refine ⟨58375881490402939515564845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155669017307741172041506253 58375881490402939515564845)
                ·
                  refine ⟨21890955558901102318336817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58375881490402939515564845 21890955558901102318336817)
                  ·
                    refine ⟨16418216669175826738752613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21890955558901102318336817 16418216669175826738752613)
                    ·
                      refine ⟨3078415625470467513516115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16418216669175826738752613 3078415625470467513516115)
                      ·
                        rfl

theorem cell23_5995193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5995193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995193 prefixEnd_5995193 := by exact prefixLift 5995193
  have htrace : WordTrace (prefixWord ++ tailWord_5995193) baseStart_5995193 baseEnd_5995193 := by
    simpa [prefixWord, tailWord_5995193, baseEnd_5995193] using wordTrace_append hprefix tailTrace_5995193
  have hstable : (prefixWord ++ tailWord_5995193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995193).length < 2 ^ (prefixWord ++ tailWord_5995193).sum := by decide
  have hdescent : baseEnd_5995193 < baseStart_5995193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995200 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_5995200 : Nat := 118140960795 + 5995200 * 2 ^ 59
def prefixEnd_5995200 : Nat := 4983230072969 + 3 ^ 40 * 5995200 * 2
def baseEnd_5995200 : Nat := 3078419219835048986128583

theorem tailTrace_5995200 : CollatzResearch.WordTrace tailWord_5995200 prefixEnd_5995200 3078419219835048986128583 := by
  unfold tailWord_5995200
  simp only [CollatzResearch.WordTrace]
  refine ⟨109331453940210886744187527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145775271920281182325583369 109331453940210886744187527)
  ·
    refine ⟨163997180910316330116281291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109331453940210886744187527 163997180910316330116281291)
    ·
      refine ⟨245995771365474495174421937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163997180910316330116281291 245995771365474495174421937)
      ·
        refine ⟨184496828524105871380816453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245995771365474495174421937 184496828524105871380816453)
        ·
          refine ⟨34593155348269850883903085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184496828524105871380816453 34593155348269850883903085)
          ·
            refine ⟨12972433255601194081463657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34593155348269850883903085 12972433255601194081463657)
            ·
              refine ⟨9729324941700895561097743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12972433255601194081463657 9729324941700895561097743)
              ·
                refine ⟨14593987412551343341646615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729324941700895561097743 14593987412551343341646615)
                ·
                  refine ⟨21890981118827015012469923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14593987412551343341646615 21890981118827015012469923)
                  ·
                    refine ⟨32836471678240522518704885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21890981118827015012469923 32836471678240522518704885)
                    ·
                      refine ⟨3078419219835048986128583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32836471678240522518704885 3078419219835048986128583)
                      ·
                        rfl

theorem cell23_5995200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_5995200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995200 prefixEnd_5995200 := by exact prefixLift 5995200
  have htrace : WordTrace (prefixWord ++ tailWord_5995200) baseStart_5995200 baseEnd_5995200 := by
    simpa [prefixWord, tailWord_5995200, baseEnd_5995200] using wordTrace_append hprefix tailTrace_5995200
  have hstable : (prefixWord ++ tailWord_5995200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995200).length < 2 ^ (prefixWord ++ tailWord_5995200).sum := by decide
  have hdescent : baseEnd_5995200 < baseStart_5995200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995201 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5995201 : Nat := 118140960795 + 5995201 * 2 ^ 59
def prefixEnd_5995201 : Nat := 4983230072969 + 3 ^ 40 * 5995201 * 2
def baseEnd_5995201 : Nat := 3078419733315703482216079

theorem tailTrace_5995201 : CollatzResearch.WordTrace tailWord_5995201 prefixEnd_5995201 3078419733315703482216079 := by
  unfold tailWord_5995201
  simp only [CollatzResearch.WordTrace]
  refine ⟨218662944353418150659161457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145775296235612100439440971 218662944353418150659161457)
  ·
    refine ⟨163997208265063612994371093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218662944353418150659161457 163997208265063612994371093)
    ·
      refine ⟨7687369137424856859111145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163997208265063612994371093 7687369137424856859111145)
      ·
        refine ⟨5765526853068642644333359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687369137424856859111145 5765526853068642644333359)
        ·
          refine ⟨8648290279602963966500039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765526853068642644333359 8648290279602963966500039)
          ·
            refine ⟨12972435419404445949750059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648290279602963966500039 12972435419404445949750059)
            ·
              refine ⟨19458653129106668924625089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12972435419404445949750059 19458653129106668924625089)
              ·
                refine ⟨14593989846830001693468817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19458653129106668924625089 14593989846830001693468817)
                ·
                  refine ⟨10945492385122501270101613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14593989846830001693468817 10945492385122501270101613)
                  ·
                    refine ⟨4104559644420937976288105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10945492385122501270101613 4104559644420937976288105)
                    ·
                      refine ⟨3078419733315703482216079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104559644420937976288105 3078419733315703482216079)
                      ·
                        rfl

theorem cell23_5995201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5995201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995201 prefixEnd_5995201 := by exact prefixLift 5995201
  have htrace : WordTrace (prefixWord ++ tailWord_5995201) baseStart_5995201 baseEnd_5995201 := by
    simpa [prefixWord, tailWord_5995201, baseEnd_5995201] using wordTrace_append hprefix tailTrace_5995201
  have hstable : (prefixWord ++ tailWord_5995201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995201).length < 2 ^ (prefixWord ++ tailWord_5995201).sum := by decide
  have hdescent : baseEnd_5995201 < baseStart_5995201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995214 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_5995214 : Nat := 118140960795 + 5995214 * 2 ^ 59
def prefixEnd_5995214 : Nat := 4983230072969 + 3 ^ 40 * 5995214 * 2
def baseEnd_5995214 : Nat := 3078426408564211931353519

theorem tailTrace_5995214 : CollatzResearch.WordTrace tailWord_5995214 prefixEnd_5995214 3078426408564211931353519 := by
  unfold tailWord_5995214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27332927312796381734923087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145775612334914035919589797 27332927312796381734923087)
  ·
    refine ⟨40999390969194572602384631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27332927312796381734923087 40999390969194572602384631)
    ·
      refine ⟨61499086453791858903576947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40999390969194572602384631 61499086453791858903576947)
      ·
        refine ⟨92248629680687788355365421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61499086453791858903576947 92248629680687788355365421)
        ·
          refine ⟨34593236130257920633262033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92248629680687788355365421 34593236130257920633262033)
          ·
            refine ⟨25944927097693440474946525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34593236130257920633262033 25944927097693440474946525)
            ·
              refine ⟨9729347661635040178104947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25944927097693440474946525 9729347661635040178104947)
              ·
                refine ⟨14594021492452560267157421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729347661635040178104947 14594021492452560267157421)
                ·
                  refine ⟨5472758059669710100184033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594021492452560267157421 5472758059669710100184033)
                  ·
                    refine ⟨4104568544752282575138025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472758059669710100184033 4104568544752282575138025)
                    ·
                      refine ⟨3078426408564211931353519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104568544752282575138025 3078426408564211931353519)
                      ·
                        rfl

theorem cell23_5995214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_5995214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995214 prefixEnd_5995214 := by exact prefixLift 5995214
  have htrace : WordTrace (prefixWord ++ tailWord_5995214) baseStart_5995214 baseEnd_5995214 := by
    simpa [prefixWord, tailWord_5995214, baseEnd_5995214] using wordTrace_append hprefix tailTrace_5995214
  have hstable : (prefixWord ++ tailWord_5995214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995214).length < 2 ^ (prefixWord ++ tailWord_5995214).sum := by decide
  have hdescent : baseEnd_5995214 < baseStart_5995214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995224 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_5995224 : Nat := 118140960795 + 5995224 * 2 ^ 59
def prefixEnd_5995224 : Nat := 4983230072969 + 3 ^ 40 * 5995224 * 2
def baseEnd_5995224 : Nat := 1026143847790252297409491

theorem tailTrace_5995224 : CollatzResearch.WordTrace tailWord_5995224 prefixEnd_5995224 1026143847790252297409491 := by
  unfold tailWord_5995224
  simp only [CollatzResearch.WordTrace]
  refine ⟨109331891616167412793624363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145775855488223217058165817 109331891616167412793624363)
  ·
    refine ⟨163997837424251119190436545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109331891616167412793624363 163997837424251119190436545)
    ·
      refine ⟨122998378068188339392827409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163997837424251119190436545 122998378068188339392827409)
      ·
        refine ⟨92248783551141254544620557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122998378068188339392827409 92248783551141254544620557)
        ·
          refine ⟨34593293831677970454232709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92248783551141254544620557 34593293831677970454232709)
          ·
            refine ⟨6486242593439619460168633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34593293831677970454232709 6486242593439619460168633)
            ·
              refine ⟨4864681945079714595126475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486242593439619460168633 4864681945079714595126475)
              ·
                refine ⟨7297022917619571892689713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864681945079714595126475 7297022917619571892689713)
                ·
                  refine ⟨5472767188214678919517285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297022917619571892689713 5472767188214678919517285)
                  ·
                    refine ⟨1026143847790252297409491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472767188214678919517285 1026143847790252297409491)
                    ·
                      rfl

theorem cell23_5995224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_5995224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995224 prefixEnd_5995224 := by exact prefixLift 5995224
  have htrace : WordTrace (prefixWord ++ tailWord_5995224) baseStart_5995224 baseEnd_5995224 := by
    simpa [prefixWord, tailWord_5995224, baseEnd_5995224] using wordTrace_append hprefix tailTrace_5995224
  have hstable : (prefixWord ++ tailWord_5995224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995224).length < 2 ^ (prefixWord ++ tailWord_5995224).sum := by decide
  have hdescent : baseEnd_5995224 < baseStart_5995224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995257 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 1, 3, 2]
def baseStart_5995257 : Nat := 118140960795 + 5995257 * 2 ^ 59
def prefixEnd_5995257 : Nat := 4983230072969 + 3 ^ 40 * 5995257 * 2
def baseEnd_5995257 : Nat := 3078448488232355263115821

theorem tailTrace_5995257 : CollatzResearch.WordTrace tailWord_5995257 prefixEnd_5995257 3078448488232355263115821 := by
  unfold tailWord_5995257
  simp only [CollatzResearch.WordTrace]
  refine ⟨218664986841215272223200025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145776657894143514815466683 218664986841215272223200025)
  ·
    refine ⟨163998740130911454167400019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218664986841215272223200025 163998740130911454167400019)
    ·
      refine ⟨245998110196367181251100029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163998740130911454167400019 245998110196367181251100029)
      ·
        refine ⟨92249291323637692969162511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245998110196367181251100029 92249291323637692969162511)
        ·
          refine ⟨138373936985456539453743767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92249291323637692969162511 138373936985456539453743767)
          ·
            refine ⟨207560905478184809180615651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138373936985456539453743767 207560905478184809180615651)
            ·
              refine ⟨311341358217277213770923477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207560905478184809180615651 311341358217277213770923477)
              ·
                refine ⟨7297063083217434697756019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 311341358217277213770923477 7297063083217434697756019)
                ·
                  refine ⟨10945594624826152046634029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297063083217434697756019 10945594624826152046634029)
                  ·
                    refine ⟨4104597984309807017487761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10945594624826152046634029 4104597984309807017487761)
                    ·
                      refine ⟨3078448488232355263115821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104597984309807017487761 3078448488232355263115821)
                      ·
                        rfl

theorem cell23_5995257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_5995257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995257 prefixEnd_5995257 := by exact prefixLift 5995257
  have htrace : WordTrace (prefixWord ++ tailWord_5995257) baseStart_5995257 baseEnd_5995257 := by
    simpa [prefixWord, tailWord_5995257, baseEnd_5995257] using wordTrace_append hprefix tailTrace_5995257
  have hstable : (prefixWord ++ tailWord_5995257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995257).length < 2 ^ (prefixWord ++ tailWord_5995257).sum := by decide
  have hdescent : baseEnd_5995257 < baseStart_5995257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995263 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 6]
def baseStart_5995263 : Nat := 118140960795 + 5995263 * 2 ^ 59
def prefixEnd_5995263 : Nat := 4983230072969 + 3 ^ 40 * 5995263 * 2
def baseEnd_5995263 : Nat := 1026150523038760746546931

theorem tailTrace_5995263 : CollatzResearch.WordTrace tailWord_5995263 prefixEnd_5995263 1026150523038760746546931 := by
  unfold tailWord_5995263
  simp only [CollatzResearch.WordTrace]
  refine ⟨218665205679193535247918443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145776803786129023498612295 218665205679193535247918443)
  ·
    refine ⟨327997808518790302871877665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218665205679193535247918443 327997808518790302871877665)
    ·
      refine ⟨245998356389092727153908249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327997808518790302871877665 245998356389092727153908249)
      ·
        refine ⟨184498767291819545365431187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245998356389092727153908249 184498767291819545365431187)
        ·
          refine ⟨276748150937729318048146781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184498767291819545365431187 276748150937729318048146781)
          ·
            refine ⟨103780556601648494268055043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276748150937729318048146781 103780556601648494268055043)
            ·
              refine ⟨155670834902472741402082565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103780556601648494268055043 155670834902472741402082565)
              ·
                refine ⟨29188281544213639012890481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155670834902472741402082565 29188281544213639012890481)
                ·
                  refine ⟨21891211158160229259667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29188281544213639012890481 21891211158160229259667861)
                  ·
                    refine ⟨1026150523038760746546931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21891211158160229259667861 1026150523038760746546931)
                    ·
                      rfl

theorem cell23_5995263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_5995263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995263 prefixEnd_5995263 := by exact prefixLift 5995263
  have htrace : WordTrace (prefixWord ++ tailWord_5995263) baseStart_5995263 baseEnd_5995263 := by
    simpa [prefixWord, tailWord_5995263, baseEnd_5995263] using wordTrace_append hprefix tailTrace_5995263
  have hstable : (prefixWord ++ tailWord_5995263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995263).length < 2 ^ (prefixWord ++ tailWord_5995263).sum := by decide
  have hdescent : baseEnd_5995263 < baseStart_5995263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995273 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_5995273 : Nat := 118140960795 + 5995273 * 2 ^ 59
def prefixEnd_5995273 : Nat := 4983230072969 + 3 ^ 40 * 5995273 * 2
def baseEnd_5995273 : Nat := 3078456703922827200515747

theorem tailTrace_5995273 : CollatzResearch.WordTrace tailWord_5995273 prefixEnd_5995273 3078456703922827200515747 := by
  unfold tailWord_5995273
  simp only [CollatzResearch.WordTrace]
  refine ⟨218665570409157306955782473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145777046939438204637188315 218665570409157306955782473)
  ·
    refine ⟨163999177806867980216836855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218665570409157306955782473 163999177806867980216836855)
    ·
      refine ⟨245998766710301970325255283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163999177806867980216836855 245998766710301970325255283)
      ·
        refine ⟨368998150065452955487882925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245998766710301970325255283 368998150065452955487882925)
        ·
          refine ⟨138374306274544858307956097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368998150065452955487882925 138374306274544858307956097)
          ·
            refine ⟨103780729705908643730967073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138374306274544858307956097 103780729705908643730967073)
            ·
              refine ⟨77835547279431482798225305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103780729705908643730967073 77835547279431482798225305)
              ·
                refine ⟨58376660459573612098668979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77835547279431482798225305 58376660459573612098668979)
                ·
                  refine ⟨87564990689360418148003469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58376660459573612098668979 87564990689360418148003469)
                  ·
                    refine ⟨32836871508510156805501301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87564990689360418148003469 32836871508510156805501301)
                    ·
                      refine ⟨3078456703922827200515747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32836871508510156805501301 3078456703922827200515747)
                      ·
                        rfl

theorem cell23_5995273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_5995273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995273 prefixEnd_5995273 := by exact prefixLift 5995273
  have htrace : WordTrace (prefixWord ++ tailWord_5995273) baseStart_5995273 baseEnd_5995273 := by
    simpa [prefixWord, tailWord_5995273, baseEnd_5995273] using wordTrace_append hprefix tailTrace_5995273
  have hstable : (prefixWord ++ tailWord_5995273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995273).length < 2 ^ (prefixWord ++ tailWord_5995273).sum := by decide
  have hdescent : baseEnd_5995273 < baseStart_5995273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995290 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_5995290 : Nat := 118140960795 + 5995290 * 2 ^ 59
def prefixEnd_5995290 : Nat := 4983230072969 + 3 ^ 40 * 5995290 * 2
def baseEnd_5995290 : Nat := 3078465433093953634003169

theorem tailTrace_5995290 : CollatzResearch.WordTrace tailWord_5995290 prefixEnd_5995290 3078465433093953634003169 := by
  unfold tailWord_5995290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666547612523929714787831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145777460300063812572767549 54666547612523929714787831)
  ·
    refine ⟨81999821418785894572181747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54666547612523929714787831 81999821418785894572181747)
    ·
      refine ⟨122999732128178841858272621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81999821418785894572181747 122999732128178841858272621)
      ·
        refine ⟨46124899548067065696852233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122999732128178841858272621 46124899548067065696852233)
        ·
          refine ⟨34593674661050299272639175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46124899548067065696852233 34593674661050299272639175)
          ·
            refine ⟨51890511991575448908958763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34593674661050299272639175 51890511991575448908958763)
            ·
              refine ⟨77835767987363173363438145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51890511991575448908958763 77835767987363173363438145)
              ·
                refine ⟨58376825990522380022578609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77835767987363173363438145 58376825990522380022578609)
                ·
                  refine ⟨43782619492891785016933957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58376825990522380022578609 43782619492891785016933957)
                  ·
                    refine ⟨8209241154917209690675117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43782619492891785016933957 8209241154917209690675117)
                    ·
                      refine ⟨3078465433093953634003169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8209241154917209690675117 3078465433093953634003169)
                      ·
                        rfl

theorem cell23_5995290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_5995290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995290 prefixEnd_5995290 := by exact prefixLift 5995290
  have htrace : WordTrace (prefixWord ++ tailWord_5995290) baseStart_5995290 baseEnd_5995290 := by
    simpa [prefixWord, tailWord_5995290, baseEnd_5995290] using wordTrace_append hprefix tailTrace_5995290
  have hstable : (prefixWord ++ tailWord_5995290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995290).length < 2 ^ (prefixWord ++ tailWord_5995290).sum := by decide
  have hdescent : baseEnd_5995290 < baseStart_5995290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995304 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5995304 : Nat := 118140960795 + 5995304 * 2 ^ 59
def prefixEnd_5995304 : Nat := 4983230072969 + 3 ^ 40 * 5995304 * 2
def baseEnd_5995304 : Nat := 3078472621823116579228105

theorem tailTrace_5995304 : CollatzResearch.WordTrace tailWord_5995304 prefixEnd_5995304 3078472621823116579228105 := by
  unfold tailWord_5995304
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333350536022499625080483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145777800714696666166773977 109333350536022499625080483)
  ·
    refine ⟨164000025804033749437620725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109333350536022499625080483 164000025804033749437620725)
    ·
      refine ⟨15375002419128164009776943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164000025804033749437620725 15375002419128164009776943)
      ·
        refine ⟨23062503628692246014665415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15375002419128164009776943 23062503628692246014665415)
        ·
          refine ⟨34593755443038369021998123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23062503628692246014665415 34593755443038369021998123)
          ·
            refine ⟨51890633164557553532997185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34593755443038369021998123 51890633164557553532997185)
            ·
              refine ⟨38917974873418165149747889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51890633164557553532997185 38917974873418165149747889)
              ·
                refine ⟨29188481155063623862310917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38917974873418165149747889 29188481155063623862310917)
                ·
                  refine ⟨5472840216574429474183297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29188481155063623862310917 5472840216574429474183297)
                  ·
                    refine ⟨4104630162430822105637473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472840216574429474183297 4104630162430822105637473)
                    ·
                      refine ⟨3078472621823116579228105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104630162430822105637473 3078472621823116579228105)
                      ·
                        rfl

theorem cell23_5995304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5995304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995304 prefixEnd_5995304 := by exact prefixLift 5995304
  have htrace : WordTrace (prefixWord ++ tailWord_5995304) baseStart_5995304 baseEnd_5995304 := by
    simpa [prefixWord, tailWord_5995304, baseEnd_5995304] using wordTrace_append hprefix tailTrace_5995304
  have hstable : (prefixWord ++ tailWord_5995304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995304).length < 2 ^ (prefixWord ++ tailWord_5995304).sum := by decide
  have hdescent : baseEnd_5995304 < baseStart_5995304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995320 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_5995320 : Nat := 118140960795 + 5995320 * 2 ^ 59
def prefixEnd_5995320 : Nat := 4983230072969 + 3 ^ 40 * 5995320 * 2
def baseEnd_5995320 : Nat := 3078480837513588516628031

theorem tailTrace_5995320 : CollatzResearch.WordTrace tailWord_5995320 prefixEnd_5995320 3078480837513588516628031 := by
  unfold tailWord_5995320
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333642319993516991371707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145778189759991355988495609 109333642319993516991371707)
  ·
    refine ⟨164000463479990275487057561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109333642319993516991371707 164000463479990275487057561)
    ·
      refine ⟨123000347609992706615293171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164000463479990275487057561 123000347609992706615293171)
      ·
        refine ⟨184500521414989059922939757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123000347609992706615293171 184500521414989059922939757)
        ·
          refine ⟨69187695530620897471102409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184500521414989059922939757 69187695530620897471102409)
          ·
            refine ⟨51890771647965673103326807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69187695530620897471102409 51890771647965673103326807)
            ·
              refine ⟨77836157471948509654990211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51890771647965673103326807 77836157471948509654990211)
              ·
                refine ⟨116754236207922764482485317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77836157471948509654990211 116754236207922764482485317)
                ·
                  refine ⟨21891419288985518340465997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116754236207922764482485317 21891419288985518340465997)
                  ·
                    refine ⟨8209282233369569377674749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21891419288985518340465997 8209282233369569377674749)
                    ·
                      refine ⟨3078480837513588516628031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8209282233369569377674749 3078480837513588516628031)
                      ·
                        rfl

theorem cell23_5995320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_5995320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995320 prefixEnd_5995320 := by exact prefixLift 5995320
  have htrace : WordTrace (prefixWord ++ tailWord_5995320) baseStart_5995320 baseEnd_5995320 := by
    simpa [prefixWord, tailWord_5995320, baseEnd_5995320] using wordTrace_append hprefix tailTrace_5995320
  have hstable : (prefixWord ++ tailWord_5995320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995320).length < 2 ^ (prefixWord ++ tailWord_5995320).sum := by decide
  have hdescent : baseEnd_5995320 < baseStart_5995320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995327 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 5]
def baseStart_5995327 : Nat := 118140960795 + 5995327 * 2 ^ 59
def prefixEnd_5995327 : Nat := 4983230072969 + 3 ^ 40 * 5995327 * 2
def baseEnd_5995327 : Nat := 342053825764241109915611

theorem tailTrace_5995327 : CollatzResearch.WordTrace tailWord_5995327 prefixEnd_5995327 342053825764241109915611 := by
  unfold tailWord_5995327
  simp only [CollatzResearch.WordTrace]
  refine ⟨218667539950961674178248235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145778359967307782785498823 218667539950961674178248235)
  ·
    refine ⟨328001309926442511267372353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218667539950961674178248235 328001309926442511267372353)
    ·
      refine ⟨246000982444831883450529265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328001309926442511267372353 246000982444831883450529265)
      ·
        refine ⟨184500736833623912587896949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246000982444831883450529265 184500736833623912587896949)
        ·
          refine ⟨17296944078152241805115339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184500736833623912587896949 17296944078152241805115339)
          ·
            refine ⟨25945416117228362707673009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17296944078152241805115339 25945416117228362707673009)
            ·
              refine ⟨19459062087921272030754757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25945416117228362707673009 19459062087921272030754757)
              ·
                refine ⟨3648574141485238505766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19459062087921272030754757 3648574141485238505766517)
                ·
                  refine ⟨342053825764241109915611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648574141485238505766517 342053825764241109915611)
                  ·
                    rfl

theorem cell23_5995327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 5].length) (baseStart_5995327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995327 prefixEnd_5995327 := by exact prefixLift 5995327
  have htrace : WordTrace (prefixWord ++ tailWord_5995327) baseStart_5995327 baseEnd_5995327 := by
    simpa [prefixWord, tailWord_5995327, baseEnd_5995327] using wordTrace_append hprefix tailTrace_5995327
  have hstable : (prefixWord ++ tailWord_5995327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995327).length < 2 ^ (prefixWord ++ tailWord_5995327).sum := by decide
  have hdescent : baseEnd_5995327 < baseStart_5995327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995340 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_5995340 : Nat := 118140960795 + 5995340 * 2 ^ 59
def prefixEnd_5995340 : Nat := 4983230072969 + 3 ^ 40 * 5995340 * 2
def baseEnd_5995340 : Nat := 1026163702375559479459313

theorem tailTrace_5995340 : CollatzResearch.WordTrace tailWord_5995340 prefixEnd_5995340 1026163702375559479459313 := by
  unfold tailWord_5995340
  simp only [CollatzResearch.WordTrace]
  refine ⟨109334007049957288699235737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145778676066609718265647649 109334007049957288699235737)
  ·
    refine ⟨82000505287467966524426803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109334007049957288699235737 82000505287467966524426803)
    ·
      refine ⟨123000757931201949786640205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82000505287467966524426803 123000757931201949786640205)
      ·
        refine ⟨46125284224200731169990077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123000757931201949786640205 46125284224200731169990077)
        ·
          refine ⟨17296981584075274188746279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46125284224200731169990077 17296981584075274188746279)
          ·
            refine ⟨25945472376112911283119419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17296981584075274188746279 25945472376112911283119419)
            ·
              refine ⟨38918208564169366924679129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25945472376112911283119419 38918208564169366924679129)
              ·
                refine ⟨29188656423127025193509347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38918208564169366924679129 29188656423127025193509347)
                ·
                  refine ⟨43782984634690537790264021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29188656423127025193509347 43782984634690537790264021)
                  ·
                    refine ⟨1026163702375559479459313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43782984634690537790264021 1026163702375559479459313)
                    ·
                      rfl

theorem cell23_5995340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_5995340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995340 prefixEnd_5995340 := by exact prefixLift 5995340
  have htrace : WordTrace (prefixWord ++ tailWord_5995340) baseStart_5995340 baseEnd_5995340 := by
    simpa [prefixWord, tailWord_5995340, baseEnd_5995340] using wordTrace_append hprefix tailTrace_5995340
  have hstable : (prefixWord ++ tailWord_5995340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995340).length < 2 ^ (prefixWord ++ tailWord_5995340).sum := by decide
  have hdescent : baseEnd_5995340 < baseStart_5995340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995360 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5995360 : Nat := 118140960795 + 5995360 * 2 ^ 59
def prefixEnd_5995360 : Nat := 4983230072969 + 3 ^ 40 * 5995360 * 2
def baseEnd_5995360 : Nat := 3078501376739768360127847

theorem tailTrace_5995360 : CollatzResearch.WordTrace tailWord_5995360 prefixEnd_5995360 3078501376739768360127847 := by
  unfold tailWord_5995360
  simp only [CollatzResearch.WordTrace]
  refine ⟨109334371779921060407099767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145779162373228080542799689 109334371779921060407099767)
  ·
    refine ⟨164001557669881590610649651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109334371779921060407099767 164001557669881590610649651)
    ·
      refine ⟨246002336504822385915974477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164001557669881590610649651 246002336504822385915974477)
      ·
        refine ⟨92250876189308394718490429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246002336504822385915974477 92250876189308394718490429)
        ·
          refine ⟨34594078570990648019433911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92250876189308394718490429 34594078570990648019433911)
          ·
            refine ⟨51891117856485972029150867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34594078570990648019433911 51891117856485972029150867)
            ·
              refine ⟨77836676784728958043726301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51891117856485972029150867 77836676784728958043726301)
              ·
                refine ⟨29188753794273359266397363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77836676784728958043726301 29188753794273359266397363)
                ·
                  refine ⟨43783130691410038899596045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29188753794273359266397363 43783130691410038899596045)
                  ·
                    refine ⟨16418674009278764587348517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43783130691410038899596045 16418674009278764587348517)
                    ·
                      refine ⟨3078501376739768360127847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16418674009278764587348517 3078501376739768360127847)
                      ·
                        rfl

theorem cell23_5995360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5995360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995360 prefixEnd_5995360 := by exact prefixLift 5995360
  have htrace : WordTrace (prefixWord ++ tailWord_5995360) baseStart_5995360 baseEnd_5995360 := by
    simpa [prefixWord, tailWord_5995360, baseEnd_5995360] using wordTrace_append hprefix tailTrace_5995360
  have hstable : (prefixWord ++ tailWord_5995360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995360).length < 2 ^ (prefixWord ++ tailWord_5995360).sum := by decide
  have hdescent : baseEnd_5995360 < baseStart_5995360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995374 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_5995374 : Nat := 118140960795 + 5995374 * 2 ^ 59
def prefixEnd_5995374 : Nat := 4983230072969 + 3 ^ 40 * 5995374 * 2
def baseEnd_5995374 : Nat := 1026169521822977101784261

theorem tailTrace_5995374 : CollatzResearch.WordTrace tailWord_5995374 prefixEnd_5995374 1026169521822977101784261 := by
  unfold tailWord_5995374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27333656772723925150651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145779502787860934136806117 27333656772723925150651147)
  ·
    refine ⟨41000485159085887725976721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27333656772723925150651147 41000485159085887725976721)
    ·
      refine ⟨30750363869314415794482541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41000485159085887725976721 30750363869314415794482541)
      ·
        refine ⟨11531386450992905922930953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30750363869314415794482541 11531386450992905922930953)
        ·
          refine ⟨8648539838244679442198215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11531386450992905922930953 8648539838244679442198215)
          ·
            refine ⟨12972809757367019163297323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648539838244679442198215 12972809757367019163297323)
            ·
              refine ⟨19459214636050528744945985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12972809757367019163297323 19459214636050528744945985)
              ·
                refine ⟨14594410977037896558709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19459214636050528744945985 14594410977037896558709489)
                ·
                  refine ⟨10945808232778422419032117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14594410977037896558709489 10945808232778422419032117)
                  ·
                    refine ⟨1026169521822977101784261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10945808232778422419032117 1026169521822977101784261)
                    ·
                      rfl

theorem cell23_5995374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_5995374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995374 prefixEnd_5995374 := by exact prefixLift 5995374
  have htrace : WordTrace (prefixWord ++ tailWord_5995374) baseStart_5995374 baseEnd_5995374 := by
    simpa [prefixWord, tailWord_5995374, baseEnd_5995374] using wordTrace_append hprefix tailTrace_5995374
  have hstable : (prefixWord ++ tailWord_5995374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995374).length < 2 ^ (prefixWord ++ tailWord_5995374).sum := by decide
  have hdescent : baseEnd_5995374 < baseStart_5995374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995377 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_5995377 : Nat := 118140960795 + 5995377 * 2 ^ 59
def prefixEnd_5995377 : Nat := 4983230072969 + 3 ^ 40 * 5995377 * 2
def baseEnd_5995377 : Nat := 3078510105910894793615269

theorem tailTrace_5995377 : CollatzResearch.WordTrace tailWord_5995377 prefixEnd_5995377 3078510105910894793615269 := by
  unfold tailWord_5995377
  simp only [CollatzResearch.WordTrace]
  refine ⟨218669363600780532717568385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145779575733853688478378923 218669363600780532717568385)
  ·
    refine ⟨164002022700585399538176289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218669363600780532717568385 164002022700585399538176289)
    ·
      refine ⟨123001517025439049653632217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164002022700585399538176289 123001517025439049653632217)
      ·
        refine ⟨92251137769079287240224163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123001517025439049653632217 92251137769079287240224163)
        ·
          refine ⟨138376706653618930860336245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92251137769079287240224163 138376706653618930860336245)
          ·
            refine ⟨12972816248776774768156523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138376706653618930860336245 12972816248776774768156523)
            ·
              refine ⟨19459224373165162152234785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12972816248776774768156523 19459224373165162152234785)
              ·
                refine ⟨14594418279873871614176089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19459224373165162152234785 14594418279873871614176089)
                ·
                  refine ⟨10945813709905403710632067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14594418279873871614176089 10945813709905403710632067)
                  ·
                    refine ⟨16418720564858105565948101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10945813709905403710632067 16418720564858105565948101)
                    ·
                      refine ⟨3078510105910894793615269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16418720564858105565948101 3078510105910894793615269)
                      ·
                        rfl

theorem cell23_5995377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_5995377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995377 prefixEnd_5995377 := by exact prefixLift 5995377
  have htrace : WordTrace (prefixWord ++ tailWord_5995377) baseStart_5995377 baseEnd_5995377 := by
    simpa [prefixWord, tailWord_5995377, baseEnd_5995377] using wordTrace_append hprefix tailTrace_5995377
  have hstable : (prefixWord ++ tailWord_5995377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995377).length < 2 ^ (prefixWord ++ tailWord_5995377).sum := by decide
  have hdescent : baseEnd_5995377 < baseStart_5995377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995387 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 3, 4]
def baseStart_5995387 : Nat := 118140960795 + 5995387 * 2 ^ 59
def prefixEnd_5995387 : Nat := 4983230072969 + 3 ^ 40 * 5995387 * 2
def baseEnd_5995387 : Nat := 1026171746905813251496741

theorem tailTrace_5995387 : CollatzResearch.WordTrace tailWord_5995387 prefixEnd_5995387 1026171746905813251496741 := by
  unfold tailWord_5995387
  simp only [CollatzResearch.WordTrace]
  refine ⟨218669728330744304425432415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145779818887162869616954943 218669728330744304425432415)
  ·
    refine ⟨328004592496116456638148623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218669728330744304425432415 328004592496116456638148623)
    ·
      refine ⟨492006888744174684957222935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328004592496116456638148623 492006888744174684957222935)
      ·
        refine ⟨738010333116262027435834403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492006888744174684957222935 738010333116262027435834403)
        ·
          refine ⟨1107015499674393041153751605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738010333116262027435834403 1107015499674393041153751605)
          ·
            refine ⟨103782703094474347608164213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1107015499674393041153751605 103782703094474347608164213)
            ·
              refine ⟨9729628415106970088265395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103782703094474347608164213 9729628415106970088265395)
              ·
                refine ⟨14594442622660455132398093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729628415106970088265395 14594442622660455132398093)
                ·
                  refine ⟨5472915983497670674649285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594442622660455132398093 5472915983497670674649285)
                  ·
                    refine ⟨1026171746905813251496741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472915983497670674649285 1026171746905813251496741)
                    ·
                      rfl

theorem cell23_5995387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 4].length) (baseStart_5995387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995387 prefixEnd_5995387 := by exact prefixLift 5995387
  have htrace : WordTrace (prefixWord ++ tailWord_5995387) baseStart_5995387 baseEnd_5995387 := by
    simpa [prefixWord, tailWord_5995387, baseEnd_5995387] using wordTrace_append hprefix tailTrace_5995387
  have hstable : (prefixWord ++ tailWord_5995387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995387).length < 2 ^ (prefixWord ++ tailWord_5995387).sum := by decide
  have hdescent : baseEnd_5995387 < baseStart_5995387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995454 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_5995454 : Nat := 118140960795 + 5995454 * 2 ^ 59
def prefixEnd_5995454 : Nat := 4983230072969 + 3 ^ 40 * 5995454 * 2
def baseEnd_5995454 : Nat := 3078549643921290992352415

theorem tailTrace_5995454 : CollatzResearch.WordTrace tailWord_5995454 prefixEnd_5995454 3078549643921290992352415 := by
  unfold tailWord_5995454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334021502687696858515177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145781448014334383245414277 27334021502687696858515177)
  ·
    refine ⟨20500516127015772643886383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27334021502687696858515177 20500516127015772643886383)
    ·
      refine ⟨30750774190523658965829575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20500516127015772643886383 30750774190523658965829575)
      ·
        refine ⟨46126161285785488448744363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30750774190523658965829575 46126161285785488448744363)
        ·
          refine ⟨69189241928678232673116545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46126161285785488448744363 69189241928678232673116545)
          ·
            refine ⟨51891931446508674504837409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69189241928678232673116545 51891931446508674504837409)
            ·
              refine ⟨38918948584881505878628057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51891931446508674504837409 38918948584881505878628057)
              ·
                refine ⟨29189211438661129408971043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38918948584881505878628057 29189211438661129408971043)
                ·
                  refine ⟨43783817157991694113456565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29189211438661129408971043 43783817157991694113456565)
                  ·
                    refine ⟨4104732858561721323136553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43783817157991694113456565 4104732858561721323136553)
                    ·
                      refine ⟨3078549643921290992352415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104732858561721323136553 3078549643921290992352415)
                      ·
                        rfl

theorem cell23_5995454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_5995454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995454 prefixEnd_5995454 := by exact prefixLift 5995454
  have htrace : WordTrace (prefixWord ++ tailWord_5995454) baseStart_5995454 baseEnd_5995454 := by
    simpa [prefixWord, tailWord_5995454, baseEnd_5995454] using wordTrace_append hprefix tailTrace_5995454
  have hstable : (prefixWord ++ tailWord_5995454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995454).length < 2 ^ (prefixWord ++ tailWord_5995454).sum := by decide
  have hdescent : baseEnd_5995454 < baseStart_5995454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995462 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5995462 : Nat := 118140960795 + 5995462 * 2 ^ 59
def prefixEnd_5995462 : Nat := 4983230072969 + 3 ^ 40 * 5995462 * 2
def baseEnd_5995462 : Nat := 3078553751766526961052379

theorem tailTrace_5995462 : CollatzResearch.WordTrace tailWord_5995462 prefixEnd_5995462 3078553751766526961052379 := by
  unfold tailWord_5995462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6833514493921018507325395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145781642536981728156275093 6833514493921018507325395)
  ·
    refine ⟨10250271740881527760988093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6833514493921018507325395 10250271740881527760988093)
    ·
      refine ⟨3843851902830572910370535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10250271740881527760988093 3843851902830572910370535)
      ·
        refine ⟨5765777854245859365555803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843851902830572910370535 5765777854245859365555803)
        ·
          refine ⟨8648666781368789048333705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765777854245859365555803 8648666781368789048333705)
          ·
            refine ⟨6486500086026591786250279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8648666781368789048333705 6486500086026591786250279)
            ·
              refine ⟨9729750129039887679375419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486500086026591786250279 9729750129039887679375419)
              ·
                refine ⟨14594625193559831519063129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729750129039887679375419 14594625193559831519063129)
                ·
                  refine ⟨10945968895169873639297347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14594625193559831519063129 10945968895169873639297347)
                  ·
                    refine ⟨16418953342754810458946021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10945968895169873639297347 16418953342754810458946021)
                    ·
                      refine ⟨3078553751766526961052379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16418953342754810458946021 3078553751766526961052379)
                      ·
                        rfl

theorem cell23_5995462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5995462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995462 prefixEnd_5995462 := by exact prefixLift 5995462
  have htrace : WordTrace (prefixWord ++ tailWord_5995462) baseStart_5995462 baseEnd_5995462 := by
    simpa [prefixWord, tailWord_5995462, baseEnd_5995462] using wordTrace_append hprefix tailTrace_5995462
  have hstable : (prefixWord ++ tailWord_5995462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995462).length < 2 ^ (prefixWord ++ tailWord_5995462).sum := by decide
  have hdescent : baseEnd_5995462 < baseStart_5995462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995467 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4]
def baseStart_5995467 : Nat := 118140960795 + 5995467 * 2 ^ 59
def prefixEnd_5995467 : Nat := 4983230072969 + 3 ^ 40 * 5995467 * 2
def baseEnd_5995467 : Nat := 3078556319169799441489855

theorem tailTrace_5995467 : CollatzResearch.WordTrace tailWord_5995467 prefixEnd_5995467 3078556319169799441489855 := by
  unfold tailWord_5995467
  simp only [CollatzResearch.WordTrace]
  refine ⟨218672646170454478088344655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145781764113636318725563103 218672646170454478088344655)
  ·
    refine ⟨328008969255681717132516983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218672646170454478088344655 328008969255681717132516983)
    ·
      refine ⟨492013453883522575698775475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328008969255681717132516983 492013453883522575698775475)
      ·
        refine ⟨738020180825283863548163213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492013453883522575698775475 738020180825283863548163213)
        ·
          refine ⟨276757567809481448830561205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 738020180825283863548163213 276757567809481448830561205)
          ·
            refine ⟨25946021982138885827865113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 276757567809481448830561205 25946021982138885827865113)
            ·
              refine ⟨19459516486604164370898835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25946021982138885827865113 19459516486604164370898835)
              ·
                refine ⟨29189274729906246556348253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19459516486604164370898835 29189274729906246556348253)
                ·
                  refine ⟨10945978023714842458630595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29189274729906246556348253 10945978023714842458630595)
                  ·
                    refine ⟨16418967035572263687945893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10945978023714842458630595 16418967035572263687945893)
                    ·
                      refine ⟨3078556319169799441489855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16418967035572263687945893 3078556319169799441489855)
                      ·
                        rfl

theorem cell23_5995467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_5995467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995467 prefixEnd_5995467 := by exact prefixLift 5995467
  have htrace : WordTrace (prefixWord ++ tailWord_5995467) baseStart_5995467 baseEnd_5995467 := by
    simpa [prefixWord, tailWord_5995467, baseEnd_5995467] using wordTrace_append hprefix tailTrace_5995467
  have hstable : (prefixWord ++ tailWord_5995467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995467).length < 2 ^ (prefixWord ++ tailWord_5995467).sum := by decide
  have hdescent : baseEnd_5995467 < baseStart_5995467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995471 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 2, 3, 2]
def baseStart_5995471 : Nat := 118140960795 + 5995471 * 2 ^ 59
def prefixEnd_5995471 : Nat := 4983230072969 + 3 ^ 40 * 5995471 * 2
def baseEnd_5995471 : Nat := 3078558373092417425839837

theorem tailTrace_5995471 : CollatzResearch.WordTrace tailWord_5995471 prefixEnd_5995471 3078558373092417425839837 := by
  unfold tailWord_5995471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218672792062439986771490267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145781861374959991180993511 218672792062439986771490267)
  ·
    refine ⟨328009188093659980157235401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218672792062439986771490267 328009188093659980157235401)
    ·
      refine ⟨246006891070244985117926551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328009188093659980157235401 246006891070244985117926551)
      ·
        refine ⟨369010336605367477676889827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246006891070244985117926551 369010336605367477676889827)
        ·
          refine ⟨553515504908051216515334741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369010336605367477676889827 553515504908051216515334741)
          ·
            refine ⟨6486509823141225193539079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 553515504908051216515334741 6486509823141225193539079)
            ·
              refine ⟨9729764734711837790308619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486509823141225193539079 9729764734711837790308619)
              ·
                refine ⟨14594647102067756685462929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729764734711837790308619 14594647102067756685462929)
                ·
                  refine ⟨10945985326550817514097197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14594647102067756685462929 10945985326550817514097197)
                  ·
                    refine ⟨4104744497456556567786449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10945985326550817514097197 4104744497456556567786449)
                    ·
                      refine ⟨3078558373092417425839837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104744497456556567786449 3078558373092417425839837)
                      ·
                        rfl

theorem cell23_5995471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3, 2].length) (baseStart_5995471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995471 prefixEnd_5995471 := by exact prefixLift 5995471
  have htrace : WordTrace (prefixWord ++ tailWord_5995471) baseStart_5995471 baseEnd_5995471 := by
    simpa [prefixWord, tailWord_5995471, baseEnd_5995471] using wordTrace_append hprefix tailTrace_5995471
  have hstable : (prefixWord ++ tailWord_5995471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995471).length < 2 ^ (prefixWord ++ tailWord_5995471).sum := by decide
  have hdescent : baseEnd_5995471 < baseStart_5995471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995481 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_5995481 : Nat := 118140960795 + 5995481 * 2 ^ 59
def prefixEnd_5995481 : Nat := 4983230072969 + 3 ^ 40 * 5995481 * 2
def baseEnd_5995481 : Nat := 1026187835966320795571597

theorem tailTrace_5995481 : CollatzResearch.WordTrace tailWord_5995481 prefixEnd_5995481 1026187835966320795571597 := by
  unfold tailWord_5995481
  simp only [CollatzResearch.WordTrace]
  refine ⟨218673156792403758479354297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145782104528269172319569531 218673156792403758479354297)
  ·
    refine ⟨164004867594302818859515723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218673156792403758479354297 164004867594302818859515723)
    ·
      refine ⟨246007301391454228289273585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164004867594302818859515723 246007301391454228289273585)
      ·
        refine ⟨184505476043590671216955189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246007301391454228289273585 184505476043590671216955189)
        ·
          refine ⟨17297388379086625426589549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184505476043590671216955189 17297388379086625426589549)
          ·
            refine ⟨6486520642157484534971081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17297388379086625426589549 6486520642157484534971081)
            ·
              refine ⟨4864890481618113401228311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486520642157484534971081 4864890481618113401228311)
              ·
                refine ⟨7297335722427170101842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864890481618113401228311 7297335722427170101842467)
                ·
                  refine ⟨10946003583640755152763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297335722427170101842467 10946003583640755152763701)
                  ·
                    refine ⟨1026187835966320795571597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10946003583640755152763701 1026187835966320795571597)
                    ·
                      rfl

theorem cell23_5995481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_5995481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995481 prefixEnd_5995481 := by exact prefixLift 5995481
  have htrace : WordTrace (prefixWord ++ tailWord_5995481) baseStart_5995481 baseEnd_5995481 := by
    simpa [prefixWord, tailWord_5995481, baseEnd_5995481] using wordTrace_append hprefix tailTrace_5995481
  have hstable : (prefixWord ++ tailWord_5995481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995481).length < 2 ^ (prefixWord ++ tailWord_5995481).sum := by decide
  have hdescent : baseEnd_5995481 < baseStart_5995481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995500 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_5995500 : Nat := 118140960795 + 5995500 * 2 ^ 59
def prefixEnd_5995500 : Nat := 4983230072969 + 3 ^ 40 * 5995500 * 2
def baseEnd_5995500 : Nat := 3078573264031397812377203

theorem tailTrace_5995500 : CollatzResearch.WordTrace tailWord_5995500 prefixEnd_5995500 3078573264031397812377203 := by
  unfold tailWord_5995500
  simp only [CollatzResearch.WordTrace]
  refine ⟨109336924889667462362147977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145782566519556616482863969 109336924889667462362147977)
  ·
    refine ⟨82002693667250596771610983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109336924889667462362147977 82002693667250596771610983)
    ·
      refine ⟨123004040500875895157416475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82002693667250596771610983 123004040500875895157416475)
      ·
        refine ⟨184506060751313842736124713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123004040500875895157416475 184506060751313842736124713)
        ·
          refine ⟨138379545563485382052093535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184506060751313842736124713 138379545563485382052093535)
          ·
            refine ⟨207569318345228073078140303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138379545563485382052093535 207569318345228073078140303)
            ·
              refine ⟨311353977517842109617210455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207569318345228073078140303 311353977517842109617210455)
              ·
                refine ⟨467030966276763164425815683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311353977517842109617210455 467030966276763164425815683)
                ·
                  refine ⟨700546449415144746638723525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467030966276763164425815683 700546449415144746638723525)
                  ·
                    refine ⟨131352459265339639994760661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700546449415144746638723525 131352459265339639994760661)
                    ·
                      refine ⟨3078573264031397812377203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131352459265339639994760661 3078573264031397812377203)
                      ·
                        rfl

theorem cell23_5995500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_5995500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995500 prefixEnd_5995500 := by exact prefixLift 5995500
  have htrace : WordTrace (prefixWord ++ tailWord_5995500) baseStart_5995500 baseEnd_5995500 := by
    simpa [prefixWord, tailWord_5995500, baseEnd_5995500] using wordTrace_append hprefix tailTrace_5995500
  have hstable : (prefixWord ++ tailWord_5995500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995500).length < 2 ^ (prefixWord ++ tailWord_5995500).sum := by decide
  have hdescent : baseEnd_5995500 < baseStart_5995500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995518 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5995518 : Nat := 118140960795 + 5995518 * 2 ^ 59
def prefixEnd_5995518 : Nat := 4983230072969 + 3 ^ 40 * 5995518 * 2
def baseEnd_5995518 : Nat := 3078582506683178741952121

theorem tailTrace_5995518 : CollatzResearch.WordTrace tailWord_5995518 prefixEnd_5995518 3078582506683178741952121 := by
  unfold tailWord_5995518
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334313286658714224806401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145783004195513142532300805 27334313286658714224806401)
  ·
    refine ⟨20500734964994035668604801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27334313286658714224806401 20500734964994035668604801)
    ·
      refine ⟨15375551223745526751453601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20500734964994035668604801 15375551223745526751453601)
      ·
        refine ⟨11531663417809145063590201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15375551223745526751453601 11531663417809145063590201)
        ·
          refine ⟨8648747563356858797692651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11531663417809145063590201 8648747563356858797692651)
          ·
            refine ⟨12973121345035288196538977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648747563356858797692651 12973121345035288196538977)
            ·
              refine ⟨9729841008776466147404233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12973121345035288196538977 9729841008776466147404233)
              ·
                refine ⟨7297380756582349610553175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9729841008776466147404233 7297380756582349610553175)
                ·
                  refine ⟨10946071134873524415829763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297380756582349610553175 10946071134873524415829763)
                  ·
                    refine ⟨16419106702310286623744645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10946071134873524415829763 16419106702310286623744645)
                    ·
                      refine ⟨3078582506683178741952121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16419106702310286623744645 3078582506683178741952121)
                      ·
                        rfl

theorem cell23_5995518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5995518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995518 prefixEnd_5995518 := by exact prefixLift 5995518
  have htrace : WordTrace (prefixWord ++ tailWord_5995518) baseStart_5995518 baseEnd_5995518 := by
    simpa [prefixWord, tailWord_5995518, baseEnd_5995518] using wordTrace_append hprefix tailTrace_5995518
  have hstable : (prefixWord ++ tailWord_5995518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995518).length < 2 ^ (prefixWord ++ tailWord_5995518).sum := by decide
  have hdescent : baseEnd_5995518 < baseStart_5995518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995520 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_5995520 : Nat := 118140960795 + 5995520 * 2 ^ 59
def prefixEnd_5995520 : Nat := 4983230072969 + 3 ^ 40 * 5995520 * 2
def baseEnd_5995520 : Nat := 1026194511214829244709037

theorem tailTrace_5995520 : CollatzResearch.WordTrace tailWord_5995520 prefixEnd_5995520 1026194511214829244709037 := by
  unfold tailWord_5995520
  simp only [CollatzResearch.WordTrace]
  refine ⟨109337289619631234070012007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145783052826174978760016009 109337289619631234070012007)
  ·
    refine ⟨164005934429446851105018011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109337289619631234070012007 164005934429446851105018011)
    ·
      refine ⟨246008901644170276657527017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164005934429446851105018011 246008901644170276657527017)
      ·
        refine ⟨184506676233127707493145263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246008901644170276657527017 184506676233127707493145263)
        ·
          refine ⟨276760014349691561239717895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184506676233127707493145263 276760014349691561239717895)
          ·
            refine ⟨415140021524537341859576843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276760014349691561239717895 415140021524537341859576843)
            ·
              refine ⟨622710032286806012789365265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415140021524537341859576843 622710032286806012789365265)
              ·
                refine ⟨467032524215104509592023949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622710032286806012789365265 467032524215104509592023949)
                ·
                  refine ⟨175137196580664191097008981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467032524215104509592023949 175137196580664191097008981)
                  ·
                    refine ⟨1026194511214829244709037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175137196580664191097008981 1026194511214829244709037)
                    ·
                      rfl

theorem cell23_5995520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_5995520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995520 prefixEnd_5995520 := by exact prefixLift 5995520
  have htrace : WordTrace (prefixWord ++ tailWord_5995520) baseStart_5995520 baseEnd_5995520 := by
    simpa [prefixWord, tailWord_5995520, baseEnd_5995520] using wordTrace_append hprefix tailTrace_5995520
  have hstable : (prefixWord ++ tailWord_5995520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995520).length < 2 ^ (prefixWord ++ tailWord_5995520).sum := by decide
  have hdescent : baseEnd_5995520 < baseStart_5995520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995521 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5995521 : Nat := 118140960795 + 5995521 * 2 ^ 59
def prefixEnd_5995521 : Nat := 4983230072969 + 3 ^ 40 * 5995521 * 2
def baseEnd_5995521 : Nat := 3078584047125142230214607

theorem tailTrace_5995521 : CollatzResearch.WordTrace tailWord_5995521 prefixEnd_5995521 3078584047125142230214607 := by
  unfold tailWord_5995521
  simp only [CollatzResearch.WordTrace]
  refine ⟨218674615712258845310810417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145783077141505896873873611 218674615712258845310810417)
  ·
    refine ⟨164005961784194133983107813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218674615712258845310810417 164005961784194133983107813)
    ·
      refine ⟨30751117834536400121832715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164005961784194133983107813 30751117834536400121832715)
      ·
        refine ⟨46126676751804600182749073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30751117834536400121832715 46126676751804600182749073)
        ·
          refine ⟨34595007563853450137061805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46126676751804600182749073 34595007563853450137061805)
          ·
            refine ⟨12973127836445043801398177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34595007563853450137061805 12973127836445043801398177)
            ·
              refine ⟨9729845877333782851048633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12973127836445043801398177 9729845877333782851048633)
              ·
                refine ⟨7297384408000337138286475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9729845877333782851048633 7297384408000337138286475)
                ·
                  refine ⟨10946076612000505707429713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297384408000337138286475 10946076612000505707429713)
                  ·
                    refine ⟨8209557459000379280572285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10946076612000505707429713 8209557459000379280572285)
                    ·
                      refine ⟨3078584047125142230214607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8209557459000379280572285 3078584047125142230214607)
                      ·
                        rfl

theorem cell23_5995521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5995521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995521 prefixEnd_5995521 := by exact prefixLift 5995521
  have htrace : WordTrace (prefixWord ++ tailWord_5995521) baseStart_5995521 baseEnd_5995521 := by
    simpa [prefixWord, tailWord_5995521, baseEnd_5995521] using wordTrace_append hprefix tailTrace_5995521
  have hstable : (prefixWord ++ tailWord_5995521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995521).length < 2 ^ (prefixWord ++ tailWord_5995521).sum := by decide
  have hdescent : baseEnd_5995521 < baseStart_5995521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995552 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5995552 : Nat := 118140960795 + 5995552 * 2 ^ 59
def prefixEnd_5995552 : Nat := 4983230072969 + 3 ^ 40 * 5995552 * 2
def baseEnd_5995552 : Nat := 3078599965025431608926965

theorem tailTrace_5995552 : CollatzResearch.WordTrace tailWord_5995552 prefixEnd_5995552 3078599965025431608926965 := by
  unfold tailWord_5995552
  simp only [CollatzResearch.WordTrace]
  refine ⟨109337873187573268802594455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145783830916764358403459273 109337873187573268802594455)
  ·
    refine ⟨164006809781359903203891683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109337873187573268802594455 164006809781359903203891683)
    ·
      refine ⟨246010214672039854805837525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164006809781359903203891683 246010214672039854805837525)
      ·
        refine ⟨5765864406375934097011817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 246010214672039854805837525 5765864406375934097011817)
        ·
          refine ⟨4324398304781950572758863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765864406375934097011817 4324398304781950572758863)
          ·
            refine ⟨6486597457172925859138295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324398304781950572758863 6486597457172925859138295)
            ·
              refine ⟨9729896185759388788707443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486597457172925859138295 9729896185759388788707443)
              ·
                refine ⟨14594844278639083183061165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729896185759388788707443 14594844278639083183061165)
                ·
                  refine ⟨5473066604489656193647937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594844278639083183061165 5473066604489656193647937)
                  ·
                    refine ⟨4104799953367242145235953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473066604489656193647937 4104799953367242145235953)
                    ·
                      refine ⟨3078599965025431608926965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104799953367242145235953 3078599965025431608926965)
                      ·
                        rfl

theorem cell23_5995552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5995552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995552 prefixEnd_5995552 := by exact prefixLift 5995552
  have htrace : WordTrace (prefixWord ++ tailWord_5995552) baseStart_5995552 baseEnd_5995552 := by
    simpa [prefixWord, tailWord_5995552, baseEnd_5995552] using wordTrace_append hprefix tailTrace_5995552
  have hstable : (prefixWord ++ tailWord_5995552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995552).length < 2 ^ (prefixWord ++ tailWord_5995552).sum := by decide
  have hdescent : baseEnd_5995552 < baseStart_5995552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995557 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_5995557 : Nat := 118140960795 + 5995557 * 2 ^ 59
def prefixEnd_5995557 : Nat := 4983230072969 + 3 ^ 40 * 5995557 * 2
def baseEnd_5995557 : Nat := 3078602532428704089364441

theorem tailTrace_5995557 : CollatzResearch.WordTrace tailWord_5995557 prefixEnd_5995557 3078602532428704089364441 := by
  unfold tailWord_5995557
  simp only [CollatzResearch.WordTrace]
  refine ⟨218675928740128423459120925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145783952493418948972747283 218675928740128423459120925)
  ·
    refine ⟨82003473277548158797170347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218675928740128423459120925 82003473277548158797170347)
    ·
      refine ⟨123005209916322238195755521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82003473277548158797170347 123005209916322238195755521)
      ·
        refine ⟨92253907437241678646816641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123005209916322238195755521 92253907437241678646816641)
        ·
          refine ⟨69190430577931258985112481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92253907437241678646816641 69190430577931258985112481)
          ·
            refine ⟨51892822933448444238834361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69190430577931258985112481 51892822933448444238834361)
            ·
              refine ⟨38919617200086333179125771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51892822933448444238834361 38919617200086333179125771)
              ·
                refine ⟨58379425800129499768688657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38919617200086333179125771 58379425800129499768688657)
                ·
                  refine ⟨43784569350097124826516493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58379425800129499768688657 43784569350097124826516493)
                  ·
                    refine ⟨16419213506286421809943685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43784569350097124826516493 16419213506286421809943685)
                    ·
                      refine ⟨3078602532428704089364441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16419213506286421809943685 3078602532428704089364441)
                      ·
                        rfl

theorem cell23_5995557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_5995557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995557 prefixEnd_5995557 := by exact prefixLift 5995557
  have htrace : WordTrace (prefixWord ++ tailWord_5995557) baseStart_5995557 baseEnd_5995557 := by
    simpa [prefixWord, tailWord_5995557, baseEnd_5995557] using wordTrace_append hprefix tailTrace_5995557
  have hstable : (prefixWord ++ tailWord_5995557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995557).length < 2 ^ (prefixWord ++ tailWord_5995557).sum := by decide
  have hdescent : baseEnd_5995557 < baseStart_5995557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995591 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_5995591 : Nat := 118140960795 + 5995591 * 2 ^ 59
def prefixEnd_5995591 : Nat := 4983230072969 + 3 ^ 40 * 5995591 * 2
def baseEnd_5995591 : Nat := 3078619990770956956339285

theorem tailTrace_5995591 : CollatzResearch.WordTrace tailWord_5995591 prefixEnd_5995591 3078619990770956956339285 := by
  unfold tailWord_5995591
  simp only [CollatzResearch.WordTrace]
  refine ⟨218677168822005247265858627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145784779214670164843905751 218677168822005247265858627)
  ·
    refine ⟨328015753233007870898787941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218677168822005247265858627 328015753233007870898787941)
    ·
      refine ⟨61502953731188975793522739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328015753233007870898787941 61502953731188975793522739)
      ·
        refine ⟨92254430596783463690284109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61502953731188975793522739 92254430596783463690284109)
        ·
          refine ⟨34595411473793798883856541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92254430596783463690284109 34595411473793798883856541)
          ·
            refine ⟨12973279302672674581446203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34595411473793798883856541 12973279302672674581446203)
            ·
              refine ⟨19459918954009011872169305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973279302672674581446203 19459918954009011872169305)
              ·
                refine ⟨14594939215506758904126979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19459918954009011872169305 14594939215506758904126979)
                ·
                  refine ⟨21892408823260138356190469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14594939215506758904126979 21892408823260138356190469)
                  ·
                    refine ⟨4104826654361275941785713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21892408823260138356190469 4104826654361275941785713)
                    ·
                      refine ⟨3078619990770956956339285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104826654361275941785713 3078619990770956956339285)
                      ·
                        rfl

theorem cell23_5995591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_5995591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995591 prefixEnd_5995591 := by exact prefixLift 5995591
  have htrace : WordTrace (prefixWord ++ tailWord_5995591) baseStart_5995591 baseEnd_5995591 := by
    simpa [prefixWord, tailWord_5995591, baseEnd_5995591] using wordTrace_append hprefix tailTrace_5995591
  have hstable : (prefixWord ++ tailWord_5995591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995591).length < 2 ^ (prefixWord ++ tailWord_5995591).sum := by decide
  have hdescent : baseEnd_5995591 < baseStart_5995591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995608 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_5995608 : Nat := 118140960795 + 5995608 * 2 ^ 59
def prefixEnd_5995608 : Nat := 4983230072969 + 3 ^ 40 * 5995608 * 2
def baseEnd_5995608 : Nat := 3078628719942083389826707

theorem tailTrace_5995608 : CollatzResearch.WordTrace tailWord_5995608 prefixEnd_5995608 3078628719942083389826707 := by
  unfold tailWord_5995608
  simp only [CollatzResearch.WordTrace]
  refine ⟨109338894431471829584613739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145785192575295772779484985 109338894431471829584613739)
  ·
    refine ⟨164008341647207744376920609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109338894431471829584613739 164008341647207744376920609)
    ·
      refine ⟨123006256235405808282690457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164008341647207744376920609 123006256235405808282690457)
      ·
        refine ⟨92254692176554356212017843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123006256235405808282690457 92254692176554356212017843)
        ·
          refine ⟨138382038264831534318026765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92254692176554356212017843 138382038264831534318026765)
          ·
            refine ⟨51893264349311825369260037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138382038264831534318026765 51893264349311825369260037)
            ·
              refine ⟨9729987065495967256736257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51893264349311825369260037 9729987065495967256736257)
              ·
                refine ⟨7297490299121975442552193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9729987065495967256736257 7297490299121975442552193)
                ·
                  refine ⟨5473117724341481581914145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297490299121975442552193 5473117724341481581914145)
                  ·
                    refine ⟨4104838293256111186435609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473117724341481581914145 4104838293256111186435609)
                    ·
                      refine ⟨3078628719942083389826707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104838293256111186435609 3078628719942083389826707)
                      ·
                        rfl

theorem cell23_5995608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_5995608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995608 prefixEnd_5995608 := by exact prefixLift 5995608
  have htrace : WordTrace (prefixWord ++ tailWord_5995608) baseStart_5995608 baseEnd_5995608 := by
    simpa [prefixWord, tailWord_5995608, baseEnd_5995608] using wordTrace_append hprefix tailTrace_5995608
  have hstable : (prefixWord ++ tailWord_5995608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995608).length < 2 ^ (prefixWord ++ tailWord_5995608).sum := by decide
  have hdescent : baseEnd_5995608 < baseStart_5995608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995646 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5995646 : Nat := 118140960795 + 5995646 * 2 ^ 59
def prefixEnd_5995646 : Nat := 4983230072969 + 3 ^ 40 * 5995646 * 2
def baseEnd_5995646 : Nat := 3078648232206954241151533

theorem tailTrace_5995646 : CollatzResearch.WordTrace tailWord_5995646 prefixEnd_5995646 3078648232206954241151533 := by
  unfold tailWord_5995646
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334896854600748957388849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145786116557870661106073861 27334896854600748957388849)
  ·
    refine ⟨20501172640950561718041637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27334896854600748957388849 20501172640950561718041637)
    ·
      refine ⟨3843969870178230322132807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20501172640950561718041637 3843969870178230322132807)
      ·
        refine ⟨5765954805267345483199211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843969870178230322132807 5765954805267345483199211)
        ·
          refine ⟨8648932207901018224798817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765954805267345483199211 8648932207901018224798817)
          ·
            refine ⟨6486699155925763668599113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8648932207901018224798817 6486699155925763668599113)
            ·
              refine ⟨4865024366944322751449335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486699155925763668599113 4865024366944322751449335)
              ·
                refine ⟨7297536550416484127174003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865024366944322751449335 7297536550416484127174003)
                ·
                  refine ⟨10946304825624726190761005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297536550416484127174003 10946304825624726190761005)
                  ·
                    refine ⟨4104864309609272321535377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10946304825624726190761005 4104864309609272321535377)
                    ·
                      refine ⟨3078648232206954241151533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104864309609272321535377 3078648232206954241151533)
                      ·
                        rfl

theorem cell23_5995646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5995646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995646 prefixEnd_5995646 := by exact prefixLift 5995646
  have htrace : WordTrace (prefixWord ++ tailWord_5995646) baseStart_5995646 baseEnd_5995646 := by
    simpa [prefixWord, tailWord_5995646, baseEnd_5995646] using wordTrace_append hprefix tailTrace_5995646
  have hstable : (prefixWord ++ tailWord_5995646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995646).length < 2 ^ (prefixWord ++ tailWord_5995646).sum := by decide
  have hdescent : baseEnd_5995646 < baseStart_5995646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995667 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_5995667 : Nat := 118140960795 + 5995667 * 2 ^ 59
def prefixEnd_5995667 : Nat := 4983230072969 + 3 ^ 40 * 5995667 * 2
def baseEnd_5995667 : Nat := 3078659015300698658988935

theorem tailTrace_5995667 : CollatzResearch.WordTrace tailWord_5995667 prefixEnd_5995667 3078659015300698658988935 := by
  unfold tailWord_5995667
  simp only [CollatzResearch.WordTrace]
  refine ⟨218679940769729912245625255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145786627179819941497083503 218679940769729912245625255)
  ·
    refine ⟨328019911154594868368437883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218679940769729912245625255 328019911154594868368437883)
    ·
      refine ⟨492029866731892302552656825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328019911154594868368437883 492029866731892302552656825)
      ·
        refine ⟨369022400048919226914492619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492029866731892302552656825 369022400048919226914492619)
        ·
          refine ⟨553533600073378840371738929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369022400048919226914492619 553533600073378840371738929)
          ·
            refine ⟨415150200055034130278804197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553533600073378840371738929 415150200055034130278804197)
            ·
              refine ⟨77840662510318899427275787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 415150200055034130278804197 77840662510318899427275787)
              ·
                refine ⟨116760993765478349140913681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77840662510318899427275787 116760993765478349140913681)
                ·
                  refine ⟨87570745324108761855685261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116760993765478349140913681 87570745324108761855685261)
                  ·
                    refine ⟨32839029496540785695881973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87570745324108761855685261 32839029496540785695881973)
                    ·
                      refine ⟨3078659015300698658988935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32839029496540785695881973 3078659015300698658988935)
                      ·
                        rfl

theorem cell23_5995667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_5995667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995667 prefixEnd_5995667 := by exact prefixLift 5995667
  have htrace : WordTrace (prefixWord ++ tailWord_5995667) baseStart_5995667 baseEnd_5995667 := by
    simpa [prefixWord, tailWord_5995667, baseEnd_5995667] using wordTrace_append hprefix tailTrace_5995667
  have hstable : (prefixWord ++ tailWord_5995667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995667).length < 2 ^ (prefixWord ++ tailWord_5995667).sum := by decide
  have hdescent : baseEnd_5995667 < baseStart_5995667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995681 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5995681 : Nat := 118140960795 + 5995681 * 2 ^ 59
def prefixEnd_5995681 : Nat := 4983230072969 + 3 ^ 40 * 5995681 * 2
def baseEnd_5995681 : Nat := 3078666204029861604213871

theorem tailTrace_5995681 : CollatzResearch.WordTrace tailWord_5995681 prefixEnd_5995681 3078666204029861604213871 := by
  unfold tailWord_5995681
  simp only [CollatzResearch.WordTrace]
  refine ⟨218680451391679192636634897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145786967594452795091089931 218680451391679192636634897)
  ·
    refine ⟨164010338543759394477476173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218680451391679192636634897 164010338543759394477476173)
    ·
      refine ⟨61503876953909772929053565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164010338543759394477476173 61503876953909772929053565)
      ·
        refine ⟨23063953857716164848395087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61503876953909772929053565 23063953857716164848395087)
        ·
          refine ⟨34595930786574247272592631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23063953857716164848395087 34595930786574247272592631)
          ·
            refine ⟨51893896179861370908888947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34595930786574247272592631 51893896179861370908888947)
            ·
              refine ⟨77840844269792056363333421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51893896179861370908888947 77840844269792056363333421)
              ·
                refine ⟨29190316601172021136250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77840844269792056363333421 29190316601172021136250033)
                ·
                  refine ⟨21892737450879015852187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29190316601172021136250033 21892737450879015852187525)
                  ·
                    refine ⟨4104888272039815472285161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21892737450879015852187525 4104888272039815472285161)
                    ·
                      refine ⟨3078666204029861604213871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104888272039815472285161 3078666204029861604213871)
                      ·
                        rfl

theorem cell23_5995681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5995681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995681 prefixEnd_5995681 := by exact prefixLift 5995681
  have htrace : WordTrace (prefixWord ++ tailWord_5995681) baseStart_5995681 baseEnd_5995681 := by
    simpa [prefixWord, tailWord_5995681, baseEnd_5995681] using wordTrace_append hprefix tailTrace_5995681
  have hstable : (prefixWord ++ tailWord_5995681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995681).length < 2 ^ (prefixWord ++ tailWord_5995681).sum := by decide
  have hdescent : baseEnd_5995681 < baseStart_5995681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_5995707 : Nat := 118140960795 + 5995707 * 2 ^ 59
def prefixEnd_5995707 : Nat := 4983230072969 + 3 ^ 40 * 5995707 * 2
def baseEnd_5995707 : Nat := 3078679554526878502488751

theorem tailTrace_5995707 : CollatzResearch.WordTrace tailWord_5995707 prefixEnd_5995707 3078679554526878502488751 := by
  unfold tailWord_5995707
  simp only [CollatzResearch.WordTrace]
  refine ⟨218681399689584999077081375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145787599793056666051387583 218681399689584999077081375)
  ·
    refine ⟨328022099534377498615622063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218681399689584999077081375 328022099534377498615622063)
    ·
      refine ⟨492033149301566247923433095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328022099534377498615622063 492033149301566247923433095)
      ·
        refine ⟨738049723952349371885149643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492033149301566247923433095 738049723952349371885149643)
        ·
          refine ⟨1107074585928524057827724465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738049723952349371885149643 1107074585928524057827724465)
          ·
            refine ⟨830305939446393043370793349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107074585928524057827724465 830305939446393043370793349)
            ·
              refine ⟨155682363646198695632023753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 830305939446393043370793349 155682363646198695632023753)
              ·
                refine ⟨116761772734649021724017815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155682363646198695632023753 116761772734649021724017815)
                ·
                  refine ⟨175142659101973532586026723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116761772734649021724017815 175142659101973532586026723)
                  ·
                    refine ⟨262713988652960298879040085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175142659101973532586026723 262713988652960298879040085)
                    ·
                      refine ⟨3078679554526878502488751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 262713988652960298879040085 3078679554526878502488751)
                      ·
                        rfl

theorem cell23_5995707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_5995707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995707 prefixEnd_5995707 := by exact prefixLift 5995707
  have htrace : WordTrace (prefixWord ++ tailWord_5995707) baseStart_5995707 baseEnd_5995707 := by
    simpa [prefixWord, tailWord_5995707, baseEnd_5995707] using wordTrace_append hprefix tailTrace_5995707
  have hstable : (prefixWord ++ tailWord_5995707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995707).length < 2 ^ (prefixWord ++ tailWord_5995707).sum := by decide
  have hdescent : baseEnd_5995707 < baseStart_5995707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995758 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_5995758 : Nat := 118140960795 + 5995758 * 2 ^ 59
def prefixEnd_5995758 : Nat := 4983230072969 + 3 ^ 40 * 5995758 * 2
def baseEnd_5995758 : Nat := 3078705742040257802951017

theorem tailTrace_5995758 : CollatzResearch.WordTrace tailWord_5995758 prefixEnd_5995758 3078705742040257802951017 := by
  unfold tailWord_5995758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27335407476550029348398491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145788839874933489858125285 27335407476550029348398491)
  ·
    refine ⟨41003111214825044022597737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27335407476550029348398491 41003111214825044022597737)
    ·
      refine ⟨30752333411118783016948303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41003111214825044022597737 30752333411118783016948303)
      ·
        refine ⟨46128500116678174525422455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30752333411118783016948303 46128500116678174525422455)
        ·
          refine ⟨69192750175017261788133683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46128500116678174525422455 69192750175017261788133683)
          ·
            refine ⟨103789125262525892682200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69192750175017261788133683 103789125262525892682200525)
            ·
              refine ⟨38920921973447209755825197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103789125262525892682200525 38920921973447209755825197)
              ·
                refine ⟨14595345740042703658434449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38920921973447209755825197 14595345740042703658434449)
                ·
                  refine ⟨10946509305032027743825837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14595345740042703658434449 10946509305032027743825837)
                  ·
                    refine ⟨4104940989387010403934689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10946509305032027743825837 4104940989387010403934689)
                    ·
                      refine ⟨3078705742040257802951017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104940989387010403934689 3078705742040257802951017)
                      ·
                        rfl

theorem cell23_5995758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_5995758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995758 prefixEnd_5995758 := by exact prefixLift 5995758
  have htrace : WordTrace (prefixWord ++ tailWord_5995758) baseStart_5995758 baseEnd_5995758 := by
    simpa [prefixWord, tailWord_5995758, baseEnd_5995758] using wordTrace_append hprefix tailTrace_5995758
  have hstable : (prefixWord ++ tailWord_5995758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995758).length < 2 ^ (prefixWord ++ tailWord_5995758).sum := by decide
  have hdescent : baseEnd_5995758 < baseStart_5995758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995805 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5995805 : Nat := 118140960795 + 5995805 * 2 ^ 59
def prefixEnd_5995805 : Nat := 4983230072969 + 3 ^ 40 * 5995805 * 2
def baseEnd_5995805 : Nat := 3078729875631019119063301

theorem tailTrace_5995805 : CollatzResearch.WordTrace tailWord_5995805 prefixEnd_5995805 3078729875631019119063301 := by
  unfold tailWord_5995805
  simp only [CollatzResearch.WordTrace]
  refine ⟨218684974043229961814148869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145789982695486641209432579 218684974043229961814148869)
  ·
    refine ⟨41003432633105617840152913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218684974043229961814148869 41003432633105617840152913)
    ·
      refine ⟨30752574474829213380114685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41003432633105617840152913 30752574474829213380114685)
      ·
        refine ⟨11532215428060955017543007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30752574474829213380114685 11532215428060955017543007)
        ·
          refine ⟨17298323142091432526314511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532215428060955017543007 17298323142091432526314511)
          ·
            refine ⟨25947484713137148789471767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298323142091432526314511 25947484713137148789471767)
            ·
              refine ⟨38921227069705723184207651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25947484713137148789471767 38921227069705723184207651)
              ·
                refine ⟨58381840604558584776311477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38921227069705723184207651 58381840604558584776311477)
                ·
                  refine ⟨5473297556677367322779201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58381840604558584776311477 5473297556677367322779201)
                  ·
                    refine ⟨4104973167508025492084401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473297556677367322779201 4104973167508025492084401)
                    ·
                      refine ⟨3078729875631019119063301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4104973167508025492084401 3078729875631019119063301)
                      ·
                        rfl

theorem cell23_5995805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5995805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995805 prefixEnd_5995805 := by exact prefixLift 5995805
  have htrace : WordTrace (prefixWord ++ tailWord_5995805) baseStart_5995805 baseEnd_5995805 := by
    simpa [prefixWord, tailWord_5995805, baseEnd_5995805] using wordTrace_append hprefix tailTrace_5995805
  have hstable : (prefixWord ++ tailWord_5995805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995805).length < 2 ^ (prefixWord ++ tailWord_5995805).sum := by decide
  have hdescent : baseEnd_5995805 < baseStart_5995805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995811 : List Nat := [1, 1, 1, 4, 2, 4, 3, 7]
def baseStart_5995811 : Nat := 118140960795 + 5995811 * 2 ^ 59
def prefixEnd_5995811 : Nat := 4983230072969 + 3 ^ 40 * 5995811 * 2
def baseEnd_5995811 : Nat := 114027146537590596132899

theorem tailTrace_5995811 : CollatzResearch.WordTrace tailWord_5995811 prefixEnd_5995811 114027146537590596132899 := by
  unfold tailWord_5995811
  simp only [CollatzResearch.WordTrace]
  refine ⟨218685192881208224838867287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145790128587472149892578191 218685192881208224838867287)
  ·
    refine ⟨328027789321812337258300931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218685192881208224838867287 328027789321812337258300931)
    ·
      refine ⟨492041683982718505887451397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328027789321812337258300931 492041683982718505887451397)
      ·
        refine ⟨92257815746759719853897137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492041683982718505887451397 92257815746759719853897137)
        ·
          refine ⟨69193361810069789890422853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92257815746759719853897137 69193361810069789890422853)
          ·
            refine ⟨12973755339388085604454285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69193361810069789890422853 12973755339388085604454285)
            ·
              refine ⟨4865158252270532101670357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12973755339388085604454285 4865158252270532101670357)
              ·
                refine ⟨114027146537590596132899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4865158252270532101670357 114027146537590596132899)
                ·
                  rfl

theorem cell23_5995811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 7].length) (baseStart_5995811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995811 prefixEnd_5995811 := by exact prefixLift 5995811
  have htrace : WordTrace (prefixWord ++ tailWord_5995811) baseStart_5995811 baseEnd_5995811 := by
    simpa [prefixWord, tailWord_5995811, baseEnd_5995811] using wordTrace_append hprefix tailTrace_5995811
  have hstable : (prefixWord ++ tailWord_5995811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995811).length < 2 ^ (prefixWord ++ tailWord_5995811).sum := by decide
  have hdescent : baseEnd_5995811 < baseStart_5995811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995818 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5995818 : Nat := 118140960795 + 5995818 * 2 ^ 59
def prefixEnd_5995818 : Nat := 4983230072969 + 3 ^ 40 * 5995818 * 2
def baseEnd_5995818 : Nat := 3078736550879527568200741

theorem tailTrace_5995818 : CollatzResearch.WordTrace tailWord_5995818 prefixEnd_5995818 3078736550879527568200741 := by
  unfold tailWord_5995818
  simp only [CollatzResearch.WordTrace]
  refine ⟨54671362048045716258593027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145790298794788576689581405 54671362048045716258593027)
  ·
    refine ⟨82007043072068574387889541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54671362048045716258593027 82007043072068574387889541)
    ·
      refine ⟨15376320576012857697729289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82007043072068574387889541 15376320576012857697729289)
      ·
        refine ⟨11532240432009643273296967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15376320576012857697729289 11532240432009643273296967)
        ·
          refine ⟨17298360648014464909945451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532240432009643273296967 17298360648014464909945451)
          ·
            refine ⟨25947540972021697364918177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298360648014464909945451 25947540972021697364918177)
            ·
              refine ⟨19460655729016273023688633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25947540972021697364918177 19460655729016273023688633)
              ·
                refine ⟨14595491796762204767766475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19460655729016273023688633 14595491796762204767766475)
                ·
                  refine ⟨21893237695143307151649713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14595491796762204767766475 21893237695143307151649713)
                  ·
                    refine ⟨16419928271357480363737285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21893237695143307151649713 16419928271357480363737285)
                    ·
                      refine ⟨3078736550879527568200741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16419928271357480363737285 3078736550879527568200741)
                      ·
                        rfl

theorem cell23_5995818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5995818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995818 prefixEnd_5995818 := by exact prefixLift 5995818
  have htrace : WordTrace (prefixWord ++ tailWord_5995818) baseStart_5995818 baseEnd_5995818 := by
    simpa [prefixWord, tailWord_5995818, baseEnd_5995818] using wordTrace_append hprefix tailTrace_5995818
  have hstable : (prefixWord ++ tailWord_5995818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995818).length < 2 ^ (prefixWord ++ tailWord_5995818).sum := by decide
  have hdescent : baseEnd_5995818 < baseStart_5995818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995825 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_5995825 : Nat := 118140960795 + 5995825 * 2 ^ 59
def prefixEnd_5995825 : Nat := 4983230072969 + 3 ^ 40 * 5995825 * 2
def baseEnd_5995825 : Nat := 3078740145244109040813209

theorem tailTrace_5995825 : CollatzResearch.WordTrace tailWord_5995825 prefixEnd_5995825 3078740145244109040813209 := by
  unfold tailWord_5995825
  simp only [CollatzResearch.WordTrace]
  refine ⟨218685703503157505229876929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145790469002105003486584619 218685703503157505229876929)
  ·
    refine ⟨164014277627368128922407697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218685703503157505229876929 164014277627368128922407697)
    ·
      refine ⟨123010708220526096691805773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164014277627368128922407697 123010708220526096691805773)
      ·
        refine ⟨46129015582697286259427165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123010708220526096691805773 46129015582697286259427165)
        ·
          refine ⟨17298380843511482347285187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46129015582697286259427165 17298380843511482347285187)
          ·
            refine ⟨25947571265267223520927781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298380843511482347285187 25947571265267223520927781)
            ·
              refine ⟨4865169612237604410173959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25947571265267223520927781 4865169612237604410173959)
              ·
                refine ⟨7297754418356406615260939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865169612237604410173959 7297754418356406615260939)
                ·
                  refine ⟨10946631627534609922891409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297754418356406615260939 10946631627534609922891409)
                  ·
                    refine ⟨8209973720650957442168557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10946631627534609922891409 8209973720650957442168557)
                    ·
                      refine ⟨3078740145244109040813209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8209973720650957442168557 3078740145244109040813209)
                      ·
                        rfl

theorem cell23_5995825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_5995825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995825 prefixEnd_5995825 := by exact prefixLift 5995825
  have htrace : WordTrace (prefixWord ++ tailWord_5995825) baseStart_5995825 baseEnd_5995825 := by
    simpa [prefixWord, tailWord_5995825, baseEnd_5995825] using wordTrace_append hprefix tailTrace_5995825
  have hstable : (prefixWord ++ tailWord_5995825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995825).length < 2 ^ (prefixWord ++ tailWord_5995825).sum := by decide
  have hdescent : baseEnd_5995825 < baseStart_5995825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995862 : List Nat := [5, 2, 3, 1, 1, 1, 1, 9]
def baseStart_5995862 : Nat := 118140960795 + 5995862 * 2 ^ 59
def prefixEnd_5995862 : Nat := 4983230072969 + 3 ^ 40 * 5995862 * 2
def baseEnd_5995862 : Nat := 114028116445493533187057

theorem tailTrace_5995862 : CollatzResearch.WordTrace tailWord_5995862 prefixEnd_5995862 114028116445493533187057 := by
  unfold tailWord_5995862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667940812751466284310865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145791368669348973699315893 13667940812751466284310865)
  ·
    refine ⟨10250955609563599713233149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13667940812751466284310865 10250955609563599713233149)
    ·
      refine ⟨3844108353586349892462431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10250955609563599713233149 3844108353586349892462431)
      ·
        refine ⟨5766162530379524838693647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844108353586349892462431 5766162530379524838693647)
        ·
          refine ⟨8649243795569287258040471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5766162530379524838693647 8649243795569287258040471)
          ·
            refine ⟨12973865693353930887060707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8649243795569287258040471 12973865693353930887060707)
            ·
              refine ⟨19460798540030896330591061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973865693353930887060707 19460798540030896330591061)
              ·
                refine ⟨114028116445493533187057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19460798540030896330591061 114028116445493533187057)
                ·
                  rfl

theorem cell23_5995862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_5995862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995862 prefixEnd_5995862 := by exact prefixLift 5995862
  have htrace : WordTrace (prefixWord ++ tailWord_5995862) baseStart_5995862 baseEnd_5995862 := by
    simpa [prefixWord, tailWord_5995862, baseEnd_5995862] using wordTrace_append hprefix tailTrace_5995862
  have hstable : (prefixWord ++ tailWord_5995862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995862).length < 2 ^ (prefixWord ++ tailWord_5995862).sum := by decide
  have hdescent : baseEnd_5995862 < baseStart_5995862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995895 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_5995895 : Nat := 118140960795 + 5995895 * 2 ^ 59
def prefixEnd_5995895 : Nat := 4983230072969 + 3 ^ 40 * 5995895 * 2
def baseEnd_5995895 : Nat := 3078776088889923766937887

theorem tailTrace_5995895 : CollatzResearch.WordTrace tailWord_5995895 prefixEnd_5995895 3078776088889923766937887 := by
  unfold tailWord_5995895
  simp only [CollatzResearch.WordTrace]
  refine ⟨218688256612903907184925139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145792171075269271456616759 218688256612903907184925139)
  ·
    refine ⟨328032384919355860777387709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218688256612903907184925139 328032384919355860777387709)
    ·
      refine ⟨123012144344758447791520391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328032384919355860777387709 123012144344758447791520391)
      ·
        refine ⟨184518216517137671687280587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123012144344758447791520391 184518216517137671687280587)
        ·
          refine ⟨276777324775706507530920881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184518216517137671687280587 276777324775706507530920881)
          ·
            refine ⟨207582993581779880648190661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276777324775706507530920881 207582993581779880648190661)
            ·
              refine ⟨38921811296583727621535749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207582993581779880648190661 38921811296583727621535749)
              ·
                refine ⟨7297839618109448929037953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38921811296583727621535749 7297839618109448929037953)
                ·
                  refine ⟨5473379713582086696778465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297839618109448929037953 5473379713582086696778465)
                  ·
                    refine ⟨4105034785186565022583849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473379713582086696778465 4105034785186565022583849)
                    ·
                      refine ⟨3078776088889923766937887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105034785186565022583849 3078776088889923766937887)
                      ·
                        rfl

theorem cell23_5995895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_5995895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995895 prefixEnd_5995895 := by exact prefixLift 5995895
  have htrace : WordTrace (prefixWord ++ tailWord_5995895) baseStart_5995895 baseEnd_5995895 := by
    simpa [prefixWord, tailWord_5995895, baseEnd_5995895] using wordTrace_append hprefix tailTrace_5995895
  have hstable : (prefixWord ++ tailWord_5995895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995895).length < 2 ^ (prefixWord ++ tailWord_5995895).sum := by decide
  have hdescent : baseEnd_5995895 < baseStart_5995895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995906 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5995906 : Nat := 118140960795 + 5995906 * 2 ^ 59
def prefixEnd_5995906 : Nat := 4983230072969 + 3 ^ 40 * 5995906 * 2
def baseEnd_5995906 : Nat := 3078781737177123223900337

theorem tailTrace_5995906 : CollatzResearch.WordTrace tailWord_5995906 prefixEnd_5995906 3078781737177123223900337 := by
  unfold tailWord_5995906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54672164453966014015893893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145792438543909370709050381 54672164453966014015893893)
  ·
    refine ⟨10251030835118627627980105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54672164453966014015893893 10251030835118627627980105)
    ·
      refine ⟨7688273126338970720985079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10251030835118627627980105 7688273126338970720985079)
      ·
        refine ⟨11532409689508456081477619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688273126338970720985079 11532409689508456081477619)
        ·
          refine ⟨17298614534262684122216429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532409689508456081477619 17298614534262684122216429)
          ·
            refine ⟨6486980450348506545831161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17298614534262684122216429 6486980450348506545831161)
            ·
              refine ⟨4865235337761379909373371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486980450348506545831161 4865235337761379909373371)
              ·
                refine ⟨7297853006642069864060057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865235337761379909373371 7297853006642069864060057)
                ·
                  refine ⟨5473389754981552398045043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297853006642069864060057 5473389754981552398045043)
                  ·
                    refine ⟨8210084632472328597067565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5473389754981552398045043 8210084632472328597067565)
                    ·
                      refine ⟨3078781737177123223900337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210084632472328597067565 3078781737177123223900337)
                      ·
                        rfl

theorem cell23_5995906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5995906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995906 prefixEnd_5995906 := by exact prefixLift 5995906
  have htrace : WordTrace (prefixWord ++ tailWord_5995906) baseStart_5995906 baseEnd_5995906 := by
    simpa [prefixWord, tailWord_5995906, baseEnd_5995906] using wordTrace_append hprefix tailTrace_5995906
  have hstable : (prefixWord ++ tailWord_5995906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995906).length < 2 ^ (prefixWord ++ tailWord_5995906).sum := by decide
  have hdescent : baseEnd_5995906 < baseStart_5995906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995912 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5995912 : Nat := 118140960795 + 5995912 * 2 ^ 59
def prefixEnd_5995912 : Nat := 4983230072969 + 3 ^ 40 * 5995912 * 2
def baseEnd_5995912 : Nat := 3078784818061050200425309

theorem tailTrace_5995912 : CollatzResearch.WordTrace tailWord_5995912 prefixEnd_5995912 3078784818061050200425309 := by
  unfold tailWord_5995912
  simp only [CollatzResearch.WordTrace]
  refine ⟨109344438326921159544146995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145792584435894879392195993 109344438326921159544146995)
  ·
    refine ⟨164016657490381739316220493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109344438326921159544146995 164016657490381739316220493)
    ·
      refine ⟨61506246558893152243582685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164016657490381739316220493 61506246558893152243582685)
      ·
        refine ⟨23064842459584932091343507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61506246558893152243582685 23064842459584932091343507)
        ·
          refine ⟨34597263689377398137015261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23064842459584932091343507 34597263689377398137015261)
          ·
            refine ⟨12973973883516524301380723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34597263689377398137015261 12973973883516524301380723)
            ·
              refine ⟨19460960825274786452071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973973883516524301380723 19460960825274786452071085)
              ·
                refine ⟨7297860309478044919526657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19460960825274786452071085 7297860309478044919526657)
                ·
                  refine ⟨5473395232108533689644993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297860309478044919526657 5473395232108533689644993)
                  ·
                    refine ⟨4105046424081400267233745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473395232108533689644993 4105046424081400267233745)
                    ·
                      refine ⟨3078784818061050200425309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105046424081400267233745 3078784818061050200425309)
                      ·
                        rfl

theorem cell23_5995912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5995912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995912 prefixEnd_5995912 := by exact prefixLift 5995912
  have htrace : WordTrace (prefixWord ++ tailWord_5995912) baseStart_5995912 baseEnd_5995912 := by
    simpa [prefixWord, tailWord_5995912, baseEnd_5995912] using wordTrace_append hprefix tailTrace_5995912
  have hstable : (prefixWord ++ tailWord_5995912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995912).length < 2 ^ (prefixWord ++ tailWord_5995912).sum := by decide
  have hdescent : baseEnd_5995912 < baseStart_5995912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995968 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2]
def baseStart_5995968 : Nat := 118140960795 + 5995968 * 2 ^ 59
def prefixEnd_5995968 : Nat := 4983230072969 + 3 ^ 40 * 5995968 * 2
def baseEnd_5995968 : Nat := 3078813572977701981325051

theorem tailTrace_5995968 : CollatzResearch.WordTrace tailWord_5995968 prefixEnd_5995968 3078813572977701981325051 := by
  unfold tailWord_5995968
  simp only [CollatzResearch.WordTrace]
  refine ⟨109345459570819720326166279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145793946094426293768221705 109345459570819720326166279)
  ·
    refine ⟨164018189356229580489249419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109345459570819720326166279 164018189356229580489249419)
    ·
      refine ⟨246027284034344370733874129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164018189356229580489249419 246027284034344370733874129)
      ·
        refine ⟨184520463025758278050405597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246027284034344370733874129 184520463025758278050405597)
        ·
          refine ⟨69195173634659354268902099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184520463025758278050405597 69195173634659354268902099)
          ·
            refine ⟨103792760451989031403353149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69195173634659354268902099 103792760451989031403353149)
            ·
              refine ⟨38922285169495886776257431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103792760451989031403353149 38922285169495886776257431)
              ·
                refine ⟨58383427754243830164386147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38922285169495886776257431 58383427754243830164386147)
                ·
                  refine ⟨87575141631365745246579221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58383427754243830164386147 87575141631365745246579221)
                  ·
                    refine ⟨4105084763970269308433401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87575141631365745246579221 4105084763970269308433401)
                    ·
                      refine ⟨3078813572977701981325051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105084763970269308433401 3078813572977701981325051)
                      ·
                        rfl

theorem cell23_5995968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_5995968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995968 prefixEnd_5995968 := by exact prefixLift 5995968
  have htrace : WordTrace (prefixWord ++ tailWord_5995968) baseStart_5995968 baseEnd_5995968 := by
    simpa [prefixWord, tailWord_5995968, baseEnd_5995968] using wordTrace_append hprefix tailTrace_5995968
  have hstable : (prefixWord ++ tailWord_5995968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995968).length < 2 ^ (prefixWord ++ tailWord_5995968).sum := by decide
  have hdescent : baseEnd_5995968 < baseStart_5995968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5995978 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_5995978 : Nat := 118140960795 + 5995978 * 2 ^ 59
def prefixEnd_5995978 : Nat := 4983230072969 + 3 ^ 40 * 5995978 * 2
def baseEnd_5995978 : Nat := 1026272902594748980733335

theorem tailTrace_5995978 : CollatzResearch.WordTrace tailWord_5995978 prefixEnd_5995978 1026272902594748980733335 := by
  unfold tailWord_5995978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54672820967900803090049147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145794189247735474906797725 54672820967900803090049147)
  ·
    refine ⟨82009231451851204635073721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54672820967900803090049147 82009231451851204635073721)
    ·
      refine ⟨61506923588888403476305291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82009231451851204635073721 61506923588888403476305291)
      ·
        refine ⟨92260385383332605214457937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61506923588888403476305291 92260385383332605214457937)
        ·
          refine ⟨69195289037499453910843453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92260385383332605214457937 69195289037499453910843453)
          ·
            refine ⟨25948233389062295216566295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69195289037499453910843453 25948233389062295216566295)
            ·
              refine ⟨38922350083593442824849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25948233389062295216566295 38922350083593442824849443)
              ·
                refine ⟨58383525125390164237274165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38922350083593442824849443 58383525125390164237274165)
                ·
                  refine ⟨5473455480505327897244453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58383525125390164237274165 5473455480505327897244453)
                  ·
                    refine ⟨1026272902594748980733335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473455480505327897244453 1026272902594748980733335)
                    ·
                      rfl

theorem cell23_5995978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_5995978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5995978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5995978 prefixEnd_5995978 := by exact prefixLift 5995978
  have htrace : WordTrace (prefixWord ++ tailWord_5995978) baseStart_5995978 baseEnd_5995978 := by
    simpa [prefixWord, tailWord_5995978, baseEnd_5995978] using wordTrace_append hprefix tailTrace_5995978
  have hstable : (prefixWord ++ tailWord_5995978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5995978).length < 2 ^ (prefixWord ++ tailWord_5995978).sum := by decide
  have hdescent : baseEnd_5995978 < baseStart_5995978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5995978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996046 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_5996046 : Nat := 118140960795 + 5996046 * 2 ^ 59
def prefixEnd_5996046 : Nat := 4983230072969 + 3 ^ 40 * 5996046 * 2
def baseEnd_5996046 : Nat := 1026284541489584225383231

theorem tailTrace_5996046 : CollatzResearch.WordTrace tailWord_5996046 prefixEnd_5996046 1026284541489584225383231 := by
  unfold tailWord_5996046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336720504419607496708999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145795842690237906649114661 27336720504419607496708999)
  ·
    refine ⟨41005080756629411245063499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27336720504419607496708999 41005080756629411245063499)
    ·
      refine ⟨61507621134944116867595249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41005080756629411245063499 61507621134944116867595249)
      ·
        refine ⟨46130715851208087650696437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61507621134944116867595249 46130715851208087650696437)
        ·
          refine ⟨4324754611050758217252791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46130715851208087650696437 4324754611050758217252791)
          ·
            refine ⟨6487131916576137325879187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324754611050758217252791 6487131916576137325879187)
            ·
              refine ⟨9730697874864205988818781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487131916576137325879187 9730697874864205988818781)
              ·
                refine ⟨3649011703074077245807043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9730697874864205988818781 3649011703074077245807043)
                ·
                  refine ⟨5473517554611115868710565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649011703074077245807043 5473517554611115868710565)
                  ·
                    refine ⟨1026284541489584225383231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473517554611115868710565 1026284541489584225383231)
                    ·
                      rfl

theorem cell23_5996046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_5996046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996046 prefixEnd_5996046 := by exact prefixLift 5996046
  have htrace : WordTrace (prefixWord ++ tailWord_5996046) baseStart_5996046 baseEnd_5996046 := by
    simpa [prefixWord, tailWord_5996046, baseEnd_5996046] using wordTrace_append hprefix tailTrace_5996046
  have hstable : (prefixWord ++ tailWord_5996046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996046).length < 2 ^ (prefixWord ++ tailWord_5996046).sum := by decide
  have hdescent : baseEnd_5996046 < baseStart_5996046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996058 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_5996058 : Nat := 118140960795 + 5996058 * 2 ^ 59
def prefixEnd_5996058 : Nat := 4983230072969 + 3 ^ 40 * 5996058 * 2
def baseEnd_5996058 : Nat := 3078859786236606629199637

theorem tailTrace_5996058 : CollatzResearch.WordTrace tailWord_5996058 prefixEnd_5996058 3078859786236606629199637 := by
  unfold tailWord_5996058
  simp only [CollatzResearch.WordTrace]
  refine ⟨54673550427828346505777207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145796134474208924015405885 54673550427828346505777207)
  ·
    refine ⟨82010325641742519758665811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54673550427828346505777207 82010325641742519758665811)
    ·
      refine ⟨123015488462613779637998717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82010325641742519758665811 123015488462613779637998717)
      ·
        refine ⟨46130808173480167364249519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123015488462613779637998717 46130808173480167364249519)
        ·
          refine ⟨69196212260220251046374279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46130808173480167364249519 69196212260220251046374279)
          ·
            refine ⟨103794318390330376569561419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69196212260220251046374279 103794318390330376569561419)
            ·
              refine ⟨155691477585495564854342129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103794318390330376569561419 155691477585495564854342129)
              ·
                refine ⟨116768608189121673640756597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155691477585495564854342129 116768608189121673640756597)
                ·
                  refine ⟨10947057017730156903820931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116768608189121673640756597 10947057017730156903820931)
                  ·
                    refine ⟨16420585526595235355731397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10947057017730156903820931 16420585526595235355731397)
                    ·
                      refine ⟨3078859786236606629199637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16420585526595235355731397 3078859786236606629199637)
                      ·
                        rfl

theorem cell23_5996058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_5996058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996058 prefixEnd_5996058 := by exact prefixLift 5996058
  have htrace : WordTrace (prefixWord ++ tailWord_5996058) baseStart_5996058 baseEnd_5996058 := by
    simpa [prefixWord, tailWord_5996058, baseEnd_5996058] using wordTrace_append hprefix tailTrace_5996058
  have hstable : (prefixWord ++ tailWord_5996058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996058).length < 2 ^ (prefixWord ++ tailWord_5996058).sum := by decide
  have hdescent : baseEnd_5996058 < baseStart_5996058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996088 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_5996088 : Nat := 118140960795 + 5996088 * 2 ^ 59
def prefixEnd_5996088 : Nat := 4983230072969 + 3 ^ 40 * 5996088 * 2
def baseEnd_5996088 : Nat := 3078875190656241511824499

theorem tailTrace_5996088 : CollatzResearch.WordTrace tailWord_5996088 prefixEnd_5996088 3078875190656241511824499 := by
  unfold tailWord_5996088
  simp only [CollatzResearch.WordTrace]
  refine ⟨109347647950602350573350459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145796863934136467431133945 109347647950602350573350459)
  ·
    refine ⟨164021471925903525860025689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109347647950602350573350459 164021471925903525860025689)
    ·
      refine ⟨123016103944427644395019267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164021471925903525860025689 123016103944427644395019267)
      ·
        refine ⟨184524155916641466592528901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123016103944427644395019267 184524155916641466592528901)
        ·
          refine ⟨34598279234370274986099169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184524155916641466592528901 34598279234370274986099169)
          ·
            refine ⟨25948709425777706239574377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34598279234370274986099169 25948709425777706239574377)
            ·
              refine ⟨19461532069333279679680783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25948709425777706239574377 19461532069333279679680783)
              ·
                refine ⟨29192298103999919519521175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19461532069333279679680783 29192298103999919519521175)
                ·
                  refine ⟨43788447155999879279281763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29192298103999919519521175 43788447155999879279281763)
                  ·
                    refine ⟨65682670733999818918922645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43788447155999879279281763 65682670733999818918922645)
                    ·
                      refine ⟨3078875190656241511824499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65682670733999818918922645 3078875190656241511824499)
                      ·
                        rfl

theorem cell23_5996088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_5996088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996088 prefixEnd_5996088 := by exact prefixLift 5996088
  have htrace : WordTrace (prefixWord ++ tailWord_5996088) baseStart_5996088 baseEnd_5996088 := by
    simpa [prefixWord, tailWord_5996088, baseEnd_5996088] using wordTrace_append hprefix tailTrace_5996088
  have hstable : (prefixWord ++ tailWord_5996088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996088).length < 2 ^ (prefixWord ++ tailWord_5996088).sum := by decide
  have hdescent : baseEnd_5996088 < baseStart_5996088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996095 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_5996095 : Nat := 118140960795 + 5996095 * 2 ^ 59
def prefixEnd_5996095 : Nat := 4983230072969 + 3 ^ 40 * 5996095 * 2
def baseEnd_5996095 : Nat := 3078878785020822984436967

theorem tailTrace_5996095 : CollatzResearch.WordTrace tailWord_5996095 prefixEnd_5996095 3078878785020822984436967 := by
  unfold tailWord_5996095
  simp only [CollatzResearch.WordTrace]
  refine ⟨218695551212179341342205739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145797034141452894228137159 218695551212179341342205739)
  ·
    refine ⟨328043326818269012013308609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218695551212179341342205739 328043326818269012013308609)
    ·
      refine ⟨246032495113701759009981457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328043326818269012013308609 246032495113701759009981457)
      ·
        refine ⟨184524371335276319257486093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246032495113701759009981457 184524371335276319257486093)
        ·
          refine ⟨69196639250728619721557285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184524371335276319257486093 69196639250728619721557285)
          ·
            refine ⟨12974369859511616197791991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69196639250728619721557285 12974369859511616197791991)
            ·
              refine ⟨19461554789267424296687987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12974369859511616197791991 19461554789267424296687987)
              ·
                refine ⟨29192332183901136445031981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19461554789267424296687987 29192332183901136445031981)
                ·
                  refine ⟨10947124568962926166886993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29192332183901136445031981 10947124568962926166886993)
                  ·
                    refine ⟨8210343426722194625165245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10947124568962926166886993 8210343426722194625165245)
                    ·
                      refine ⟨3078878785020822984436967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210343426722194625165245 3078878785020822984436967)
                      ·
                        rfl

theorem cell23_5996095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_5996095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996095 prefixEnd_5996095 := by exact prefixLift 5996095
  have htrace : WordTrace (prefixWord ++ tailWord_5996095) baseStart_5996095 baseEnd_5996095 := by
    simpa [prefixWord, tailWord_5996095, baseEnd_5996095] using wordTrace_append hprefix tailTrace_5996095
  have hstable : (prefixWord ++ tailWord_5996095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996095).length < 2 ^ (prefixWord ++ tailWord_5996095).sum := by decide
  have hdescent : baseEnd_5996095 < baseStart_5996095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996112 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3]
def baseStart_5996112 : Nat := 118140960795 + 5996112 * 2 ^ 59
def prefixEnd_5996112 : Nat := 4983230072969 + 3 ^ 40 * 5996112 * 2
def baseEnd_5996112 : Nat := 3078887514191949417924389

theorem tailTrace_5996112 : CollatzResearch.WordTrace tailWord_5996112 prefixEnd_5996112 3078887514191949417924389 := by
  unfold tailWord_5996112
  simp only [CollatzResearch.WordTrace]
  refine ⟨109348085626558876622787295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145797447502078502163716393 109348085626558876622787295)
  ·
    refine ⟨164022128439838314934180943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109348085626558876622787295 164022128439838314934180943)
    ·
      refine ⟨246033192659757472401271415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164022128439838314934180943 246033192659757472401271415)
      ·
        refine ⟨369049788989636208601907123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246033192659757472401271415 369049788989636208601907123)
        ·
          refine ⟨553574683484454312902860685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369049788989636208601907123 553574683484454312902860685)
          ·
            refine ⟨207590506306670367338572757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 553574683484454312902860685 207590506306670367338572757)
            ·
              refine ⟨4865402491562586734497799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207590506306670367338572757 4865402491562586734497799)
              ·
                refine ⟨7298103737343880101746699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865402491562586734497799 7298103737343880101746699)
                ·
                  refine ⟨10947155606015820152620049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298103737343880101746699 10947155606015820152620049)
                  ·
                    refine ⟨8210366704511865114465037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10947155606015820152620049 8210366704511865114465037)
                    ·
                      refine ⟨3078887514191949417924389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210366704511865114465037 3078887514191949417924389)
                      ·
                        rfl

theorem cell23_5996112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 2, 3].length) (baseStart_5996112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996112 prefixEnd_5996112 := by exact prefixLift 5996112
  have htrace : WordTrace (prefixWord ++ tailWord_5996112) baseStart_5996112 baseEnd_5996112 := by
    simpa [prefixWord, tailWord_5996112, baseEnd_5996112] using wordTrace_append hprefix tailTrace_5996112
  have hstable : (prefixWord ++ tailWord_5996112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996112).length < 2 ^ (prefixWord ++ tailWord_5996112).sum := by decide
  have hdescent : baseEnd_5996112 < baseStart_5996112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996169 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 1, 3, 2]
def baseStart_5996169 : Nat := 118140960795 + 5996169 * 2 ^ 59
def prefixEnd_5996169 : Nat := 4983230072969 + 3 ^ 40 * 5996169 * 2
def baseEnd_5996169 : Nat := 3078916782589255694911627

theorem tailTrace_5996169 : CollatzResearch.WordTrace tailWord_5996169 prefixEnd_5996169 3078916782589255694911627 := by
  unfold tailWord_5996169
  simp only [CollatzResearch.WordTrace]
  refine ⟨218698250213911251980399561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145798833475940834653599707 218698250213911251980399561)
  ·
    refine ⟨164023687660433438985299671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218698250213911251980399561 164023687660433438985299671)
    ·
      refine ⟨246035531490650158477949507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164023687660433438985299671 246035531490650158477949507)
      ·
        refine ⟨369053297235975237716924261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246035531490650158477949507 369053297235975237716924261)
        ·
          refine ⟨69197493231745357071923299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369053297235975237716924261 69197493231745357071923299)
          ·
            refine ⟨103796239847618035607884949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69197493231745357071923299 103796239847618035607884949)
            ·
              refine ⟨4865448742857095419119607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103796239847618035607884949 4865448742857095419119607)
              ·
                refine ⟨7298173114285643128679411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865448742857095419119607 7298173114285643128679411)
                ·
                  refine ⟨10947259671428464693019117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298173114285643128679411 10947259671428464693019117)
                  ·
                    refine ⟨4105222376785674259882169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10947259671428464693019117 4105222376785674259882169)
                    ·
                      refine ⟨3078916782589255694911627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105222376785674259882169 3078916782589255694911627)
                      ·
                        rfl

theorem cell23_5996169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 3, 2].length) (baseStart_5996169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996169 prefixEnd_5996169 := by exact prefixLift 5996169
  have htrace : WordTrace (prefixWord ++ tailWord_5996169) baseStart_5996169 baseEnd_5996169 := by
    simpa [prefixWord, tailWord_5996169, baseEnd_5996169] using wordTrace_append hprefix tailTrace_5996169
  have hstable : (prefixWord ++ tailWord_5996169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996169).length < 2 ^ (prefixWord ++ tailWord_5996169).sum := by decide
  have hdescent : baseEnd_5996169 < baseStart_5996169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996205 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 7]
def baseStart_5996205 : Nat := 118140960795 + 5996205 * 2 ^ 59
def prefixEnd_5996205 : Nat := 4983230072969 + 3 ^ 40 * 5996205 * 2
def baseEnd_5996205 : Nat := 342103918654757506006829

theorem tailTrace_5996205 : CollatzResearch.WordTrace tailWord_5996205 prefixEnd_5996205 342103918654757506006829 := by
  unfold tailWord_5996205
  simp only [CollatzResearch.WordTrace]
  refine ⟨218699563241780830128710069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145799708827853886752473379 218699563241780830128710069)
  ·
    refine ⟨20503084053916952824566569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218699563241780830128710069 20503084053916952824566569)
    ·
      refine ⟨15377313040437714618424927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20503084053916952824566569 15377313040437714618424927)
      ·
        refine ⟨23065969560656571927637391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15377313040437714618424927 23065969560656571927637391)
        ·
          refine ⟨34598954340984857891456087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23065969560656571927637391 34598954340984857891456087)
          ·
            refine ⟨51898431511477286837184131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34598954340984857891456087 51898431511477286837184131)
            ·
              refine ⟨77847647267215930255776197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51898431511477286837184131 77847647267215930255776197)
              ·
                refine ⟨14596433862602986922958037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77847647267215930255776197 14596433862602986922958037)
                ·
                  refine ⟨342103918654757506006829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14596433862602986922958037 342103918654757506006829)
                  ·
                    rfl

theorem cell23_5996205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_5996205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996205 prefixEnd_5996205 := by exact prefixLift 5996205
  have htrace : WordTrace (prefixWord ++ tailWord_5996205) baseStart_5996205 baseEnd_5996205 := by
    simpa [prefixWord, tailWord_5996205, baseEnd_5996205] using wordTrace_append hprefix tailTrace_5996205
  have hstable : (prefixWord ++ tailWord_5996205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996205).length < 2 ^ (prefixWord ++ tailWord_5996205).sum := by decide
  have hdescent : baseEnd_5996205 < baseStart_5996205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996255 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_5996255 : Nat := 118140960795 + 5996255 * 2 ^ 59
def prefixEnd_5996255 : Nat := 4983230072969 + 3 ^ 40 * 5996255 * 2
def baseEnd_5996255 : Nat := 3078960941925542358436231

theorem tailTrace_5996255 : CollatzResearch.WordTrace tailWord_5996255 prefixEnd_5996255 3078960941925542358436231 := by
  unfold tailWord_5996255
  simp only [CollatzResearch.WordTrace]
  refine ⟨218701386891599688668030219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145800924594399792445353479 218701386891599688668030219)
  ·
    refine ⟨328052080337399533002045329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218701386891599688668030219 328052080337399533002045329)
    ·
      refine ⟨246039060253049649751533997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328052080337399533002045329 246039060253049649751533997)
      ·
        refine ⟨92264647594893618656825249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246039060253049649751533997 92264647594893618656825249)
        ·
          refine ⟨69198485696170213992618937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92264647594893618656825249 69198485696170213992618937)
          ·
            refine ⟨51898864272127660494464203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69198485696170213992618937 51898864272127660494464203)
            ·
              refine ⟨77848296408191490741696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51898864272127660494464203 77848296408191490741696305)
              ·
                refine ⟨58386222306143618056272229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77848296408191490741696305 58386222306143618056272229)
                ·
                  refine ⟨10947416682401928385551043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58386222306143618056272229 10947416682401928385551043)
                  ·
                    refine ⟨16421125023602892578326565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10947416682401928385551043 16421125023602892578326565)
                    ·
                      refine ⟨3078960941925542358436231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16421125023602892578326565 3078960941925542358436231)
                      ·
                        rfl

theorem cell23_5996255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_5996255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996255 prefixEnd_5996255 := by exact prefixLift 5996255
  have htrace : WordTrace (prefixWord ++ tailWord_5996255) baseStart_5996255 baseEnd_5996255 := by
    simpa [prefixWord, tailWord_5996255, baseEnd_5996255] using wordTrace_append hprefix tailTrace_5996255
  have hstable : (prefixWord ++ tailWord_5996255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996255).length < 2 ^ (prefixWord ++ tailWord_5996255).sum := by decide
  have hdescent : baseEnd_5996255 < baseStart_5996255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996265 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_5996265 : Nat := 118140960795 + 5996265 * 2 ^ 59
def prefixEnd_5996265 : Nat := 4983230072969 + 3 ^ 40 * 5996265 * 2
def baseEnd_5996265 : Nat := 1026322025577362439770395

theorem tailTrace_5996265 : CollatzResearch.WordTrace tailWord_5996265 prefixEnd_5996265 1026322025577362439770395 := by
  unfold tailWord_5996265
  simp only [CollatzResearch.WordTrace]
  refine ⟨218701751621563460375894249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145801167747708973583929499 218701751621563460375894249)
  ·
    refine ⟨164026313716172595281920687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218701751621563460375894249 164026313716172595281920687)
    ·
      refine ⟨246039470574258892922881031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164026313716172595281920687 246039470574258892922881031)
      ·
        refine ⟨369059205861388339384321547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246039470574258892922881031 369059205861388339384321547)
        ·
          refine ⟨553588808792082509076482321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369059205861388339384321547 553588808792082509076482321)
          ·
            refine ⟨415191606594061881807361741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553588808792082509076482321 415191606594061881807361741)
            ·
              refine ⟨155696852472773205677760653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415191606594061881807361741 155696852472773205677760653)
              ·
                refine ⟨58386319677289952129160245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155696852472773205677760653 58386319677289952129160245)
                ·
                  refine ⟨5473717469745933012108773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58386319677289952129160245 5473717469745933012108773)
                  ·
                    refine ⟨1026322025577362439770395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473717469745933012108773 1026322025577362439770395)
                    ·
                      rfl

theorem cell23_5996265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_5996265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996265 prefixEnd_5996265 := by exact prefixLift 5996265
  have htrace : WordTrace (prefixWord ++ tailWord_5996265) baseStart_5996265 baseEnd_5996265 := by
    simpa [prefixWord, tailWord_5996265, baseEnd_5996265] using wordTrace_append hprefix tailTrace_5996265
  have hstable : (prefixWord ++ tailWord_5996265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996265).length < 2 ^ (prefixWord ++ tailWord_5996265).sum := by decide
  have hdescent : baseEnd_5996265 < baseStart_5996265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996275 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3]
def baseStart_5996275 : Nat := 118140960795 + 5996275 * 2 ^ 59
def prefixEnd_5996275 : Nat := 4983230072969 + 3 ^ 40 * 5996275 * 2
def baseEnd_5996275 : Nat := 3078971211538632280186139

theorem tailTrace_5996275 : CollatzResearch.WordTrace tailWord_5996275 prefixEnd_5996275 3078971211538632280186139 := by
  unfold tailWord_5996275
  simp only [CollatzResearch.WordTrace]
  refine ⟨218702116351527232083758279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145801410901018154722505519 218702116351527232083758279)
  ·
    refine ⟨328053174527290848125637419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218702116351527232083758279 328053174527290848125637419)
    ·
      refine ⟨492079761790936272188456129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328053174527290848125637419 492079761790936272188456129)
      ·
        refine ⟨369059821343202204141342097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492079761790936272188456129 369059821343202204141342097)
        ·
          refine ⟨276794866007401653106006573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369059821343202204141342097 276794866007401653106006573)
          ·
            refine ⟨103798074752775619914752465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276794866007401653106006573 103798074752775619914752465)
            ·
              refine ⟨77848556064581714936064349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103798074752775619914752465 77848556064581714936064349)
              ·
                refine ⟨29193208524218143101024131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77848556064581714936064349 29193208524218143101024131)
                ·
                  refine ⟨43789812786327214651536197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29193208524218143101024131 43789812786327214651536197)
                  ·
                    refine ⟨8210589897436352747163037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43789812786327214651536197 8210589897436352747163037)
                    ·
                      refine ⟨3078971211538632280186139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210589897436352747163037 3078971211538632280186139)
                      ·
                        rfl

theorem cell23_5996275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_5996275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996275 prefixEnd_5996275 := by exact prefixLift 5996275
  have htrace : WordTrace (prefixWord ++ tailWord_5996275) baseStart_5996275 baseEnd_5996275 := by
    simpa [prefixWord, tailWord_5996275, baseEnd_5996275] using wordTrace_append hprefix tailTrace_5996275
  have hstable : (prefixWord ++ tailWord_5996275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996275).length < 2 ^ (prefixWord ++ tailWord_5996275).sum := by decide
  have hdescent : baseEnd_5996275 < baseStart_5996275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996305 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_5996305 : Nat := 118140960795 + 5996305 * 2 ^ 59
def prefixEnd_5996305 : Nat := 4983230072969 + 3 ^ 40 * 5996305 * 2
def baseEnd_5996305 : Nat := 3078986615958267162811001

theorem tailTrace_5996305 : CollatzResearch.WordTrace tailWord_5996305 prefixEnd_5996305 3078986615958267162811001 := by
  unfold tailWord_5996305
  simp only [CollatzResearch.WordTrace]
  refine ⟨218703210541418547207350369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145802140360945698138233579 218703210541418547207350369)
  ·
    refine ⟨164027407906063910405512777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218703210541418547207350369 164027407906063910405512777)
    ·
      refine ⟨123020555929547932804134583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164027407906063910405512777 123020555929547932804134583)
      ·
        refine ⟨184530833894321899206201875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123020555929547932804134583 184530833894321899206201875)
        ·
          refine ⟨276796250841482848809302813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184530833894321899206201875 276796250841482848809302813)
          ·
            refine ⟨103798594065556068303488555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276796250841482848809302813 103798594065556068303488555)
            ·
              refine ⟨155697891098334102455232833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103798594065556068303488555 155697891098334102455232833)
              ·
                refine ⟨116773418323750576841424625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155697891098334102455232833 116773418323750576841424625)
                ·
                  refine ⟨87580063742812932631068469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116773418323750576841424625 87580063742812932631068469)
                  ·
                    refine ⟨8210630975888712434162669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87580063742812932631068469 8210630975888712434162669)
                    ·
                      refine ⟨3078986615958267162811001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210630975888712434162669 3078986615958267162811001)
                      ·
                        rfl

theorem cell23_5996305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_5996305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996305 prefixEnd_5996305 := by exact prefixLift 5996305
  have htrace : WordTrace (prefixWord ++ tailWord_5996305) baseStart_5996305 baseEnd_5996305 := by
    simpa [prefixWord, tailWord_5996305, baseEnd_5996305] using wordTrace_append hprefix tailTrace_5996305
  have hstable : (prefixWord ++ tailWord_5996305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996305).length < 2 ^ (prefixWord ++ tailWord_5996305).sum := by decide
  have hdescent : baseEnd_5996305 < baseStart_5996305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996306 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5996306 : Nat := 118140960795 + 5996306 * 2 ^ 59
def prefixEnd_5996306 : Nat := 4983230072969 + 3 ^ 40 * 5996306 * 2
def baseEnd_5996306 : Nat := 3078987129438921658898497

theorem tailTrace_5996306 : CollatzResearch.WordTrace tailWord_5996306 prefixEnd_5996306 3078987129438921658898497 := by
  unfold tailWord_5996306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54675811753603731094534193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145802164676276616252091181 54675811753603731094534193)
  ·
    refine ⟨41006858815202798320900645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54675811753603731094534193 41006858815202798320900645)
    ·
      refine ⟨7688786027850524685168871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41006858815202798320900645 7688786027850524685168871)
      ·
        refine ⟨11533179041775787027753307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688786027850524685168871 11533179041775787027753307)
        ·
          refine ⟨17299768562663680541629961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533179041775787027753307 17299768562663680541629961)
          ·
            refine ⟨12974826421997760406222471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17299768562663680541629961 12974826421997760406222471)
            ·
              refine ⟨19462239632996640609333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12974826421997760406222471 19462239632996640609333707)
              ·
                refine ⟨29193359449494960914000561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19462239632996640609333707 29193359449494960914000561)
                ·
                  refine ⟨21895019587121220685500421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29193359449494960914000561 21895019587121220685500421)
                  ·
                    refine ⟨4105316172585228878531329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21895019587121220685500421 4105316172585228878531329)
                    ·
                      refine ⟨3078987129438921658898497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105316172585228878531329 3078987129438921658898497)
                      ·
                        rfl

theorem cell23_5996306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5996306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996306 prefixEnd_5996306 := by exact prefixLift 5996306
  have htrace : WordTrace (prefixWord ++ tailWord_5996306) baseStart_5996306 baseEnd_5996306 := by
    simpa [prefixWord, tailWord_5996306, baseEnd_5996306] using wordTrace_append hprefix tailTrace_5996306
  have hstable : (prefixWord ++ tailWord_5996306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996306).length < 2 ^ (prefixWord ++ tailWord_5996306).sum := by decide
  have hdescent : baseEnd_5996306 < baseStart_5996306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996385 : List Nat := [1, 2, 3, 1, 1, 1, 5, 9]
def baseStart_5996385 : Nat := 118140960795 + 5996385 * 2 ^ 59
def prefixEnd_5996385 : Nat := 4983230072969 + 3 ^ 40 * 5996385 * 2
def baseEnd_5996385 : Nat := 114038062755949142585579

theorem tailTrace_5996385 : CollatzResearch.WordTrace tailWord_5996385 prefixEnd_5996385 114038062755949142585579 := by
  unfold tailWord_5996385
  simp only [CollatzResearch.WordTrace]
  refine ⟨218706128381128720870262609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145804085587419147246841739 218706128381128720870262609)
  ·
    refine ⟨164029596285846540652696957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218706128381128720870262609 164029596285846540652696957)
    ·
      refine ⟨61511098607192452744761359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164029596285846540652696957 61511098607192452744761359)
      ·
        refine ⟨92266647910788679117142039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61511098607192452744761359 92266647910788679117142039)
        ·
          refine ⟨138399971866183018675713059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92266647910788679117142039 138399971866183018675713059)
          ·
            refine ⟨207599957799274528013569589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138399971866183018675713059 207599957799274528013569589)
            ·
              refine ⟨19462496043681987001272149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207599957799274528013569589 19462496043681987001272149)
              ·
                refine ⟨114038062755949142585579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19462496043681987001272149 114038062755949142585579)
                ·
                  rfl

theorem cell23_5996385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 9].length) (baseStart_5996385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996385 prefixEnd_5996385 := by exact prefixLift 5996385
  have htrace : WordTrace (prefixWord ++ tailWord_5996385) baseStart_5996385 baseEnd_5996385 := by
    simpa [prefixWord, tailWord_5996385, baseEnd_5996385] using wordTrace_append hprefix tailTrace_5996385
  have hstable : (prefixWord ++ tailWord_5996385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996385).length < 2 ^ (prefixWord ++ tailWord_5996385).sum := by decide
  have hdescent : baseEnd_5996385 < baseStart_5996385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996392 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5996392 : Nat := 118140960795 + 5996392 * 2 ^ 59
def prefixEnd_5996392 : Nat := 4983230072969 + 3 ^ 40 * 5996392 * 2
def baseEnd_5996392 : Nat := 3079031288775208322423101

theorem tailTrace_5996392 : CollatzResearch.WordTrace tailWord_5996392 prefixEnd_5996392 3079031288775208322423101 := by
  unfold tailWord_5996392
  simp only [CollatzResearch.WordTrace]
  refine ⟨109353191846051680532883715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145804255794735574043844953 109353191846051680532883715)
  ·
    refine ⟨164029787769077520799325573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109353191846051680532883715 164029787769077520799325573)
    ·
      refine ⟨30755585206702035149873545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164029787769077520799325573 30755585206702035149873545)
      ·
        refine ⟨23066688905026526362405159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30755585206702035149873545 23066688905026526362405159)
        ·
          refine ⟨34600033357539789543607739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23066688905026526362405159 34600033357539789543607739)
          ·
            refine ⟨51900050036309684315411609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34600033357539789543607739 51900050036309684315411609)
            ·
              refine ⟨38925037527232263236558707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51900050036309684315411609 38925037527232263236558707)
              ·
                refine ⟨58387556290848394854838061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38925037527232263236558707 58387556290848394854838061)
                ·
                  refine ⟨21895333609068148070564273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58387556290848394854838061 21895333609068148070564273)
                  ·
                    refine ⟨16421500206801111052923205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21895333609068148070564273 16421500206801111052923205)
                    ·
                      refine ⟨3079031288775208322423101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16421500206801111052923205 3079031288775208322423101)
                      ·
                        rfl

theorem cell23_5996392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5996392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996392 prefixEnd_5996392 := by exact prefixLift 5996392
  have htrace : WordTrace (prefixWord ++ tailWord_5996392) baseStart_5996392 baseEnd_5996392 := by
    simpa [prefixWord, tailWord_5996392, baseEnd_5996392] using wordTrace_append hprefix tailTrace_5996392
  have hstable : (prefixWord ++ tailWord_5996392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996392).length < 2 ^ (prefixWord ++ tailWord_5996392).sum := by decide
  have hdescent : baseEnd_5996392 < baseStart_5996392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996415 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 7]
def baseStart_5996415 : Nat := 118140960795 + 5996415 * 2 ^ 59
def prefixEnd_5996415 : Nat := 4983230072969 + 3 ^ 40 * 5996415 * 2
def baseEnd_5996415 : Nat := 1026347699610087244145165

theorem tailTrace_5996415 : CollatzResearch.WordTrace tailWord_5996415 prefixEnd_5996415 1026347699610087244145165 := by
  unfold tailWord_5996415
  simp only [CollatzResearch.WordTrace]
  refine ⟨218707222571020035993854699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145804815047346690662569799 218707222571020035993854699)
  ·
    refine ⟨328060833856530053990782049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218707222571020035993854699 328060833856530053990782049)
    ·
      refine ⟨246045625392397540493086537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328060833856530053990782049 246045625392397540493086537)
      ·
        refine ⟨184534219044298155369814903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246045625392397540493086537 184534219044298155369814903)
        ·
          refine ⟨276801328566447233054722355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184534219044298155369814903 276801328566447233054722355)
          ·
            refine ⟨415201992849670849582083533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276801328566447233054722355 415201992849670849582083533)
            ·
              refine ⟨155700747318626568593281325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415201992849670849582083533 155700747318626568593281325)
              ·
                refine ⟨58387780244484963222480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155700747318626568593281325 58387780244484963222480497)
                ·
                  refine ⟨43790835183363722416860373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58387780244484963222480497 43790835183363722416860373)
                  ·
                    refine ⟨1026347699610087244145165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43790835183363722416860373 1026347699610087244145165)
                    ·
                      rfl

theorem cell23_5996415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_5996415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996415 prefixEnd_5996415 := by exact prefixLift 5996415
  have htrace : WordTrace (prefixWord ++ tailWord_5996415) baseStart_5996415 baseEnd_5996415 := by
    simpa [prefixWord, tailWord_5996415, baseEnd_5996415] using wordTrace_append hprefix tailTrace_5996415
  have hstable : (prefixWord ++ tailWord_5996415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996415).length < 2 ^ (prefixWord ++ tailWord_5996415).sum := by decide
  have hdescent : baseEnd_5996415 < baseStart_5996415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996423 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 2, 4]
def baseStart_5996423 : Nat := 118140960795 + 5996423 * 2 ^ 59
def prefixEnd_5996423 : Nat := 4983230072969 + 3 ^ 40 * 5996423 * 2
def baseEnd_5996423 : Nat := 1026349068891832567045153

theorem tailTrace_5996423 : CollatzResearch.WordTrace tailWord_5996423 prefixEnd_5996423 1026349068891832567045153 := by
  unfold tailWord_5996423
  simp only [CollatzResearch.WordTrace]
  refine ⟨218707514354991053360145923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145805009569994035573430615 218707514354991053360145923)
  ·
    refine ⟨328061271532486580040218885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218707514354991053360145923 328061271532486580040218885)
    ·
      refine ⟨61511488412341233757541041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328061271532486580040218885 61511488412341233757541041)
      ·
        refine ⟨46133616309255925318155781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61511488412341233757541041 46133616309255925318155781)
        ·
          refine ⟨8650053057985485997154209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46133616309255925318155781 8650053057985485997154209)
          ·
            refine ⟨6487539793489114497865657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8650053057985485997154209 6487539793489114497865657)
            ·
              refine ⟨4865654845116835873399243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487539793489114497865657 4865654845116835873399243)
              ·
                refine ⟨7298482267675253810098865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865654845116835873399243 7298482267675253810098865)
                ·
                  refine ⟨5473861700756440357574149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7298482267675253810098865 5473861700756440357574149)
                  ·
                    refine ⟨1026349068891832567045153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473861700756440357574149 1026349068891832567045153)
                    ·
                      rfl

theorem cell23_5996423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_5996423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996423 prefixEnd_5996423 := by exact prefixLift 5996423
  have htrace : WordTrace (prefixWord ++ tailWord_5996423) baseStart_5996423 baseEnd_5996423 := by
    simpa [prefixWord, tailWord_5996423, baseEnd_5996423] using wordTrace_append hprefix tailTrace_5996423
  have hstable : (prefixWord ++ tailWord_5996423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996423).length < 2 ^ (prefixWord ++ tailWord_5996423).sum := by decide
  have hdescent : baseEnd_5996423 < baseStart_5996423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996430 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5996430 : Nat := 118140960795 + 5996430 * 2 ^ 59
def prefixEnd_5996430 : Nat := 4983230072969 + 3 ^ 40 * 5996430 * 2
def baseEnd_5996430 : Nat := 3079050801040079173747927

theorem tailTrace_5996430 : CollatzResearch.WordTrace tailWord_5996430 prefixEnd_5996430 3079050801040079173747927 := by
  unfold tailWord_5996430
  simp only [CollatzResearch.WordTrace]
  refine ⟨27338471208245711694456343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145805179777310462370433829 27338471208245711694456343)
  ·
    refine ⟨41007706812368567541684515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27338471208245711694456343 41007706812368567541684515)
    ·
      refine ⟨61511560218552851312526773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41007706812368567541684515 61511560218552851312526773)
      ·
        refine ⟨5766708770489329810549385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61511560218552851312526773 5766708770489329810549385)
        ·
          refine ⟨4325031577866997357912039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766708770489329810549385 4325031577866997357912039)
          ·
            refine ⟨6487547366800496036868059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325031577866997357912039 6487547366800496036868059)
            ·
              refine ⟨9731321050200744055302089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487547366800496036868059 9731321050200744055302089)
              ·
                refine ⟨7298490787650558041476567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9731321050200744055302089 7298490787650558041476567)
                ·
                  refine ⟨10947736181475837062214851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298490787650558041476567 10947736181475837062214851)
                  ·
                    refine ⟨16421604272213755593322277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10947736181475837062214851 16421604272213755593322277)
                    ·
                      refine ⟨3079050801040079173747927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16421604272213755593322277 3079050801040079173747927)
                      ·
                        rfl

theorem cell23_5996430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5996430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996430 prefixEnd_5996430 := by exact prefixLift 5996430
  have htrace : WordTrace (prefixWord ++ tailWord_5996430) baseStart_5996430 baseEnd_5996430 := by
    simpa [prefixWord, tailWord_5996430, baseEnd_5996430] using wordTrace_append hprefix tailTrace_5996430
  have hstable : (prefixWord ++ tailWord_5996430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996430).length < 2 ^ (prefixWord ++ tailWord_5996430).sum := by decide
  have hdescent : baseEnd_5996430 < baseStart_5996430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996472 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_5996472 : Nat := 118140960795 + 5996472 * 2 ^ 59
def prefixEnd_5996472 : Nat := 4983230072969 + 3 ^ 40 * 5996472 * 2
def baseEnd_5996472 : Nat := 3079072367227568009422733

theorem tailTrace_5996472 : CollatzResearch.WordTrace tailWord_5996472 prefixEnd_5996472 3079072367227568009422733 := by
  unfold tailWord_5996472
  simp only [CollatzResearch.WordTrace]
  refine ⟨109354650765906767364339835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145806201021209023152453113 109354650765906767364339835)
  ·
    refine ⟨164031976148860151046509753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109354650765906767364339835 164031976148860151046509753)
    ·
      refine ⟨123023982111645113284882315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164031976148860151046509753 123023982111645113284882315)
      ·
        refine ⟨184535973167467669927323473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123023982111645113284882315 184535973167467669927323473)
        ·
          refine ⟨138401979875600752445492605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184535973167467669927323473 138401979875600752445492605)
          ·
            refine ⟨51900742453350282167059727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138401979875600752445492605 51900742453350282167059727)
            ·
              refine ⟨77851113680025423250589591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51900742453350282167059727 77851113680025423250589591)
              ·
                refine ⟨116776670520038134875884387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77851113680025423250589591 116776670520038134875884387)
                ·
                  refine ⟨175165005780057202313826581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116776670520038134875884387 175165005780057202313826581)
                  ·
                    refine ⟨8210859645940181358460621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175165005780057202313826581 8210859645940181358460621)
                    ·
                      refine ⟨3079072367227568009422733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8210859645940181358460621 3079072367227568009422733)
                      ·
                        rfl

theorem cell23_5996472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_5996472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996472 prefixEnd_5996472 := by exact prefixLift 5996472
  have htrace : WordTrace (prefixWord ++ tailWord_5996472) baseStart_5996472 baseEnd_5996472 := by
    simpa [prefixWord, tailWord_5996472, baseEnd_5996472] using wordTrace_append hprefix tailTrace_5996472
  have hstable : (prefixWord ++ tailWord_5996472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996472).length < 2 ^ (prefixWord ++ tailWord_5996472).sum := by decide
  have hdescent : baseEnd_5996472 < baseStart_5996472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996492 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 9]
def baseStart_5996492 : Nat := 118140960795 + 5996492 * 2 ^ 59
def prefixEnd_5996492 : Nat := 4983230072969 + 3 ^ 40 * 5996492 * 2
def baseEnd_5996492 : Nat := 342120292982295325685849

theorem tailTrace_5996492 : CollatzResearch.WordTrace tailWord_5996492 prefixEnd_5996492 342120292982295325685849 := by
  unfold tailWord_5996492
  simp only [CollatzResearch.WordTrace]
  refine ⟨109355015495870539072203865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145806687327827385429605153 109355015495870539072203865)
  ·
    refine ⟨82016261621902904304152899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109355015495870539072203865 82016261621902904304152899)
    ·
      refine ⟨123024392432854356456229349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82016261621902904304152899 123024392432854356456229349)
      ·
        refine ⟨23067073581160191835543003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123024392432854356456229349 23067073581160191835543003)
        ·
          refine ⟨34600610371740287753314505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23067073581160191835543003 34600610371740287753314505)
          ·
            refine ⟨25950457778805215814985879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34600610371740287753314505 25950457778805215814985879)
            ·
              refine ⟨38925686668207823722478819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25950457778805215814985879 38925686668207823722478819)
              ·
                refine ⟨58388530002311735583718229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38925686668207823722478819 58388530002311735583718229)
                ·
                  refine ⟨342120292982295325685849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58388530002311735583718229 342120292982295325685849)
                  ·
                    rfl

theorem cell23_5996492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_5996492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996492 prefixEnd_5996492 := by exact prefixLift 5996492
  have htrace : WordTrace (prefixWord ++ tailWord_5996492) baseStart_5996492 baseEnd_5996492 := by
    simpa [prefixWord, tailWord_5996492, baseEnd_5996492] using wordTrace_append hprefix tailTrace_5996492
  have hstable : (prefixWord ++ tailWord_5996492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996492).length < 2 ^ (prefixWord ++ tailWord_5996492).sum := by decide
  have hdescent : baseEnd_5996492 < baseStart_5996492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996526 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_5996526 : Nat := 118140960795 + 5996526 * 2 ^ 59
def prefixEnd_5996526 : Nat := 4983230072969 + 3 ^ 40 * 5996526 * 2
def baseEnd_5996526 : Nat := 342122232798101199794165

theorem tailTrace_5996526 : CollatzResearch.WordTrace tailWord_5996526 prefixEnd_5996526 342122232798101199794165 := by
  unfold tailWord_5996526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27338908884202237743893179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145807514049078601300763621 27338908884202237743893179)
  ·
    refine ⟨41008363326303356615839769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27338908884202237743893179 41008363326303356615839769)
    ·
      refine ⟨30756272494727517461879827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41008363326303356615839769 30756272494727517461879827)
      ·
        refine ⟨46134408742091276192819741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30756272494727517461879827 46134408742091276192819741)
        ·
          refine ⟨17300403278284228572307403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46134408742091276192819741 17300403278284228572307403)
          ·
            refine ⟨25950604917426342858461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17300403278284228572307403 25950604917426342858461105)
            ·
              refine ⟨19462953688069757143845829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25950604917426342858461105 19462953688069757143845829)
              ·
                refine ⟨3649303816513079464471093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19462953688069757143845829 3649303816513079464471093)
                ·
                  refine ⟨342122232798101199794165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3649303816513079464471093 342122232798101199794165)
                  ·
                    rfl

theorem cell23_5996526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_5996526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996526 prefixEnd_5996526 := by exact prefixLift 5996526
  have htrace : WordTrace (prefixWord ++ tailWord_5996526) baseStart_5996526 baseEnd_5996526 := by
    simpa [prefixWord, tailWord_5996526, baseEnd_5996526] using wordTrace_append hprefix tailTrace_5996526
  have hstable : (prefixWord ++ tailWord_5996526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996526).length < 2 ^ (prefixWord ++ tailWord_5996526).sum := by decide
  have hdescent : baseEnd_5996526 < baseStart_5996526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996552 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_5996552 : Nat := 118140960795 + 5996552 * 2 ^ 59
def prefixEnd_5996552 : Nat := 4983230072969 + 3 ^ 40 * 5996552 * 2
def baseEnd_5996552 : Nat := 1026371148559975898807455

theorem tailTrace_5996552 : CollatzResearch.WordTrace tailWord_5996552 prefixEnd_5996552 1026371148559975898807455 := by
  unfold tailWord_5996552
  simp only [CollatzResearch.WordTrace]
  refine ⟨109356109685761854195795955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145808146247682472261061273 109356109685761854195795955)
  ·
    refine ⟨164034164528642781293693933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109356109685761854195795955 164034164528642781293693933)
    ·
      refine ⟨61512811698241042985135225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164034164528642781293693933 61512811698241042985135225)
      ·
        refine ⟨46134608773680782238851419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61512811698241042985135225 46134608773680782238851419)
        ·
          refine ⟨69201913160521173358277129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46134608773680782238851419 69201913160521173358277129)
          ·
            refine ⟨51901434870390880018707847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69201913160521173358277129 51901434870390880018707847)
            ·
              refine ⟨77852152305586320028061771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51901434870390880018707847 77852152305586320028061771)
              ·
                refine ⟨116778228458379480042092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77852152305586320028061771 116778228458379480042092657)
                ·
                  refine ⟨87583671343784610031569493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116778228458379480042092657 87583671343784610031569493)
                  ·
                    refine ⟨1026371148559975898807455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87583671343784610031569493 1026371148559975898807455)
                    ·
                      rfl

theorem cell23_5996552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_5996552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996552 prefixEnd_5996552 := by exact prefixLift 5996552
  have htrace : WordTrace (prefixWord ++ tailWord_5996552) baseStart_5996552 baseEnd_5996552 := by
    simpa [prefixWord, tailWord_5996552, baseEnd_5996552] using wordTrace_append hprefix tailTrace_5996552
  have hstable : (prefixWord ++ tailWord_5996552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996552).length < 2 ^ (prefixWord ++ tailWord_5996552).sum := by decide
  have hdescent : baseEnd_5996552 < baseStart_5996552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996630 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5996630 : Nat := 118140960795 + 5996630 * 2 ^ 59
def prefixEnd_5996630 : Nat := 4983230072969 + 3 ^ 40 * 5996630 * 2
def baseEnd_5996630 : Nat := 3079153497170978391247007

theorem tailTrace_5996630 : CollatzResearch.WordTrace tailWord_5996630 prefixEnd_5996630 3079153497170978391247007 := by
  unfold tailWord_5996630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669691516577570482058209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145810042843494085141954229 13669691516577570482058209)
  ·
    refine ⟨10252268637433177861543657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13669691516577570482058209 10252268637433177861543657)
    ·
      refine ⟨7689201478074883396157743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10252268637433177861543657 7689201478074883396157743)
      ·
        refine ⟨11533802217112325094236615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689201478074883396157743 11533802217112325094236615)
        ·
          refine ⟨17300703325668487641354923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533802217112325094236615 17300703325668487641354923)
          ·
            refine ⟨25951054988502731462032385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17300703325668487641354923 25951054988502731462032385)
            ·
              refine ⟨19463291241377048596524289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25951054988502731462032385 19463291241377048596524289)
              ·
                refine ⟨14597468431032786447393217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19463291241377048596524289 14597468431032786447393217)
                ·
                  refine ⟨10948101323274589835544913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14597468431032786447393217 10948101323274589835544913)
                  ·
                    refine ⟨8211075992455942376658685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10948101323274589835544913 8211075992455942376658685)
                    ·
                      refine ⟨3079153497170978391247007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211075992455942376658685 3079153497170978391247007)
                      ·
                        rfl

theorem cell23_5996630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5996630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996630 prefixEnd_5996630 := by exact prefixLift 5996630
  have htrace : WordTrace (prefixWord ++ tailWord_5996630) baseStart_5996630 baseEnd_5996630 := by
    simpa [prefixWord, tailWord_5996630, baseEnd_5996630] using wordTrace_append hprefix tailTrace_5996630
  have hstable : (prefixWord ++ tailWord_5996630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996630).length < 2 ^ (prefixWord ++ tailWord_5996630).sum := by decide
  have hdescent : baseEnd_5996630 < baseStart_5996630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996637 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5996637 : Nat := 118140960795 + 5996637 * 2 ^ 59
def prefixEnd_5996637 : Nat := 4983230072969 + 3 ^ 40 * 5996637 * 2
def baseEnd_5996637 : Nat := 1026385697178519954619825

theorem tailTrace_5996637 : CollatzResearch.WordTrace tailWord_5996637 prefixEnd_5996637 1026385697178519954619825 := by
  unfold tailWord_5996637
  simp only [CollatzResearch.WordTrace]
  refine ⟨218715319576215767908436165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145810213050810511938957443 218715319576215767908436165)
  ·
    refine ⟨41009122420540456482831781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218715319576215767908436165 41009122420540456482831781)
    ·
      refine ⟨7689210453851335590530959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41009122420540456482831781 7689210453851335590530959)
      ·
        refine ⟨11533815680777003385796439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689210453851335590530959 11533815680777003385796439)
        ·
          refine ⟨17300723521165505078694659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533815680777003385796439 17300723521165505078694659)
          ·
            refine ⟨25951085281748257618041989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17300723521165505078694659 25951085281748257618041989)
            ·
              refine ⟨4865828490327798303382873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25951085281748257618041989 4865828490327798303382873)
              ·
                refine ⟨3649371367745848727537155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865828490327798303382873 3649371367745848727537155)
                ·
                  refine ⟨5474057051618773091305733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649371367745848727537155 5474057051618773091305733)
                  ·
                    refine ⟨1026385697178519954619825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474057051618773091305733 1026385697178519954619825)
                    ·
                      rfl

theorem cell23_5996637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5996637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996637 prefixEnd_5996637 := by exact prefixLift 5996637
  have htrace : WordTrace (prefixWord ++ tailWord_5996637) baseStart_5996637 baseEnd_5996637 := by
    simpa [prefixWord, tailWord_5996637, baseEnd_5996637] using wordTrace_append hprefix tailTrace_5996637
  have hstable : (prefixWord ++ tailWord_5996637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996637).length < 2 ^ (prefixWord ++ tailWord_5996637).sum := by decide
  have hdescent : baseEnd_5996637 < baseStart_5996637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996649 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_5996649 : Nat := 118140960795 + 5996649 * 2 ^ 59
def prefixEnd_5996649 : Nat := 4983230072969 + 3 ^ 40 * 5996649 * 2
def baseEnd_5996649 : Nat := 3079163253303413816909419

theorem tailTrace_5996649 : CollatzResearch.WordTrace tailWord_5996649 prefixEnd_5996649 3079163253303413816909419 := by
  unfold tailWord_5996649
  simp only [CollatzResearch.WordTrace]
  refine ⟨218715757252172293957873001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145810504834781529305248667 218715757252172293957873001)
  ·
    refine ⟨164036817939129220468404751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218715757252172293957873001 164036817939129220468404751)
    ·
      refine ⟨246055226908693830702607127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164036817939129220468404751 246055226908693830702607127)
      ·
        refine ⟨369082840363040746053910691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246055226908693830702607127 369082840363040746053910691)
        ·
          refine ⟨553624260544561119080866037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369082840363040746053910691 553624260544561119080866037)
          ·
            refine ⟨51902274426052604913831191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 553624260544561119080866037 51902274426052604913831191)
            ·
              refine ⟨77853411639078907370746787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51902274426052604913831191 77853411639078907370746787)
              ·
                refine ⟨116780117458618361056120181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77853411639078907370746787 116780117458618361056120181)
                ·
                  refine ⟨10948136011745471349011267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116780117458618361056120181 10948136011745471349011267)
                  ·
                    refine ⟨16422204017618207023516901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10948136011745471349011267 16422204017618207023516901)
                    ·
                      refine ⟨3079163253303413816909419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16422204017618207023516901 3079163253303413816909419)
                      ·
                        rfl

theorem cell23_5996649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_5996649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996649 prefixEnd_5996649 := by exact prefixLift 5996649
  have htrace : WordTrace (prefixWord ++ tailWord_5996649) baseStart_5996649 baseEnd_5996649 := by
    simpa [prefixWord, tailWord_5996649, baseEnd_5996649] using wordTrace_append hprefix tailTrace_5996649
  have hstable : (prefixWord ++ tailWord_5996649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996649).length < 2 ^ (prefixWord ++ tailWord_5996649).sum := by decide
  have hdescent : baseEnd_5996649 < baseStart_5996649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996676 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_5996676 : Nat := 118140960795 + 5996676 * 2 ^ 59
def prefixEnd_5996676 : Nat := 4983230072969 + 3 ^ 40 * 5996676 * 2
def baseEnd_5996676 : Nat := 1026392372427028403757265

theorem tailTrace_5996676 : CollatzResearch.WordTrace tailWord_5996676 prefixEnd_5996676 1026392372427028403757265 := by
  unfold tailWord_5996676
  simp only [CollatzResearch.WordTrace]
  refine ⟨109358371011537238784552941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145811161348716318379403921 109358371011537238784552941)
  ·
    refine ⟨41009389129326464544207353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109358371011537238784552941 41009389129326464544207353)
    ·
      refine ⟨30757041846994848408155515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41009389129326464544207353 30757041846994848408155515)
      ·
        refine ⟨46135562770492272612233273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30757041846994848408155515 46135562770492272612233273)
        ·
          refine ⟨34601672077869204459174955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46135562770492272612233273 34601672077869204459174955)
          ·
            refine ⟨51902508116803806688762433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34601672077869204459174955 51902508116803806688762433)
            ·
              refine ⟨38926881087602855016571825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51902508116803806688762433 38926881087602855016571825)
              ·
                refine ⟨29195160815702141262428869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38926881087602855016571825 29195160815702141262428869)
                ·
                  refine ⟨5474092652944151486705413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29195160815702141262428869 5474092652944151486705413)
                  ·
                    refine ⟨1026392372427028403757265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474092652944151486705413 1026392372427028403757265)
                    ·
                      rfl

theorem cell23_5996676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_5996676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996676 prefixEnd_5996676 := by exact prefixLift 5996676
  have htrace : WordTrace (prefixWord ++ tailWord_5996676) baseStart_5996676 baseEnd_5996676 := by
    simpa [prefixWord, tailWord_5996676, baseEnd_5996676] using wordTrace_append hprefix tailTrace_5996676
  have hstable : (prefixWord ++ tailWord_5996676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996676).length < 2 ^ (prefixWord ++ tailWord_5996676).sum := by decide
  have hdescent : baseEnd_5996676 < baseStart_5996676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996680 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_5996680 : Nat := 118140960795 + 5996680 * 2 ^ 59
def prefixEnd_5996680 : Nat := 4983230072969 + 3 ^ 40 * 5996680 * 2
def baseEnd_5996680 : Nat := 1026393057067901065207259

theorem tailTrace_5996680 : CollatzResearch.WordTrace tailWord_5996680 prefixEnd_5996680 1026393057067901065207259 := by
  unfold tailWord_5996680
  simp only [CollatzResearch.WordTrace]
  refine ⟨109358443957529993126125747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145811258610039990834834329 109358443957529993126125747)
  ·
    refine ⟨164037665936294989689188621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109358443957529993126125747 164037665936294989689188621)
    ·
      refine ⟨61514124726110621133445733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164037665936294989689188621 61514124726110621133445733)
      ·
        refine ⟨11533898386145741462521075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61514124726110621133445733 11533898386145741462521075)
        ·
          refine ⟨17300847579218612193781613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533898386145741462521075 17300847579218612193781613)
          ·
            refine ⟨6487817842206979572668105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17300847579218612193781613 6487817842206979572668105)
            ·
              refine ⟨4865863381655234679501079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487817842206979572668105 4865863381655234679501079)
              ·
                refine ⟨7298795072482852019251619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865863381655234679501079 7298795072482852019251619)
                ·
                  refine ⟨10948192608724278028877429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298795072482852019251619 10948192608724278028877429)
                  ·
                    refine ⟨1026393057067901065207259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10948192608724278028877429 1026393057067901065207259)
                    ·
                      rfl

theorem cell23_5996680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_5996680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996680 prefixEnd_5996680 := by exact prefixLift 5996680
  have htrace : WordTrace (prefixWord ++ tailWord_5996680) baseStart_5996680 baseEnd_5996680 := by
    simpa [prefixWord, tailWord_5996680, baseEnd_5996680] using wordTrace_append hprefix tailTrace_5996680
  have hstable : (prefixWord ++ tailWord_5996680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996680).length < 2 ^ (prefixWord ++ tailWord_5996680).sum := by decide
  have hdescent : baseEnd_5996680 < baseStart_5996680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996700 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5996700 : Nat := 118140960795 + 5996700 * 2 ^ 59
def prefixEnd_5996700 : Nat := 4983230072969 + 3 ^ 40 * 5996700 * 2
def baseEnd_5996700 : Nat := 3079189440816793117371685

theorem tailTrace_5996700 : CollatzResearch.WordTrace tailWord_5996700 prefixEnd_5996700 3079189440816793117371685 := by
  unfold tailWord_5996700
  simp only [CollatzResearch.WordTrace]
  refine ⟨109358808687493764833989777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145811744916658353111986369 109358808687493764833989777)
  ·
    refine ⟨82019106515620323625492333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109358808687493764833989777 82019106515620323625492333)
    ·
      refine ⟨30757164943357621359559625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82019106515620323625492333 30757164943357621359559625)
      ·
        refine ⟨23067873707518216019669719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30757164943357621359559625 23067873707518216019669719)
        ·
          refine ⟨34601810561277324029504579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23067873707518216019669719 34601810561277324029504579)
          ·
            refine ⟨51902715841915986044256869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34601810561277324029504579 51902715841915986044256869)
            ·
              refine ⟨9731759220359247383298163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51902715841915986044256869 9731759220359247383298163)
              ·
                refine ⟨14597638830538871074947245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9731759220359247383298163 14597638830538871074947245)
                ·
                  refine ⟨5474114561452076653105217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14597638830538871074947245 5474114561452076653105217)
                  ·
                    refine ⟨4105585921089057489828913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474114561452076653105217 4105585921089057489828913)
                    ·
                      refine ⟨3079189440816793117371685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105585921089057489828913 3079189440816793117371685)
                      ·
                        rfl

theorem cell23_5996700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5996700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996700 prefixEnd_5996700 := by exact prefixLift 5996700
  have htrace : WordTrace (prefixWord ++ tailWord_5996700) baseStart_5996700 baseEnd_5996700 := by
    simpa [prefixWord, tailWord_5996700, baseEnd_5996700] using wordTrace_append hprefix tailTrace_5996700
  have hstable : (prefixWord ++ tailWord_5996700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996700).length < 2 ^ (prefixWord ++ tailWord_5996700).sum := by decide
  have hdescent : baseEnd_5996700 < baseStart_5996700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996729 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5996729 : Nat := 118140960795 + 5996729 * 2 ^ 59
def prefixEnd_5996729 : Nat := 4983230072969 + 3 ^ 40 * 5996729 * 2
def baseEnd_5996729 : Nat := 3079204331755773503909051

theorem tailTrace_5996729 : CollatzResearch.WordTrace tailWord_5996729 prefixEnd_5996729 3079204331755773503909051 := by
  unfold tailWord_5996729
  simp only [CollatzResearch.WordTrace]
  refine ⟨218718675091882467620785241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145812450061254978413856827 218718675091882467620785241)
  ·
    refine ⟨164039006318911850715588931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218718675091882467620785241 164039006318911850715588931)
    ·
      refine ⟨246058509478367776073383397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164039006318911850715588931 246058509478367776073383397)
      ·
        refine ⟨46135970527193958013759387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246058509478367776073383397 46135970527193958013759387)
        ·
          refine ⟨69203955790790937020639081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46135970527193958013759387 69203955790790937020639081)
          ·
            refine ⟨51902966843093202765479311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69203955790790937020639081 51902966843093202765479311)
            ·
              refine ⟨77854450264639804148218967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51902966843093202765479311 77854450264639804148218967)
              ·
                refine ⟨116781675396959706222328451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77854450264639804148218967 116781675396959706222328451)
                ·
                  refine ⟨175172513095439559333492677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116781675396959706222328451 175172513095439559333492677)
                  ·
                    refine ⟨32844846205394917375029877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175172513095439559333492677 32844846205394917375029877)
                    ·
                      refine ⟨3079204331755773503909051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32844846205394917375029877 3079204331755773503909051)
                      ·
                        rfl

theorem cell23_5996729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5996729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996729 prefixEnd_5996729 := by exact prefixLift 5996729
  have htrace : WordTrace (prefixWord ++ tailWord_5996729) baseStart_5996729 baseEnd_5996729 := by
    simpa [prefixWord, tailWord_5996729, baseEnd_5996729] using wordTrace_append hprefix tailTrace_5996729
  have hstable : (prefixWord ++ tailWord_5996729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996729).length < 2 ^ (prefixWord ++ tailWord_5996729).sum := by decide
  have hdescent : baseEnd_5996729 < baseStart_5996729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996759 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_5996759 : Nat := 118140960795 + 5996759 * 2 ^ 59
def prefixEnd_5996759 : Nat := 4983230072969 + 3 ^ 40 * 5996759 * 2
def baseEnd_5996759 : Nat := 3079219736175408386533913

theorem tailTrace_5996759 : CollatzResearch.WordTrace tailWord_5996759 prefixEnd_5996759 3079219736175408386533913 := by
  unfold tailWord_5996759
  simp only [CollatzResearch.WordTrace]
  refine ⟨218719769281773782744377331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145813179521182521829584887 218719769281773782744377331)
  ·
    refine ⟨328079653922660674116565997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218719769281773782744377331 328079653922660674116565997)
    ·
      refine ⟨123029870220997752793712249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328079653922660674116565997 123029870220997752793712249)
      ·
        refine ⟨92272402665748314595284187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123029870220997752793712249 92272402665748314595284187)
        ·
          refine ⟨138408603998622471892926281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92272402665748314595284187 138408603998622471892926281)
          ·
            refine ⟨103806452998966853919694711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138408603998622471892926281 103806452998966853919694711)
            ·
              refine ⟨155709679498450280879542067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103806452998966853919694711 155709679498450280879542067)
              ·
                refine ⟨233564519247675421319313101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155709679498450280879542067 233564519247675421319313101)
                ·
                  refine ⟨87586694717878282994742413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233564519247675421319313101 87586694717878282994742413)
                  ·
                    refine ⟨32845010519204356123028405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87586694717878282994742413 32845010519204356123028405)
                    ·
                      refine ⟨3079219736175408386533913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32845010519204356123028405 3079219736175408386533913)
                      ·
                        rfl

theorem cell23_5996759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_5996759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996759 prefixEnd_5996759 := by exact prefixLift 5996759
  have htrace : WordTrace (prefixWord ++ tailWord_5996759) baseStart_5996759 baseEnd_5996759 := by
    simpa [prefixWord, tailWord_5996759, baseEnd_5996759] using wordTrace_append hprefix tailTrace_5996759
  have hstable : (prefixWord ++ tailWord_5996759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996759).length < 2 ^ (prefixWord ++ tailWord_5996759).sum := by decide
  have hdescent : baseEnd_5996759 < baseStart_5996759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996776 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5996776 : Nat := 118140960795 + 5996776 * 2 ^ 59
def prefixEnd_5996776 : Nat := 4983230072969 + 3 ^ 40 * 5996776 * 2
def baseEnd_5996776 : Nat := 3079228465346534820021335

theorem tailTrace_5996776 : CollatzResearch.WordTrace tailWord_5996776 prefixEnd_5996776 3079228465346534820021335 := by
  unfold tailWord_5996776
  simp only [CollatzResearch.WordTrace]
  refine ⟨109360194661356097323873091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145813592881808129765164121 109360194661356097323873091)
  ·
    refine ⟨164040291992034145985809637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109360194661356097323873091 164040291992034145985809637)
    ·
      refine ⟨30757554748506402372339307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164040291992034145985809637 30757554748506402372339307)
      ·
        refine ⟨46136332122759603558508961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30757554748506402372339307 46136332122759603558508961)
        ·
          refine ⟨34602249092069702668881721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46136332122759603558508961 34602249092069702668881721)
          ·
            refine ⟨25951686819052277001661291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34602249092069702668881721 25951686819052277001661291)
            ·
              refine ⟨38927530228578415502491937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25951686819052277001661291 38927530228578415502491937)
              ·
                refine ⟨29195647671433811626868953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38927530228578415502491937 29195647671433811626868953)
                ·
                  refine ⟨21896735753575358720151715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29195647671433811626868953 21896735753575358720151715)
                  ·
                    refine ⟨32845103630363038080227573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21896735753575358720151715 32845103630363038080227573)
                    ·
                      refine ⟨3079228465346534820021335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32845103630363038080227573 3079228465346534820021335)
                      ·
                        rfl

theorem cell23_5996776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5996776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996776 prefixEnd_5996776 := by exact prefixLift 5996776
  have htrace : WordTrace (prefixWord ++ tailWord_5996776) baseStart_5996776 baseEnd_5996776 := by
    simpa [prefixWord, tailWord_5996776, baseEnd_5996776] using wordTrace_append hprefix tailTrace_5996776
  have hstable : (prefixWord ++ tailWord_5996776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996776).length < 2 ^ (prefixWord ++ tailWord_5996776).sum := by decide
  have hdescent : baseEnd_5996776 < baseStart_5996776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996779 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 9]
def baseStart_5996779 : Nat := 118140960795 + 5996779 * 2 ^ 59
def prefixEnd_5996779 : Nat := 4983230072969 + 3 ^ 40 * 5996779 * 2
def baseEnd_5996779 : Nat := 342136667309833145364869

theorem tailTrace_5996779 : CollatzResearch.WordTrace tailWord_5996779 prefixEnd_5996779 342136667309833145364869 := by
  unfold tailWord_5996779
  simp only [CollatzResearch.WordTrace]
  refine ⟨218720498741701326160105391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145813665827800884106736927 218720498741701326160105391)
  ·
    refine ⟨328080748112551989240158087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218720498741701326160105391 328080748112551989240158087)
    ·
      refine ⟨492121122168827983860237131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328080748112551989240158087 492121122168827983860237131)
      ·
        refine ⟨738181683253241975790355697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492121122168827983860237131 738181683253241975790355697)
        ·
          refine ⟨553636262439931481842766773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738181683253241975790355697 553636262439931481842766773)
          ·
            refine ⟨51903399603743576422759385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 553636262439931481842766773 51903399603743576422759385)
            ·
              refine ⟨38927549702807682317069539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51903399603743576422759385 38927549702807682317069539)
              ·
                refine ⟨58391324554211523475604309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38927549702807682317069539 58391324554211523475604309)
                ·
                  refine ⟨342136667309833145364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58391324554211523475604309 342136667309833145364869)
                  ·
                    rfl

theorem cell23_5996779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_5996779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996779 prefixEnd_5996779 := by exact prefixLift 5996779
  have htrace : WordTrace (prefixWord ++ tailWord_5996779) baseStart_5996779 baseEnd_5996779 := by
    simpa [prefixWord, tailWord_5996779, baseEnd_5996779] using wordTrace_append hprefix tailTrace_5996779
  have hstable : (prefixWord ++ tailWord_5996779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996779).length < 2 ^ (prefixWord ++ tailWord_5996779).sum := by decide
  have hdescent : baseEnd_5996779 < baseStart_5996779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996790 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5996790 : Nat := 118140960795 + 5996790 * 2 ^ 59
def prefixEnd_5996790 : Nat := 4983230072969 + 3 ^ 40 * 5996790 * 2
def baseEnd_5996790 : Nat := 3079235654075697765246271

theorem tailTrace_5996790 : CollatzResearch.WordTrace tailWord_5996790 prefixEnd_5996790 3079235654075697765246271 := by
  unfold tailWord_5996790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13670056246541342189922239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145813933296440983359170549 13670056246541342189922239)
  ·
    refine ⟨20505084369812013284883359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13670056246541342189922239 20505084369812013284883359)
    ·
      refine ⟨30757626554718019927325039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20505084369812013284883359 30757626554718019927325039)
      ·
        refine ⟨46136439832077029890987559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30757626554718019927325039 46136439832077029890987559)
        ·
          refine ⟨69204659748115544836481339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46136439832077029890987559 69204659748115544836481339)
          ·
            refine ⟨103806989622173317254722009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69204659748115544836481339 103806989622173317254722009)
            ·
              refine ⟨77855242216629987941041507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103806989622173317254722009 77855242216629987941041507)
              ·
                refine ⟨116782863324944981911562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77855242216629987941041507 116782863324944981911562261)
                ·
                  refine ⟨5474196718356796027104481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116782863324944981911562261 5474196718356796027104481)
                  ·
                    refine ⟨4105647538767597020328361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474196718356796027104481 4105647538767597020328361)
                    ·
                      refine ⟨3079235654075697765246271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105647538767597020328361 3079235654075697765246271)
                      ·
                        rfl

theorem cell23_5996790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5996790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996790 prefixEnd_5996790 := by exact prefixLift 5996790
  have htrace : WordTrace (prefixWord ++ tailWord_5996790) baseStart_5996790 baseEnd_5996790 := by
    simpa [prefixWord, tailWord_5996790, baseEnd_5996790] using wordTrace_append hprefix tailTrace_5996790
  have hstable : (prefixWord ++ tailWord_5996790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996790).length < 2 ^ (prefixWord ++ tailWord_5996790).sum := by decide
  have hdescent : baseEnd_5996790 < baseStart_5996790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996823 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5996823 : Nat := 118140960795 + 5996823 * 2 ^ 59
def prefixEnd_5996823 : Nat := 4983230072969 + 3 ^ 40 * 5996823 * 2
def baseEnd_5996823 : Nat := 3079252598937296136133619

theorem tailTrace_5996823 : CollatzResearch.WordTrace tailWord_5996823 prefixEnd_5996823 3079252598937296136133619 := by
  unfold tailWord_5996823
  simp only [CollatzResearch.WordTrace]
  refine ⟨218722103553541921674707123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145814735702361281116471415 218722103553541921674707123)
  ·
    refine ⟨328083155330312882512060685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218722103553541921674707123 328083155330312882512060685)
    ·
      refine ⟨123031183248867330942022757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328083155330312882512060685 123031183248867330942022757)
      ·
        refine ⟨23068346859162624551629267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123031183248867330942022757 23068346859162624551629267)
        ·
          refine ⟨34602520288743936827443901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23068346859162624551629267 34602520288743936827443901)
          ·
            refine ⟨12975945108278976310291463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34602520288743936827443901 12975945108278976310291463)
            ·
              refine ⟨19463917662418464465437195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12975945108278976310291463 19463917662418464465437195)
              ·
                refine ⟨29195876493627696698155793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19463917662418464465437195 29195876493627696698155793)
                ·
                  refine ⟨21896907370220772523616845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29195876493627696698155793 21896907370220772523616845)
                  ·
                    refine ⟨8211340263832789696356317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21896907370220772523616845 8211340263832789696356317)
                    ·
                      refine ⟨3079252598937296136133619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211340263832789696356317 3079252598937296136133619)
                      ·
                        rfl

theorem cell23_5996823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5996823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996823 prefixEnd_5996823 := by exact prefixLift 5996823
  have htrace : WordTrace (prefixWord ++ tailWord_5996823) baseStart_5996823 baseEnd_5996823 := by
    simpa [prefixWord, tailWord_5996823, baseEnd_5996823] using wordTrace_append hprefix tailTrace_5996823
  have hstable : (prefixWord ++ tailWord_5996823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996823).length < 2 ^ (prefixWord ++ tailWord_5996823).sum := by decide
  have hdescent : baseEnd_5996823 < baseStart_5996823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996830 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5996830 : Nat := 118140960795 + 5996830 * 2 ^ 59
def prefixEnd_5996830 : Nat := 4983230072969 + 3 ^ 40 * 5996830 * 2
def baseEnd_5996830 : Nat := 342139577033541956527343

theorem tailTrace_5996830 : CollatzResearch.WordTrace tailWord_5996830 prefixEnd_5996830 342139577033541956527343 := by
  unfold tailWord_5996830
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340294858064570233776493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145814905909677707913474629 27340294858064570233776493)
  ·
    refine ⟨10252610571774213837666185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27340294858064570233776493 10252610571774213837666185)
    ·
      refine ⟨7689457928830660378249639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10252610571774213837666185 7689457928830660378249639)
      ·
        refine ⟨11534186893245990567374459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689457928830660378249639 11534186893245990567374459)
        ·
          refine ⟨17301280339868985851061689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534186893245990567374459 17301280339868985851061689)
          ·
            refine ⟨12975960254901739388296267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17301280339868985851061689 12975960254901739388296267)
            ·
              refine ⟨19463940382352609082444401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12975960254901739388296267 19463940382352609082444401)
              ·
                refine ⟨14597955286764456811833301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19463940382352609082444401 14597955286764456811833301)
                ·
                  refine ⟨342139577033541956527343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14597955286764456811833301 342139577033541956527343)
                  ·
                    rfl

theorem cell23_5996830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5996830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996830 prefixEnd_5996830 := by exact prefixLift 5996830
  have htrace : WordTrace (prefixWord ++ tailWord_5996830) baseStart_5996830 baseEnd_5996830 := by
    simpa [prefixWord, tailWord_5996830, baseEnd_5996830] using wordTrace_append hprefix tailTrace_5996830
  have hstable : (prefixWord ++ tailWord_5996830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996830).length < 2 ^ (prefixWord ++ tailWord_5996830).sum := by decide
  have hdescent : baseEnd_5996830 < baseStart_5996830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996863 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 4, 2]
def baseStart_5996863 : Nat := 118140960795 + 5996863 * 2 ^ 59
def prefixEnd_5996863 : Nat := 4983230072969 + 3 ^ 40 * 5996863 * 2
def baseEnd_5996863 : Nat := 3079273138163475979633435

theorem tailTrace_5996863 : CollatzResearch.WordTrace tailWord_5996863 prefixEnd_5996863 3079273138163475979633435 := by
  unfold tailWord_5996863
  simp only [CollatzResearch.WordTrace]
  refine ⟨218723562473397008506163243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145815708315598005670775495 218723562473397008506163243)
  ·
    refine ⟨328085343710095512759244865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218723562473397008506163243 328085343710095512759244865)
    ·
      refine ⟨246064007782571634569433649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328085343710095512759244865 246064007782571634569433649)
      ·
        refine ⟨184548005836928725927075237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246064007782571634569433649 184548005836928725927075237)
        ·
          refine ⟨34602751094424136111326607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184548005836928725927075237 34602751094424136111326607)
          ·
            refine ⟨51904126641636204166989911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34602751094424136111326607 51904126641636204166989911)
            ·
              refine ⟨77856189962454306250484867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51904126641636204166989911 77856189962454306250484867)
              ·
                refine ⟨116784284943681459375727301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77856189962454306250484867 116784284943681459375727301)
                ·
                  refine ⟨21897053426940273632948869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116784284943681459375727301 21897053426940273632948869)
                  ·
                    refine ⟨4105697517551301306177913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21897053426940273632948869 4105697517551301306177913)
                    ·
                      refine ⟨3079273138163475979633435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105697517551301306177913 3079273138163475979633435)
                      ·
                        rfl

theorem cell23_5996863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_5996863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996863 prefixEnd_5996863 := by exact prefixLift 5996863
  have htrace : WordTrace (prefixWord ++ tailWord_5996863) baseStart_5996863 baseEnd_5996863 := by
    simpa [prefixWord, tailWord_5996863, baseEnd_5996863] using wordTrace_append hprefix tailTrace_5996863
  have hstable : (prefixWord ++ tailWord_5996863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996863).length < 2 ^ (prefixWord ++ tailWord_5996863).sum := by decide
  have hdescent : baseEnd_5996863 < baseStart_5996863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996876 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5996876 : Nat := 118140960795 + 5996876 * 2 ^ 59
def prefixEnd_5996876 : Nat := 4983230072969 + 3 ^ 40 * 5996876 * 2
def baseEnd_5996876 : Nat := 3079279813411984428770875

theorem tailTrace_5996876 : CollatzResearch.WordTrace tailWord_5996876 prefixEnd_5996876 3079279813411984428770875 := by
  unfold tailWord_5996876
  simp only [CollatzResearch.WordTrace]
  refine ⟨109362018311174955863193241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145816024414899941150924321 109362018311174955863193241)
  ·
    refine ⟨82021513733381216897394931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109362018311174955863193241 82021513733381216897394931)
    ·
      refine ⟨123032270600071825346092397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82021513733381216897394931 123032270600071825346092397)
      ·
        refine ⟨46137101475026934504784649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123032270600071825346092397 46137101475026934504784649)
        ·
          refine ⟨34602826106270200878588487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46137101475026934504784649 34602826106270200878588487)
          ·
            refine ⟨51904239159405301317882731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34602826106270200878588487 51904239159405301317882731)
            ·
              refine ⟨77856358739107951976824097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51904239159405301317882731 77856358739107951976824097)
              ·
                refine ⟨58392269054330963982618073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77856358739107951976824097 58392269054330963982618073)
                ·
                  refine ⟨43794201790748222986963555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58392269054330963982618073 43794201790748222986963555)
                  ·
                    refine ⟨65691302686122334480445333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43794201790748222986963555 65691302686122334480445333)
                    ·
                      refine ⟨3079279813411984428770875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65691302686122334480445333 3079279813411984428770875)
                      ·
                        rfl

theorem cell23_5996876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5996876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996876 prefixEnd_5996876 := by exact prefixLift 5996876
  have htrace : WordTrace (prefixWord ++ tailWord_5996876) baseStart_5996876 baseEnd_5996876 := by
    simpa [prefixWord, tailWord_5996876, baseEnd_5996876] using wordTrace_append hprefix tailTrace_5996876
  have hstable : (prefixWord ++ tailWord_5996876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996876).length < 2 ^ (prefixWord ++ tailWord_5996876).sum := by decide
  have hdescent : baseEnd_5996876 < baseStart_5996876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996953 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_5996953 : Nat := 118140960795 + 5996953 * 2 ^ 59
def prefixEnd_5996953 : Nat := 4983230072969 + 3 ^ 40 * 5996953 * 2
def baseEnd_5996953 : Nat := 3079319351422380627508021

theorem tailTrace_5996953 : CollatzResearch.WordTrace tailWord_5996953 prefixEnd_5996953 3079319351422380627508021 := by
  unfold tailWord_5996953
  simp only [CollatzResearch.WordTrace]
  refine ⟨218726845043070953876939513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145817896695380635917959675 218726845043070953876939513)
  ·
    refine ⟨164045133782303215407704635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218726845043070953876939513 164045133782303215407704635)
    ·
      refine ⟨246067700673454823111556953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164045133782303215407704635 246067700673454823111556953)
      ·
        refine ⟨184550775505091117333667715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246067700673454823111556953 184550775505091117333667715)
        ·
          refine ⟨276826163257636676000501573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184550775505091117333667715 276826163257636676000501573)
          ·
            refine ⟨51904905610806876750094045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276826163257636676000501573 51904905610806876750094045)
            ·
              refine ⟨19464339604052578781285267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51904905610806876750094045 19464339604052578781285267)
              ·
                refine ⟨29196509406078868171927901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19464339604052578781285267 29196509406078868171927901)
                ·
                  refine ⟨10948691027279575564472963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29196509406078868171927901 10948691027279575564472963)
                  ·
                    refine ⟨16423036540919363346709445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10948691027279575564472963 16423036540919363346709445)
                    ·
                      refine ⟨3079319351422380627508021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16423036540919363346709445 3079319351422380627508021)
                      ·
                        rfl

theorem cell23_5996953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_5996953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996953 prefixEnd_5996953 := by exact prefixLift 5996953
  have htrace : WordTrace (prefixWord ++ tailWord_5996953) baseStart_5996953 baseEnd_5996953 := by
    simpa [prefixWord, tailWord_5996953, baseEnd_5996953] using wordTrace_append hprefix tailTrace_5996953
  have hstable : (prefixWord ++ tailWord_5996953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996953).length < 2 ^ (prefixWord ++ tailWord_5996953).sum := by decide
  have hdescent : baseEnd_5996953 < baseStart_5996953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996963 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 6]
def baseStart_5996963 : Nat := 118140960795 + 5996963 * 2 ^ 59
def prefixEnd_5996963 : Nat := 4983230072969 + 3 ^ 40 * 5996963 * 2
def baseEnd_5996963 : Nat := 1026441495409641862794325

theorem tailTrace_5996963 : CollatzResearch.WordTrace tailWord_5996963 prefixEnd_5996963 1026441495409641862794325 := by
  unfold tailWord_5996963
  simp only [CollatzResearch.WordTrace]
  refine ⟨218727209773034725584803543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145818139848689817056535695 218727209773034725584803543)
  ·
    refine ⟨328090814659552088377205315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218727209773034725584803543 328090814659552088377205315)
    ·
      refine ⟨492136221989328132565807973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328090814659552088377205315 492136221989328132565807973)
      ·
        refine ⟨92275541622999024856088995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492136221989328132565807973 92275541622999024856088995)
        ·
          refine ⟨138413312434498537284133493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92275541622999024856088995 138413312434498537284133493)
          ·
            refine ⟨12976248040734237870387515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138413312434498537284133493 12976248040734237870387515)
            ·
              refine ⟨19464372061101356805581273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976248040734237870387515 19464372061101356805581273)
              ·
                refine ⟨14598279045826017604185955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464372061101356805581273 14598279045826017604185955)
                ·
                  refine ⟨21897418568739026406278933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598279045826017604185955 21897418568739026406278933)
                  ·
                    refine ⟨1026441495409641862794325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21897418568739026406278933 1026441495409641862794325)
                    ·
                      rfl

theorem cell23_5996963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_5996963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996963 prefixEnd_5996963 := by exact prefixLift 5996963
  have htrace : WordTrace (prefixWord ++ tailWord_5996963) baseStart_5996963 baseEnd_5996963 := by
    simpa [prefixWord, tailWord_5996963, baseEnd_5996963] using wordTrace_append hprefix tailTrace_5996963
  have hstable : (prefixWord ++ tailWord_5996963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996963).length < 2 ^ (prefixWord ++ tailWord_5996963).sum := by decide
  have hdescent : baseEnd_5996963 < baseStart_5996963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996967 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5996967 : Nat := 118140960795 + 5996967 * 2 ^ 59
def prefixEnd_5996967 : Nat := 4983230072969 + 3 ^ 40 * 5996967 * 2
def baseEnd_5996967 : Nat := 1026442180050514524244319

theorem tailTrace_5996967 : CollatzResearch.WordTrace tailWord_5996967 prefixEnd_5996967 1026442180050514524244319 := by
  unfold tailWord_5996967
  simp only [CollatzResearch.WordTrace]
  refine ⟨218727355665020234267949155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145818237110013489511966103 218727355665020234267949155)
  ·
    refine ⟨328091033497530351401923733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218727355665020234267949155 328091033497530351401923733)
    ·
      refine ⟨15379267195196735221965175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 328091033497530351401923733 15379267195196735221965175)
      ·
        refine ⟨23068900792795102832947763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379267195196735221965175 23068900792795102832947763)
        ·
          refine ⟨34603351189192654249421645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23068900792795102832947763 34603351189192654249421645)
          ·
            refine ⟨12976256695947245343533117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34603351189192654249421645 12976256695947245343533117)
            ·
              refine ⟨4866096260980217003824919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12976256695947245343533117 4866096260980217003824919)
              ·
                refine ⟨7299144391470325505737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866096260980217003824919 7299144391470325505737379)
                ·
                  refine ⟨10948716587205488258606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7299144391470325505737379 10948716587205488258606069)
                  ·
                    refine ⟨1026442180050514524244319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10948716587205488258606069 1026442180050514524244319)
                    ·
                      rfl

theorem cell23_5996967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5996967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996967 prefixEnd_5996967 := by exact prefixLift 5996967
  have htrace : WordTrace (prefixWord ++ tailWord_5996967) baseStart_5996967 baseEnd_5996967 := by
    simpa [prefixWord, tailWord_5996967, baseEnd_5996967] using wordTrace_append hprefix tailTrace_5996967
  have hstable : (prefixWord ++ tailWord_5996967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996967).length < 2 ^ (prefixWord ++ tailWord_5996967).sum := by decide
  have hdescent : baseEnd_5996967 < baseStart_5996967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5996990 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_5996990 : Nat := 118140960795 + 5996990 * 2 ^ 59
def prefixEnd_5996990 : Nat := 4983230072969 + 3 ^ 40 * 5996990 * 2
def baseEnd_5996990 : Nat := 3079338350206596982745351

theorem tailTrace_5996990 : CollatzResearch.WordTrace tailWord_5996990 prefixEnd_5996990 3079338350206596982745351 := by
  unfold tailWord_5996990
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341024317992113649504553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145818796362624606130690949 27341024317992113649504553)
  ·
    refine ⟨20505768238494085237128415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27341024317992113649504553 20505768238494085237128415)
    ·
      refine ⟨30758652357741127855692623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20505768238494085237128415 30758652357741127855692623)
      ·
        refine ⟨46137978536611691783538935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30758652357741127855692623 46137978536611691783538935)
        ·
          refine ⟨69206967804917537675308403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46137978536611691783538935 69206967804917537675308403)
          ·
            refine ⟨103810451707376306512962605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69206967804917537675308403 103810451707376306512962605)
            ·
              refine ⟨38928919390266114942360977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103810451707376306512962605 38928919390266114942360977)
              ·
                refine ⟨29196689542699586206770733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38928919390266114942360977 29196689542699586206770733)
                ·
                  refine ⟨10948758578512344827539025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29196689542699586206770733 10948758578512344827539025)
                  ·
                    refine ⟨8211568933884258620654269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10948758578512344827539025 8211568933884258620654269)
                    ·
                      refine ⟨3079338350206596982745351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211568933884258620654269 3079338350206596982745351)
                      ·
                        rfl

theorem cell23_5996990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_5996990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5996990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5996990 prefixEnd_5996990 := by exact prefixLift 5996990
  have htrace : WordTrace (prefixWord ++ tailWord_5996990) baseStart_5996990 baseEnd_5996990 := by
    simpa [prefixWord, tailWord_5996990, baseEnd_5996990] using wordTrace_append hprefix tailTrace_5996990
  have hstable : (prefixWord ++ tailWord_5996990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5996990).length < 2 ^ (prefixWord ++ tailWord_5996990).sum := by decide
  have hdescent : baseEnd_5996990 < baseStart_5996990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5996990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997000 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_5997000 : Nat := 118140960795 + 5997000 * 2 ^ 59
def prefixEnd_5997000 : Nat := 4983230072969 + 3 ^ 40 * 5997000 * 2
def baseEnd_5997000 : Nat := 3079343485013141943620305

theorem tailTrace_5997000 : CollatzResearch.WordTrace tailWord_5997000 prefixEnd_5997000 3079343485013141943620305 := by
  unfold tailWord_5997000
  simp only [CollatzResearch.WordTrace]
  refine ⟨109364279636950340451950227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145819039515933787269266969 109364279636950340451950227)
  ·
    refine ⟨164046419455425510677925341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109364279636950340451950227 164046419455425510677925341)
    ·
      refine ⟨61517407295784566504222003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164046419455425510677925341 61517407295784566504222003)
      ·
        refine ⟨92276110943676849756333005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61517407295784566504222003 92276110943676849756333005)
        ·
          refine ⟨34603541603878818658624877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92276110943676849756333005 34603541603878818658624877)
          ·
            refine ⟨12976328101454556996984329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34603541603878818658624877 12976328101454556996984329)
            ·
              refine ⟨9732246076090917747738247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12976328101454556996984329 9732246076090917747738247)
              ·
                refine ⟨14598369114136376621607371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732246076090917747738247 14598369114136376621607371)
                ·
                  refine ⟨21897553671204564932411057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598369114136376621607371 21897553671204564932411057)
                  ·
                    refine ⟨16423165253403423699308293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21897553671204564932411057 16423165253403423699308293)
                    ·
                      refine ⟨3079343485013141943620305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16423165253403423699308293 3079343485013141943620305)
                      ·
                        rfl

theorem cell23_5997000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_5997000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997000 prefixEnd_5997000 := by exact prefixLift 5997000
  have htrace : WordTrace (prefixWord ++ tailWord_5997000) baseStart_5997000 baseEnd_5997000 := by
    simpa [prefixWord, tailWord_5997000, baseEnd_5997000] using wordTrace_append hprefix tailTrace_5997000
  have hstable : (prefixWord ++ tailWord_5997000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997000).length < 2 ^ (prefixWord ++ tailWord_5997000).sum := by decide
  have hdescent : baseEnd_5997000 < baseStart_5997000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997004 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5997004 : Nat := 118140960795 + 5997004 * 2 ^ 59
def prefixEnd_5997004 : Nat := 4983230072969 + 3 ^ 40 * 5997004 * 2
def baseEnd_5997004 : Nat := 3079345538935759927970287

theorem tailTrace_5997004 : CollatzResearch.WordTrace tailWord_5997004 prefixEnd_5997004 3079345538935759927970287 := by
  unfold tailWord_5997004
  simp only [CollatzResearch.WordTrace]
  refine ⟨109364352582943094793523033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145819136777257459724697377 109364352582943094793523033)
  ·
    refine ⟨82023264437207321095142275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109364352582943094793523033 82023264437207321095142275)
    ·
      refine ⟨123034896655810981642713413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82023264437207321095142275 123034896655810981642713413)
      ·
        refine ⟨23069043122964559058008765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123034896655810981642713413 23069043122964559058008765)
        ·
          refine ⟨8650891171111709646753287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23069043122964559058008765 8650891171111709646753287)
          ·
            refine ⟨12976336756667564470129931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650891171111709646753287 12976336756667564470129931)
            ·
              refine ⟨19464505135001346705194897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976336756667564470129931 19464505135001346705194897)
              ·
                refine ⟨14598378851251010028896173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464505135001346705194897 14598378851251010028896173)
                ·
                  refine ⟨5474392069219128760836065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14598378851251010028896173 5474392069219128760836065)
                  ·
                    refine ⟨4105794051914346570627049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474392069219128760836065 4105794051914346570627049)
                    ·
                      refine ⟨3079345538935759927970287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105794051914346570627049 3079345538935759927970287)
                      ·
                        rfl

theorem cell23_5997004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5997004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997004 prefixEnd_5997004 := by exact prefixLift 5997004
  have htrace : WordTrace (prefixWord ++ tailWord_5997004) baseStart_5997004 baseEnd_5997004 := by
    simpa [prefixWord, tailWord_5997004, baseEnd_5997004] using wordTrace_append hprefix tailTrace_5997004
  have hstable : (prefixWord ++ tailWord_5997004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997004).length < 2 ^ (prefixWord ++ tailWord_5997004).sum := by decide
  have hdescent : baseEnd_5997004 < baseStart_5997004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997021 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5997021 : Nat := 118140960795 + 5997021 * 2 ^ 59
def prefixEnd_5997021 : Nat := 4983230072969 + 3 ^ 40 * 5997021 * 2
def baseEnd_5997021 : Nat := 3079354268106886361457709

theorem tailTrace_5997021 : CollatzResearch.WordTrace tailWord_5997021 prefixEnd_5997021 3079354268106886361457709 := by
  unfold tailWord_5997021
  simp only [CollatzResearch.WordTrace]
  refine ⟨218729325206824601490414917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145819550137883067660276611 218729325206824601490414917)
  ·
    refine ⟨41011748476279612779452797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218729325206824601490414917 41011748476279612779452797)
    ·
      refine ⟨15379405678604854792294799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41011748476279612779452797 15379405678604854792294799)
      ·
        refine ⟨23069108517907282188442199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379405678604854792294799 23069108517907282188442199)
        ·
          refine ⟨34603662776860923282663299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23069108517907282188442199 34603662776860923282663299)
          ·
            refine ⟨51905494165291384923994949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34603662776860923282663299 51905494165291384923994949)
            ·
              refine ⟨9732280155992134673249053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51905494165291384923994949 9732280155992134673249053)
              ·
                refine ⟨3649605058497050502468395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9732280155992134673249053 3649605058497050502468395)
                ·
                  refine ⟨5474407587745575753702593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649605058497050502468395 5474407587745575753702593)
                  ·
                    refine ⟨4105805690809181815276945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474407587745575753702593 4105805690809181815276945)
                    ·
                      refine ⟨3079354268106886361457709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105805690809181815276945 3079354268106886361457709)
                      ·
                        rfl

theorem cell23_5997021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5997021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997021 prefixEnd_5997021 := by exact prefixLift 5997021
  have htrace : WordTrace (prefixWord ++ tailWord_5997021) baseStart_5997021 baseEnd_5997021 := by
    simpa [prefixWord, tailWord_5997021, baseEnd_5997021] using wordTrace_append hprefix tailTrace_5997021
  have hstable : (prefixWord ++ tailWord_5997021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997021).length < 2 ^ (prefixWord ++ tailWord_5997021).sum := by decide
  have hdescent : baseEnd_5997021 < baseStart_5997021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997053 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5997053 : Nat := 118140960795 + 5997053 * 2 ^ 59
def prefixEnd_5997053 : Nat := 4983230072969 + 3 ^ 40 * 5997053 * 2
def baseEnd_5997053 : Nat := 1026456899829276745419187

theorem tailTrace_5997053 : CollatzResearch.WordTrace tailWord_5997053 prefixEnd_5997053 1026456899829276745419187 := by
  unfold tailWord_5997053
  simp only [CollatzResearch.WordTrace]
  refine ⟨218730492342708670955579813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145820328228472447303719875 218730492342708670955579813)
  ·
    refine ⟨41011967314257875804171215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218730492342708670955579813 41011967314257875804171215)
    ·
      refine ⟨61517950971386813706256823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41011967314257875804171215 61517950971386813706256823)
      ·
        refine ⟨92276926457080220559385235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61517950971386813706256823 92276926457080220559385235)
        ·
          refine ⟨138415389685620330839077853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92276926457080220559385235 138415389685620330839077853)
          ·
            refine ⟨51905771132107624064654195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138415389685620330839077853 51905771132107624064654195)
            ·
              refine ⟨77858656698161436096981293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51905771132107624064654195 77858656698161436096981293)
              ·
                refine ⟨29196996261810538536367985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77858656698161436096981293 29196996261810538536367985)
                ·
                  refine ⟨21897747196357903902275989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29196996261810538536367985 21897747196357903902275989)
                  ·
                    refine ⟨1026456899829276745419187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21897747196357903902275989 1026456899829276745419187)
                    ·
                      rfl

theorem cell23_5997053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5997053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997053 prefixEnd_5997053 := by exact prefixLift 5997053
  have htrace : WordTrace (prefixWord ++ tailWord_5997053) baseStart_5997053 baseEnd_5997053 := by
    simpa [prefixWord, tailWord_5997053, baseEnd_5997053] using wordTrace_append hprefix tailTrace_5997053
  have hstable : (prefixWord ++ tailWord_5997053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997053).length < 2 ^ (prefixWord ++ tailWord_5997053).sum := by decide
  have hdescent : baseEnd_5997053 < baseStart_5997053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997073 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_5997073 : Nat := 118140960795 + 5997073 * 2 ^ 59
def prefixEnd_5997073 : Nat := 4983230072969 + 3 ^ 40 * 5997073 * 2
def baseEnd_5997073 : Nat := 3079380969100920158007469

theorem tailTrace_5997073 : CollatzResearch.WordTrace tailWord_5997073 prefixEnd_5997073 3079380969100920158007469 := by
  unfold tailWord_5997073
  simp only [CollatzResearch.WordTrace]
  refine ⟨218731221802636214371307873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145820814535090809580871915 218731221802636214371307873)
  ·
    refine ⟨164048416351977160778480905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218731221802636214371307873 164048416351977160778480905)
    ·
      refine ⟨123036312263982870583860679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164048416351977160778480905 123036312263982870583860679)
      ·
        refine ⟨184554468395974305875791019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123036312263982870583860679 184554468395974305875791019)
        ·
          refine ⟨276831702593961458813686529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184554468395974305875791019 276831702593961458813686529)
          ·
            refine ⟨207623776945471094110264897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276831702593961458813686529 207623776945471094110264897)
            ·
              refine ⟨155717832709103320582698673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207623776945471094110264897 155717832709103320582698673)
              ·
                refine ⟨116788374531827490437024005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155717832709103320582698673 116788374531827490437024005)
                ·
                  refine ⟨21897820224717654456942001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116788374531827490437024005 21897820224717654456942001)
                  ·
                    refine ⟨16423365168538240842706501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21897820224717654456942001 16423365168538240842706501)
                    ·
                      refine ⟨3079380969100920158007469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16423365168538240842706501 3079380969100920158007469)
                      ·
                        rfl

theorem cell23_5997073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_5997073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997073 prefixEnd_5997073 := by exact prefixLift 5997073
  have htrace : WordTrace (prefixWord ++ tailWord_5997073) baseStart_5997073 baseEnd_5997073 := by
    simpa [prefixWord, tailWord_5997073, baseEnd_5997073] using wordTrace_append hprefix tailTrace_5997073
  have hstable : (prefixWord ++ tailWord_5997073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997073).length < 2 ^ (prefixWord ++ tailWord_5997073).sum := by decide
  have hdescent : baseEnd_5997073 < baseStart_5997073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997077 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_5997077 : Nat := 118140960795 + 5997077 * 2 ^ 59
def prefixEnd_5997077 : Nat := 4983230072969 + 3 ^ 40 * 5997077 * 2
def baseEnd_5997077 : Nat := 3079383023023538142357451

theorem tailTrace_5997077 : CollatzResearch.WordTrace tailWord_5997077 prefixEnd_5997077 3079383023023538142357451 := by
  unfold tailWord_5997077
  simp only [CollatzResearch.WordTrace]
  refine ⟨218731367694621723054453485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145820911796414482036302323 218731367694621723054453485)
  ·
    refine ⟨82024262885483146145420057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218731367694621723054453485 82024262885483146145420057)
    ·
      refine ⟨61518197164112359609065043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82024262885483146145420057 61518197164112359609065043)
      ·
        refine ⟨92277295746168539413597565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61518197164112359609065043 92277295746168539413597565)
        ·
          refine ⟨34603985904813202280099087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92277295746168539413597565 34603985904813202280099087)
          ·
            refine ⟨51905978857219803420148631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34603985904813202280099087 51905978857219803420148631)
            ·
              refine ⟨77858968285829705130222947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51905978857219803420148631 77858968285829705130222947)
              ·
                refine ⟨116788452428744557695334421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77858968285829705130222947 116788452428744557695334421)
                ·
                  refine ⟨5474458707597401141968801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116788452428744557695334421 5474458707597401141968801)
                  ·
                    refine ⟨4105844030698050856476601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474458707597401141968801 4105844030698050856476601)
                    ·
                      refine ⟨3079383023023538142357451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105844030698050856476601 3079383023023538142357451)
                      ·
                        rfl

theorem cell23_5997077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_5997077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997077 prefixEnd_5997077 := by exact prefixLift 5997077
  have htrace : WordTrace (prefixWord ++ tailWord_5997077) baseStart_5997077 baseEnd_5997077 := by
    simpa [prefixWord, tailWord_5997077, baseEnd_5997077] using wordTrace_append hprefix tailTrace_5997077
  have hstable : (prefixWord ++ tailWord_5997077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997077).length < 2 ^ (prefixWord ++ tailWord_5997077).sum := by decide
  have hdescent : baseEnd_5997077 < baseStart_5997077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997080 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5997080 : Nat := 118140960795 + 5997080 * 2 ^ 59
def prefixEnd_5997080 : Nat := 4983230072969 + 3 ^ 40 * 5997080 * 2
def baseEnd_5997080 : Nat := 3079384563465501630619937

theorem tailTrace_5997080 : CollatzResearch.WordTrace tailWord_5997080 prefixEnd_5997080 3079384563465501630619937 := by
  unfold tailWord_5997080
  simp only [CollatzResearch.WordTrace]
  refine ⟨109365738556805427283406347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145820984742407236377875129 109365738556805427283406347)
  ·
    refine ⟨164048607835208140925109521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109365738556805427283406347 164048607835208140925109521)
    ·
      refine ⟨123036455876406105693832141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164048607835208140925109521 123036455876406105693832141)
      ·
        refine ⟨46138670953652289635187053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123036455876406105693832141 46138670953652289635187053)
        ·
          refine ⟨17302001607619608613195145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46138670953652289635187053 17302001607619608613195145)
          ·
            refine ⟨12976501205714706459896359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17302001607619608613195145 12976501205714706459896359)
            ·
              refine ⟨19464751808572059689844539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976501205714706459896359 19464751808572059689844539)
              ·
                refine ⟨29197127712858089534766809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19464751808572059689844539 29197127712858089534766809)
                ·
                  refine ⟨21897845784643567151075107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29197127712858089534766809 21897845784643567151075107)
                  ·
                    refine ⟨32846768676965350726612661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21897845784643567151075107 32846768676965350726612661)
                    ·
                      refine ⟨3079384563465501630619937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32846768676965350726612661 3079384563465501630619937)
                      ·
                        rfl

theorem cell23_5997080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5997080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997080 prefixEnd_5997080 := by exact prefixLift 5997080
  have htrace : WordTrace (prefixWord ++ tailWord_5997080) baseStart_5997080 baseEnd_5997080 := by
    simpa [prefixWord, tailWord_5997080, baseEnd_5997080] using wordTrace_append hprefix tailTrace_5997080
  have hstable : (prefixWord ++ tailWord_5997080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997080).length < 2 ^ (prefixWord ++ tailWord_5997080).sum := by decide
  have hdescent : baseEnd_5997080 < baseStart_5997080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997100 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 5]
def baseStart_5997100 : Nat := 118140960795 + 5997100 * 2 ^ 59
def prefixEnd_5997100 : Nat := 4983230072969 + 3 ^ 40 * 5997100 * 2
def baseEnd_5997100 : Nat := 342154981453176839152205

theorem tailTrace_5997100 : CollatzResearch.WordTrace tailWord_5997100 prefixEnd_5997100 342154981453176839152205 := by
  unfold tailWord_5997100
  simp only [CollatzResearch.WordTrace]
  refine ⟨109366103286769198991270377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145821471049025598655027169 109366103286769198991270377)
  ·
    refine ⟨82024577465076899243452783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109366103286769198991270377 82024577465076899243452783)
    ·
      refine ⟨123036866197615348865179175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82024577465076899243452783 123036866197615348865179175)
      ·
        refine ⟨184555299296423023297768763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123036866197615348865179175 184555299296423023297768763)
        ·
          refine ⟨276832948944634534946653145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184555299296423023297768763 276832948944634534946653145)
          ·
            refine ⟨207624711708475901209989859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276832948944634534946653145 207624711708475901209989859)
            ·
              refine ⟨311437067562713851814984789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207624711708475901209989859 311437067562713851814984789)
              ·
                refine ⟨3649653135500552950956853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 311437067562713851814984789 3649653135500552950956853)
                ·
                  refine ⟨342154981453176839152205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3649653135500552950956853 342154981453176839152205)
                  ·
                    rfl

theorem cell23_5997100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_5997100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997100 prefixEnd_5997100 := by exact prefixLift 5997100
  have htrace : WordTrace (prefixWord ++ tailWord_5997100) baseStart_5997100 baseEnd_5997100 := by
    simpa [prefixWord, tailWord_5997100, baseEnd_5997100] using wordTrace_append hprefix tailTrace_5997100
  have hstable : (prefixWord ++ tailWord_5997100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997100).length < 2 ^ (prefixWord ++ tailWord_5997100).sum := by decide
  have hdescent : baseEnd_5997100 < baseStart_5997100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997130 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_5997130 : Nat := 118140960795 + 5997130 * 2 ^ 59
def prefixEnd_5997130 : Nat := 4983230072969 + 3 ^ 40 * 5997130 * 2
def baseEnd_5997130 : Nat := 1026470079166075478331569

theorem tailTrace_5997130 : CollatzResearch.WordTrace tailWord_5997130 prefixEnd_5997130 1026470079166075478331569 := by
  unfold tailWord_5997130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54683325190857428276533211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145822200508953142070755229 54683325190857428276533211)
  ·
    refine ⟨82024987786286142414799817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54683325190857428276533211 82024987786286142414799817)
    ·
      refine ⟨61518740839714606811099863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82024987786286142414799817 61518740839714606811099863)
      ·
        refine ⟨92278111259571910216649795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61518740839714606811099863 92278111259571910216649795)
        ·
          refine ⟨138417166889357865324974693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92278111259571910216649795 138417166889357865324974693)
          ·
            refine ⟨25953218791754599748432755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138417166889357865324974693 25953218791754599748432755)
            ·
              refine ⟨38929828187631899622649133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25953218791754599748432755 38929828187631899622649133)
              ·
                refine ⟨14598685570361962358493425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38929828187631899622649133 14598685570361962358493425)
                ·
                  refine ⟨10949014177771471768870069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598685570361962358493425 10949014177771471768870069)
                  ·
                    refine ⟨1026470079166075478331569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10949014177771471768870069 1026470079166075478331569)
                    ·
                      rfl

theorem cell23_5997130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_5997130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997130 prefixEnd_5997130 := by exact prefixLift 5997130
  have htrace : WordTrace (prefixWord ++ tailWord_5997130) baseStart_5997130 baseEnd_5997130 := by
    simpa [prefixWord, tailWord_5997130, baseEnd_5997130] using wordTrace_append hprefix tailTrace_5997130
  have hstable : (prefixWord ++ tailWord_5997130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997130).length < 2 ^ (prefixWord ++ tailWord_5997130).sum := by decide
  have hdescent : baseEnd_5997130 < baseStart_5997130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997140 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5997140 : Nat := 118140960795 + 5997140 * 2 ^ 59
def prefixEnd_5997140 : Nat := 4983230072969 + 3 ^ 40 * 5997140 * 2
def baseEnd_5997140 : Nat := 3079415372304771395869661

theorem tailTrace_5997140 : CollatzResearch.WordTrace tailWord_5997140 prefixEnd_5997140 3079415372304771395869661 := by
  unfold tailWord_5997140
  simp only [CollatzResearch.WordTrace]
  refine ⟨109366832746696742406998437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145822443662262323209331249 109366832746696742406998437)
  ·
    refine ⟨20506281140005639201312207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109366832746696742406998437 20506281140005639201312207)
    ·
      refine ⟨30759421710008458801968311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20506281140005639201312207 30759421710008458801968311)
      ·
        refine ⟨46139132565012688202952467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30759421710008458801968311 46139132565012688202952467)
        ·
          refine ⟨69208698847519032304428701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46139132565012688202952467 69208698847519032304428701)
          ·
            refine ⟨25953262067819637114160763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69208698847519032304428701 25953262067819637114160763)
            ·
              refine ⟨38929893101729455671241145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25953262067819637114160763 38929893101729455671241145)
              ·
                refine ⟨29197419826297091753430859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38929893101729455671241145 29197419826297091753430859)
                ·
                  refine ⟨43796129739445637630146289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29197419826297091753430859 43796129739445637630146289)
                  ·
                    refine ⟨32847097304584228222609717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43796129739445637630146289 32847097304584228222609717)
                    ·
                      refine ⟨3079415372304771395869661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32847097304584228222609717 3079415372304771395869661)
                      ·
                        rfl

theorem cell23_5997140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5997140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997140 prefixEnd_5997140 := by exact prefixLift 5997140
  have htrace : WordTrace (prefixWord ++ tailWord_5997140) baseStart_5997140 baseEnd_5997140 := by
    simpa [prefixWord, tailWord_5997140, baseEnd_5997140] using wordTrace_append hprefix tailTrace_5997140
  have hstable : (prefixWord ++ tailWord_5997140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997140).length < 2 ^ (prefixWord ++ tailWord_5997140).sum := by decide
  have hdescent : baseEnd_5997140 < baseStart_5997140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997163 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_5997163 : Nat := 118140960795 + 5997163 * 2 ^ 59
def prefixEnd_5997163 : Nat := 4983230072969 + 3 ^ 40 * 5997163 * 2
def baseEnd_5997163 : Nat := 3079427182359824805882055

theorem tailTrace_5997163 : CollatzResearch.WordTrace tailWord_5997163 prefixEnd_5997163 3079427182359824805882055 := by
  unfold tailWord_5997163
  simp only [CollatzResearch.WordTrace]
  refine ⟨218734504372310159742084143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145823002914873439828056095 218734504372310159742084143)
  ·
    refine ⟨328101756558465239613126215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218734504372310159742084143 328101756558465239613126215)
    ·
      refine ⟨492152634837697859419689323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328101756558465239613126215 492152634837697859419689323)
      ·
        refine ⟨738228952256546789129533985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492152634837697859419689323 738228952256546789129533985)
        ·
          refine ⟨553671714192410091847150489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738228952256546789129533985 553671714192410091847150489)
          ·
            refine ⟨415253785644307568885362867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553671714192410091847150489 415253785644307568885362867)
            ·
              refine ⟨622880678466461353328044301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415253785644307568885362867 622880678466461353328044301)
              ·
                refine ⟨233580254424923007498016613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622880678466461353328044301 233580254424923007498016613)
                ·
                  refine ⟨43796297704673063905878115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233580254424923007498016613 43796297704673063905878115)
                  ·
                    refine ⟨65694446557009595858817173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43796297704673063905878115 65694446557009595858817173)
                    ·
                      refine ⟨3079427182359824805882055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65694446557009595858817173 3079427182359824805882055)
                      ·
                        rfl

theorem cell23_5997163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_5997163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997163 prefixEnd_5997163 := by exact prefixLift 5997163
  have htrace : WordTrace (prefixWord ++ tailWord_5997163) baseStart_5997163 baseEnd_5997163 := by
    simpa [prefixWord, tailWord_5997163, baseEnd_5997163] using wordTrace_append hprefix tailTrace_5997163
  have hstable : (prefixWord ++ tailWord_5997163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997163).length < 2 ^ (prefixWord ++ tailWord_5997163).sum := by decide
  have hdescent : baseEnd_5997163 < baseStart_5997163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997177 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_5997177 : Nat := 118140960795 + 5997177 * 2 ^ 59
def prefixEnd_5997177 : Nat := 4983230072969 + 3 ^ 40 * 5997177 * 2
def baseEnd_5997177 : Nat := 1026478123696329250368997

theorem tailTrace_5997177 : CollatzResearch.WordTrace tailWord_5997177 prefixEnd_5997177 1026478123696329250368997 := by
  unfold tailWord_5997177
  simp only [CollatzResearch.WordTrace]
  refine ⟨218735014994259440133093785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145823343329506293422062523 218735014994259440133093785)
  ·
    refine ⟨164051261245694580099820339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218735014994259440133093785 164051261245694580099820339)
    ·
      refine ⟨246076891868541870149730509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164051261245694580099820339 246076891868541870149730509)
      ·
        refine ⟨92278834450703201306148941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246076891868541870149730509 92278834450703201306148941)
        ·
          refine ⟨34604562919013700489805853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92278834450703201306148941 34604562919013700489805853)
          ·
            refine ⟨12976711094630137683677195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34604562919013700489805853 12976711094630137683677195)
            ·
              refine ⟨19465066641945206525515793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976711094630137683677195 19465066641945206525515793)
              ·
                refine ⟨14598799981458904894136845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19465066641945206525515793 14598799981458904894136845)
                ·
                  refine ⟨5474549993047089335301317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14598799981458904894136845 5474549993047089335301317)
                  ·
                    refine ⟨1026478123696329250368997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474549993047089335301317 1026478123696329250368997)
                    ·
                      rfl

theorem cell23_5997177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_5997177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997177 prefixEnd_5997177 := by exact prefixLift 5997177
  have htrace : WordTrace (prefixWord ++ tailWord_5997177) baseStart_5997177 baseEnd_5997177 := by
    simpa [prefixWord, tailWord_5997177, baseEnd_5997177] using wordTrace_append hprefix tailTrace_5997177
  have hstable : (prefixWord ++ tailWord_5997177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997177).length < 2 ^ (prefixWord ++ tailWord_5997177).sum := by decide
  have hdescent : baseEnd_5997177 < baseStart_5997177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997187 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3]
def baseStart_5997187 : Nat := 118140960795 + 5997187 * 2 ^ 59
def prefixEnd_5997187 : Nat := 4983230072969 + 3 ^ 40 * 5997187 * 2
def baseEnd_5997187 : Nat := 3079439505895532711981945

theorem tailTrace_5997187 : CollatzResearch.WordTrace tailWord_5997187 prefixEnd_5997187 3079439505895532711981945 := by
  unfold tailWord_5997187
  simp only [CollatzResearch.WordTrace]
  refine ⟨218735379724223211840957815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145823586482815474560638543 218735379724223211840957815)
  ·
    refine ⟨328103069586334817761436723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218735379724223211840957815 328103069586334817761436723)
    ·
      refine ⟨492154604379502226642155085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328103069586334817761436723 492154604379502226642155085)
      ·
        refine ⟨184557976642313334990808157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492154604379502226642155085 184557976642313334990808157)
        ·
          refine ⟨69209241240867500621553059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184557976642313334990808157 69209241240867500621553059)
          ·
            refine ⟨103813861861301250932329589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69209241240867500621553059 103813861861301250932329589)
            ·
              refine ⟨9732549549496992274905899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103813861861301250932329589 9732549549496992274905899)
              ·
                refine ⟨14598824324245488412358849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732549549496992274905899 14598824324245488412358849)
                ·
                  refine ⟨10949118243184116309269137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598824324245488412358849 10949118243184116309269137)
                  ·
                    refine ⟨8211838682388087231951853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10949118243184116309269137 8211838682388087231951853)
                    ·
                      refine ⟨3079439505895532711981945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211838682388087231951853 3079439505895532711981945)
                      ·
                        rfl

theorem cell23_5997187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_5997187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997187 prefixEnd_5997187 := by exact prefixLift 5997187
  have htrace : WordTrace (prefixWord ++ tailWord_5997187) baseStart_5997187 baseEnd_5997187 := by
    simpa [prefixWord, tailWord_5997187, baseEnd_5997187] using wordTrace_append hprefix tailTrace_5997187
  have hstable : (prefixWord ++ tailWord_5997187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997187).length < 2 ^ (prefixWord ++ tailWord_5997187).sum := by decide
  have hdescent : baseEnd_5997187 < baseStart_5997187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997244 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5997244 : Nat := 118140960795 + 5997244 * 2 ^ 59
def prefixEnd_5997244 : Nat := 4983230072969 + 3 ^ 40 * 5997244 * 2
def baseEnd_5997244 : Nat := 3079468774292838988969183

theorem tailTrace_5997244 : CollatzResearch.WordTrace tailWord_5997244 prefixEnd_5997244 3079468774292838988969183 := by
  unfold tailWord_5997244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109368729342508355287891393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145824972456677807050521857 109368729342508355287891393)
  ·
    refine ⟨82026547006881266465918545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109368729342508355287891393 82026547006881266465918545)
    ·
      refine ⟨61519910255160949849438909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82026547006881266465918545 61519910255160949849438909)
      ·
        refine ⟨23069966345685356193539591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61519910255160949849438909 23069966345685356193539591)
        ·
          refine ⟨34604949518528034290309387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23069966345685356193539591 34604949518528034290309387)
          ·
            refine ⟨51907424277792051435464081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34604949518528034290309387 51907424277792051435464081)
            ·
              refine ⟨38930568208344038576598061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51907424277792051435464081 38930568208344038576598061)
              ·
                refine ⟨14598963078129014466224273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38930568208344038576598061 14598963078129014466224273)
                ·
                  refine ⟨10949222308596760849668205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598963078129014466224273 10949222308596760849668205)
                  ·
                    refine ⟨4105958365723785318625577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10949222308596760849668205 4105958365723785318625577)
                    ·
                      refine ⟨3079468774292838988969183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4105958365723785318625577 3079468774292838988969183)
                      ·
                        rfl

theorem cell23_5997244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5997244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997244 prefixEnd_5997244 := by exact prefixLift 5997244
  have htrace : WordTrace (prefixWord ++ tailWord_5997244) baseStart_5997244 baseEnd_5997244 := by
    simpa [prefixWord, tailWord_5997244, baseEnd_5997244] using wordTrace_append hprefix tailTrace_5997244
  have hstable : (prefixWord ++ tailWord_5997244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997244).length < 2 ^ (prefixWord ++ tailWord_5997244).sum := by decide
  have hdescent : baseEnd_5997244 < baseStart_5997244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997268 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5997268 : Nat := 118140960795 + 5997268 * 2 ^ 59
def prefixEnd_5997268 : Nat := 4983230072969 + 3 ^ 40 * 5997268 * 2
def baseEnd_5997268 : Nat := 3079481097828546895069073

theorem tailTrace_5997268 : CollatzResearch.WordTrace tailWord_5997268 prefixEnd_5997268 3079481097828546895069073 := by
  unfold tailWord_5997268
  simp only [CollatzResearch.WordTrace]
  refine ⟨109369167018464881337328229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145825556024619841783104305 109369167018464881337328229)
  ·
    refine ⟨20506718815962165250749043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109369167018464881337328229 20506718815962165250749043)
    ·
      refine ⟨30760078223943247876123565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20506718815962165250749043 30760078223943247876123565)
      ·
        refine ⟨11535029333978717953546337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30760078223943247876123565 11535029333978717953546337)
        ·
          refine ⟨8651272000484038465159753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11535029333978717953546337 8651272000484038465159753)
          ·
            refine ⟨6488454000363028848869815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651272000484038465159753 6488454000363028848869815)
            ·
              refine ⟨9732681000544543273304723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488454000363028848869815 9732681000544543273304723)
              ·
                refine ⟨14599021500816814909957085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732681000544543273304723 14599021500816814909957085)
                ·
                  refine ⟨5474633062806305591233907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14599021500816814909957085 5474633062806305591233907)
                  ·
                    refine ⟨8211949594209458386850861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5474633062806305591233907 8211949594209458386850861)
                    ·
                      refine ⟨3079481097828546895069073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211949594209458386850861 3079481097828546895069073)
                      ·
                        rfl

theorem cell23_5997268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5997268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997268 prefixEnd_5997268 := by exact prefixLift 5997268
  have htrace : WordTrace (prefixWord ++ tailWord_5997268) baseStart_5997268 baseEnd_5997268 := by
    simpa [prefixWord, tailWord_5997268, baseEnd_5997268] using wordTrace_append hprefix tailTrace_5997268
  have hstable : (prefixWord ++ tailWord_5997268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997268).length < 2 ^ (prefixWord ++ tailWord_5997268).sum := by decide
  have hdescent : baseEnd_5997268 < baseStart_5997268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997284 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5997284 : Nat := 118140960795 + 5997284 * 2 ^ 59
def prefixEnd_5997284 : Nat := 4983230072969 + 3 ^ 40 * 5997284 * 2
def baseEnd_5997284 : Nat := 1026496437839672944156333

theorem tailTrace_5997284 : CollatzResearch.WordTrace tailWord_5997284 prefixEnd_5997284 1026496437839672944156333 := by
  unfold tailWord_5997284
  simp only [CollatzResearch.WordTrace]
  refine ⟨109369458802435898703619453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145825945069914531604825937 109369458802435898703619453)
  ·
    refine ⟨41013547050913462013857295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109369458802435898703619453 41013547050913462013857295)
    ·
      refine ⟨61520320576370193020785943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41013547050913462013857295 61520320576370193020785943)
      ·
        refine ⟨92280480864555289531178915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61520320576370193020785943 92280480864555289531178915)
        ·
          refine ⟨138420721296832934296768373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92280480864555289531178915 138420721296832934296768373)
          ·
            refine ⟨12976942621578087590322035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138420721296832934296768373 12976942621578087590322035)
            ·
              refine ⟨19465413932367131385483053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976942621578087590322035 19465413932367131385483053)
              ·
                refine ⟨7299530224637674269556145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19465413932367131385483053 7299530224637674269556145)
                ·
                  refine ⟨5474647668478255702167109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299530224637674269556145 5474647668478255702167109)
                  ·
                    refine ⟨1026496437839672944156333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474647668478255702167109 1026496437839672944156333)
                    ·
                      rfl

theorem cell23_5997284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5997284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997284 prefixEnd_5997284 := by exact prefixLift 5997284
  have htrace : WordTrace (prefixWord ++ tailWord_5997284) baseStart_5997284 baseEnd_5997284 := by
    simpa [prefixWord, tailWord_5997284, baseEnd_5997284] using wordTrace_append hprefix tailTrace_5997284
  have hstable : (prefixWord ++ tailWord_5997284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997284).length < 2 ^ (prefixWord ++ tailWord_5997284).sum := by decide
  have hdescent : baseEnd_5997284 < baseStart_5997284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997294 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_5997294 : Nat := 118140960795 + 5997294 * 2 ^ 59
def prefixEnd_5997294 : Nat := 4983230072969 + 3 ^ 40 * 5997294 * 2
def baseEnd_5997294 : Nat := 3079494448325563793343953

theorem tailTrace_5997294 : CollatzResearch.WordTrace tailWord_5997294 prefixEnd_5997294 3079494448325563793343953 := by
  unfold tailWord_5997294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27342410291854446139387867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145826188223223712743401957 27342410291854446139387867)
  ·
    refine ⟨41013615437781669209081801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27342410291854446139387867 41013615437781669209081801)
    ·
      refine ⟨30760211578336251906811351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41013615437781669209081801 30760211578336251906811351)
      ·
        refine ⟨46140317367504377860217027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30760211578336251906811351 46140317367504377860217027)
        ·
          refine ⟨69210476051256566790325541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46140317367504377860217027 69210476051256566790325541)
          ·
            refine ⟨12976964259610606273186039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69210476051256566790325541 12976964259610606273186039)
            ·
              refine ⟨19465446389415909409779059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976964259610606273186039 19465446389415909409779059)
              ·
                refine ⟨29198169584123864114668589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19465446389415909409779059 29198169584123864114668589)
                ·
                  refine ⟨10949313594046449043000721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29198169584123864114668589 10949313594046449043000721)
                  ·
                    refine ⟨8211985195534836782250541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10949313594046449043000721 8211985195534836782250541)
                    ·
                      refine ⟨3079494448325563793343953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8211985195534836782250541 3079494448325563793343953)
                      ·
                        rfl

theorem cell23_5997294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_5997294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997294 prefixEnd_5997294 := by exact prefixLift 5997294
  have htrace : WordTrace (prefixWord ++ tailWord_5997294) baseStart_5997294 baseEnd_5997294 := by
    simpa [prefixWord, tailWord_5997294, baseEnd_5997294] using wordTrace_append hprefix tailTrace_5997294
  have hstable : (prefixWord ++ tailWord_5997294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997294).length < 2 ^ (prefixWord ++ tailWord_5997294).sum := by decide
  have hdescent : baseEnd_5997294 < baseStart_5997294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997381 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_5997381 : Nat := 118140960795 + 5997381 * 2 ^ 59
def prefixEnd_5997381 : Nat := 4983230072969 + 3 ^ 40 * 5997381 * 2
def baseEnd_5997381 : Nat := 3079539121142504952956053

theorem tailTrace_5997381 : CollatzResearch.WordTrace tailWord_5997381 prefixEnd_5997381 3079539121142504952956053 := by
  unfold tailWord_5997381
  simp only [CollatzResearch.WordTrace]
  refine ⟨218742455485520382973519997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145828303657013588649013331 218742455485520382973519997)
  ·
    refine ⟨82028420807070143615069999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218742455485520382973519997 82028420807070143615069999)
    ·
      refine ⟨123042631210605215422604999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82028420807070143615069999 123042631210605215422604999)
      ·
        refine ⟨184563946815907823133907499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123042631210605215422604999 184563946815907823133907499)
        ·
          refine ⟨276845920223861734700861249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184563946815907823133907499 276845920223861734700861249)
          ·
            refine ⟨207634440167896301025645937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276845920223861734700861249 207634440167896301025645937)
            ·
              refine ⟨155725830125922225769234453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207634440167896301025645937 155725830125922225769234453)
              ·
                refine ⟨7299648287152604332932865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155725830125922225769234453 7299648287152604332932865)
                ·
                  refine ⟨5474736215364453249699649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299648287152604332932865 5474736215364453249699649)
                  ·
                    refine ⟨4106052161523339937274737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474736215364453249699649 4106052161523339937274737)
                    ·
                      refine ⟨3079539121142504952956053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106052161523339937274737 3079539121142504952956053)
                      ·
                        rfl

theorem cell23_5997381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_5997381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997381 prefixEnd_5997381 := by exact prefixLift 5997381
  have htrace : WordTrace (prefixWord ++ tailWord_5997381) baseStart_5997381 baseEnd_5997381 := by
    simpa [prefixWord, tailWord_5997381, baseEnd_5997381] using wordTrace_append hprefix tailTrace_5997381
  have hstable : (prefixWord ++ tailWord_5997381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997381).length < 2 ^ (prefixWord ++ tailWord_5997381).sum := by decide
  have hdescent : baseEnd_5997381 < baseStart_5997381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997404 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 7]
def baseStart_5997404 : Nat := 118140960795 + 5997404 * 2 ^ 59
def prefixEnd_5997404 : Nat := 4983230072969 + 3 ^ 40 * 5997404 * 2
def baseEnd_5997404 : Nat := 342172325688617595885383

theorem tailTrace_5997404 : CollatzResearch.WordTrace tailWord_5997404 prefixEnd_5997404 342172325688617595885383 := by
  unfold tailWord_5997404
  simp only [CollatzResearch.WordTrace]
  refine ⟨109371647182218528950803633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145828862909624705267738177 109371647182218528950803633)
  ·
    refine ⟨82028735386663896713102725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109371647182218528950803633 82028735386663896713102725)
    ·
      refine ⟨15380387884999480633706761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82028735386663896713102725 15380387884999480633706761)
      ·
        refine ⟨11535290913749610475280071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15380387884999480633706761 11535290913749610475280071)
        ·
          refine ⟨17302936370624415712920107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535290913749610475280071 17302936370624415712920107)
          ·
            refine ⟨25954404555936623569380161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17302936370624415712920107 25954404555936623569380161)
            ·
              refine ⟨19465803416952467677035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25954404555936623569380161 19465803416952467677035121)
              ·
                refine ⟨14599352562714350757776341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19465803416952467677035121 14599352562714350757776341)
                ·
                  refine ⟨342172325688617595885383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14599352562714350757776341 342172325688617595885383)
                  ·
                    rfl

theorem cell23_5997404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_5997404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997404 prefixEnd_5997404 := by exact prefixLift 5997404
  have htrace : WordTrace (prefixWord ++ tailWord_5997404) baseStart_5997404 baseEnd_5997404 := by
    simpa [prefixWord, tailWord_5997404, baseEnd_5997404] using wordTrace_append hprefix tailTrace_5997404
  have hstable : (prefixWord ++ tailWord_5997404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997404).length < 2 ^ (prefixWord ++ tailWord_5997404).sum := by decide
  have hdescent : baseEnd_5997404 < baseStart_5997404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997438 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_5997438 : Nat := 118140960795 + 5997438 * 2 ^ 59
def prefixEnd_5997438 : Nat := 4983230072969 + 3 ^ 40 * 5997438 * 2
def baseEnd_5997438 : Nat := 342174265504423469993699

theorem tailTrace_5997438 : CollatzResearch.WordTrace tailWord_5997438 prefixEnd_5997438 342174265504423469993699 := by
  unfold tailWord_5997438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27343066805789235213543121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145829689630875921138896645 27343066805789235213543121)
  ·
    refine ⟨20507300104341926410157341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27343066805789235213543121 20507300104341926410157341)
    ·
      refine ⟨7690237539128222403809003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20507300104341926410157341 7690237539128222403809003)
      ·
        refine ⟨11535356308692333605713505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690237539128222403809003 11535356308692333605713505)
        ·
          refine ⟨8651517231519250204285129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11535356308692333605713505 8651517231519250204285129)
          ·
            refine ⟨6488637923639437653213847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651517231519250204285129 6488637923639437653213847)
            ·
              refine ⟨9732956885459156479820771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488637923639437653213847 9732956885459156479820771)
              ·
                refine ⟨14599435328188734719731157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732956885459156479820771 14599435328188734719731157)
                ·
                  refine ⟨342174265504423469993699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14599435328188734719731157 342174265504423469993699)
                  ·
                    rfl

theorem cell23_5997438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_5997438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997438 prefixEnd_5997438 := by exact prefixLift 5997438
  have htrace : WordTrace (prefixWord ++ tailWord_5997438) baseStart_5997438 baseEnd_5997438 := by
    simpa [prefixWord, tailWord_5997438, baseEnd_5997438] using wordTrace_append hprefix tailTrace_5997438
  have hstable : (prefixWord ++ tailWord_5997438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997438).length < 2 ^ (prefixWord ++ tailWord_5997438).sum := by decide
  have hdescent : baseEnd_5997438 < baseStart_5997438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997471 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_5997471 : Nat := 118140960795 + 5997471 * 2 ^ 59
def prefixEnd_5997471 : Nat := 4983230072969 + 3 ^ 40 * 5997471 * 2
def baseEnd_5997471 : Nat := 3079585334401409600830639

theorem tailTrace_5997471 : CollatzResearch.WordTrace tailWord_5997471 prefixEnd_5997471 3079585334401409600830639 := by
  unfold tailWord_5997471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218745738055194328344296267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145830492036796218896197511 218745738055194328344296267)
  ·
    refine ⟨328118607082791492516444401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218745738055194328344296267 328118607082791492516444401)
    ·
      refine ⟨246088955312093619387333301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328118607082791492516444401 246088955312093619387333301)
      ·
        refine ⟨23070839560508776817562497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246088955312093619387333301 23070839560508776817562497)
        ·
          refine ⟨17303129670381582613171873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23070839560508776817562497 17303129670381582613171873)
          ·
            refine ⟨12977347252786186959878905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303129670381582613171873 12977347252786186959878905)
            ·
              refine ⟨9733010439589640219909179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12977347252786186959878905 9733010439589640219909179)
              ·
                refine ⟨14599515659384460329863769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733010439589640219909179 14599515659384460329863769)
                ·
                  refine ⟨10949636744538345247397827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14599515659384460329863769 10949636744538345247397827)
                  ·
                    refine ⟨16424455116807517871096741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10949636744538345247397827 16424455116807517871096741)
                    ·
                      refine ⟨3079585334401409600830639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16424455116807517871096741 3079585334401409600830639)
                      ·
                        rfl

theorem cell23_5997471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_5997471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997471 prefixEnd_5997471 := by exact prefixLift 5997471
  have htrace : WordTrace (prefixWord ++ tailWord_5997471) baseStart_5997471 baseEnd_5997471 := by
    simpa [prefixWord, tailWord_5997471, baseEnd_5997471] using wordTrace_append hprefix tailTrace_5997471
  have hstable : (prefixWord ++ tailWord_5997471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997471).length < 2 ^ (prefixWord ++ tailWord_5997471).sum := by decide
  have hdescent : baseEnd_5997471 < baseStart_5997471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997481 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 1, 4]
def baseStart_5997481 : Nat := 118140960795 + 5997481 * 2 ^ 59
def prefixEnd_5997481 : Nat := 4983230072969 + 3 ^ 40 * 5997481 * 2
def baseEnd_5997481 : Nat := 1026530156402651520568531

theorem tailTrace_5997481 : CollatzResearch.WordTrace tailWord_5997481 prefixEnd_5997481 1026530156402651520568531 := by
  unfold tailWord_5997481
  simp only [CollatzResearch.WordTrace]
  refine ⟨218746102785158100052160297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145830735190105400034773531 218746102785158100052160297)
  ·
    refine ⟨164059577088868575039120223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218746102785158100052160297 164059577088868575039120223)
    ·
      refine ⟨246089365633302862558680335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164059577088868575039120223 246089365633302862558680335)
      ·
        refine ⟨369134048449954293838020503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246089365633302862558680335 369134048449954293838020503)
        ·
          refine ⟨553701072674931440757030755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369134048449954293838020503 553701072674931440757030755)
          ·
            refine ⟨830551609012397161135546133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553701072674931440757030755 830551609012397161135546133)
            ·
              refine ⟨38932106672456116928228725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 830551609012397161135546133 38932106672456116928228725)
              ·
                refine ⟨3649885000542760962021443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38932106672456116928228725 3649885000542760962021443)
                ·
                  refine ⟨5474827500814141443032165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649885000542760962021443 5474827500814141443032165)
                  ·
                    refine ⟨1026530156402651520568531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474827500814141443032165 1026530156402651520568531)
                    ·
                      rfl

theorem cell23_5997481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_5997481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997481 prefixEnd_5997481 := by exact prefixLift 5997481
  have htrace : WordTrace (prefixWord ++ tailWord_5997481) baseStart_5997481 baseEnd_5997481 := by
    simpa [prefixWord, tailWord_5997481, baseEnd_5997481] using wordTrace_append hprefix tailTrace_5997481
  have hstable : (prefixWord ++ tailWord_5997481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997481).length < 2 ^ (prefixWord ++ tailWord_5997481).sum := by decide
  have hdescent : baseEnd_5997481 < baseStart_5997481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997521 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_5997521 : Nat := 118140960795 + 5997521 * 2 ^ 59
def prefixEnd_5997521 : Nat := 4983230072969 + 3 ^ 40 * 5997521 * 2
def baseEnd_5997521 : Nat := 3079611008434134405205409

theorem tailTrace_5997521 : CollatzResearch.WordTrace tailWord_5997521 prefixEnd_5997521 3079611008434134405205409 := by
  unfold tailWord_5997521
  simp only [CollatzResearch.WordTrace]
  refine ⟨218747561705013186883616417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145831707803342124589077611 218747561705013186883616417)
  ·
    refine ⟨164060671278759890162712313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218747561705013186883616417 164060671278759890162712313)
    ·
      refine ⟨123045503459069917622034235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164060671278759890162712313 123045503459069917622034235)
      ·
        refine ⟨184568255188604876433051353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123045503459069917622034235 184568255188604876433051353)
        ·
          refine ⟨138426191391453657324788515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184568255188604876433051353 138426191391453657324788515)
          ·
            refine ⟨207639287087180485987182773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138426191391453657324788515 207639287087180485987182773)
            ·
              refine ⟨19466183164423170561298385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207639287087180485987182773 19466183164423170561298385)
              ·
                refine ⟨14599637373317377920973789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19466183164423170561298385 14599637373317377920973789)
                ·
                  refine ⟨5474864014994016720365171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14599637373317377920973789 5474864014994016720365171)
                  ·
                    refine ⟨8212296022491025080547757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5474864014994016720365171 8212296022491025080547757)
                    ·
                      refine ⟨3079611008434134405205409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8212296022491025080547757 3079611008434134405205409)
                      ·
                        rfl

theorem cell23_5997521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_5997521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997521 prefixEnd_5997521 := by exact prefixLift 5997521
  have htrace : WordTrace (prefixWord ++ tailWord_5997521) baseStart_5997521 baseEnd_5997521 := by
    simpa [prefixWord, tailWord_5997521, baseEnd_5997521] using wordTrace_append hprefix tailTrace_5997521
  have hstable : (prefixWord ++ tailWord_5997521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997521).length < 2 ^ (prefixWord ++ tailWord_5997521).sum := by decide
  have hdescent : baseEnd_5997521 < baseStart_5997521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997525 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5997525 : Nat := 118140960795 + 5997525 * 2 ^ 59
def prefixEnd_5997525 : Nat := 4983230072969 + 3 ^ 40 * 5997525 * 2
def baseEnd_5997525 : Nat := 3079613062356752389555391

theorem tailTrace_5997525 : CollatzResearch.WordTrace tailWord_5997525 prefixEnd_5997525 3079613062356752389555391 := by
  unfold tailWord_5997525
  simp only [CollatzResearch.WordTrace]
  refine ⟨218747707596998695566762029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145831805064665797044508019 218747707596998695566762029)
  ·
    refine ⟨82030390348874510837535761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218747707596998695566762029 82030390348874510837535761)
    ·
      refine ⟨61522792761655883128151821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82030390348874510837535761 61522792761655883128151821)
      ·
        refine ⟨23071047285620956173056933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61522792761655883128151821 23071047285620956173056933)
        ·
          refine ⟨4325821366053929282448175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23071047285620956173056933 4325821366053929282448175)
          ·
            refine ⟨6488732049080893923672263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325821366053929282448175 6488732049080893923672263)
            ·
              refine ⟨9733098073621340885508395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488732049080893923672263 9733098073621340885508395)
              ·
                refine ⟨14599647110432011328262593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733098073621340885508395 14599647110432011328262593)
                ·
                  refine ⟨10949735332824008496196945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14599647110432011328262593 10949735332824008496196945)
                  ·
                    refine ⟨8212301499618006372147709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10949735332824008496196945 8212301499618006372147709)
                    ·
                      refine ⟨3079613062356752389555391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8212301499618006372147709 3079613062356752389555391)
                      ·
                        rfl

theorem cell23_5997525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5997525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997525 prefixEnd_5997525 := by exact prefixLift 5997525
  have htrace : WordTrace (prefixWord ++ tailWord_5997525) baseStart_5997525 baseEnd_5997525 := by
    simpa [prefixWord, tailWord_5997525, baseEnd_5997525] using wordTrace_append hprefix tailTrace_5997525
  have hstable : (prefixWord ++ tailWord_5997525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997525).length < 2 ^ (prefixWord ++ tailWord_5997525).sum := by decide
  have hdescent : baseEnd_5997525 < baseStart_5997525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997564 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_5997564 : Nat := 118140960795 + 5997564 * 2 ^ 59
def prefixEnd_5997564 : Nat := 4983230072969 + 3 ^ 40 * 5997564 * 2
def baseEnd_5997564 : Nat := 3079633088102277736967711

theorem tailTrace_5997564 : CollatzResearch.WordTrace tailWord_5997564 prefixEnd_5997564 3079633088102277736967711 := by
  unfold tailWord_5997564
  simp only [CollatzResearch.WordTrace]
  refine ⟨109374565021928702613715873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145832753362571603484954497 109374565021928702613715873)
  ·
    refine ⟨82030923766446526960286905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109374565021928702613715873 82030923766446526960286905)
    ·
      refine ⟨61523192824834895220215179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82030923766446526960286905 61523192824834895220215179)
      ·
        refine ⟨92284789237252342830322769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61523192824834895220215179 92284789237252342830322769)
        ·
          refine ⟨69213591927939257122742077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92284789237252342830322769 69213591927939257122742077)
          ·
            refine ⟨25955096972977221421028279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69213591927939257122742077 25955096972977221421028279)
            ·
              refine ⟨38932645459465832131542419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25955096972977221421028279 38932645459465832131542419)
              ·
                refine ⟨58398968189198748197313629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38932645459465832131542419 58398968189198748197313629)
                ·
                  refine ⟨21899613070949530573992611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58398968189198748197313629 21899613070949530573992611)
                  ·
                    refine ⟨32849419606424295860988917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21899613070949530573992611 32849419606424295860988917)
                    ·
                      refine ⟨3079633088102277736967711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32849419606424295860988917 3079633088102277736967711)
                      ·
                        rfl

theorem cell23_5997564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_5997564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997564 prefixEnd_5997564 := by exact prefixLift 5997564
  have htrace : WordTrace (prefixWord ++ tailWord_5997564) baseStart_5997564 baseEnd_5997564 := by
    simpa [prefixWord, tailWord_5997564, baseEnd_5997564] using wordTrace_append hprefix tailTrace_5997564
  have hstable : (prefixWord ++ tailWord_5997564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997564).length < 2 ^ (prefixWord ++ tailWord_5997564).sum := by decide
  have hdescent : baseEnd_5997564 < baseStart_5997564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997578 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5997578 : Nat := 118140960795 + 5997578 * 2 ^ 59
def prefixEnd_5997578 : Nat := 4983230072969 + 3 ^ 40 * 5997578 * 2
def baseEnd_5997578 : Nat := 3079640276831440682192647

theorem tailTrace_5997578 : CollatzResearch.WordTrace tailWord_5997578 prefixEnd_5997578 3079640276831440682192647 := by
  unfold tailWord_5997578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54687410166451671404610347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145833093777204457078960925 54687410166451671404610347)
  ·
    refine ⟨82031115249677507106915521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54687410166451671404610347 82031115249677507106915521)
    ·
      refine ⟨61523336437258130330186641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82031115249677507106915521 61523336437258130330186641)
      ·
        refine ⟨46142502327943597747639981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61523336437258130330186641 46142502327943597747639981)
        ·
          refine ⟨17303438372978849155364993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46142502327943597747639981 17303438372978849155364993)
          ·
            refine ⟨12977578779734136866523745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303438372978849155364993 12977578779734136866523745)
            ·
              refine ⟨9733184084800602649892809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12977578779734136866523745 9733184084800602649892809)
              ·
                refine ⟨7299888063600451987419607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9733184084800602649892809 7299888063600451987419607)
                ·
                  refine ⟨10949832095400677981129411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7299888063600451987419607 10949832095400677981129411)
                  ·
                    refine ⟨16424748143101016971694117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10949832095400677981129411 16424748143101016971694117)
                    ·
                      refine ⟨3079640276831440682192647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16424748143101016971694117 3079640276831440682192647)
                      ·
                        rfl

theorem cell23_5997578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5997578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997578 prefixEnd_5997578 := by exact prefixLift 5997578
  have htrace : WordTrace (prefixWord ++ tailWord_5997578) baseStart_5997578 baseEnd_5997578 := by
    simpa [prefixWord, tailWord_5997578, baseEnd_5997578] using wordTrace_append hprefix tailTrace_5997578
  have hstable : (prefixWord ++ tailWord_5997578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997578).length < 2 ^ (prefixWord ++ tailWord_5997578).sum := by decide
  have hdescent : baseEnd_5997578 < baseStart_5997578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997611 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 3]
def baseStart_5997611 : Nat := 118140960795 + 5997611 * 2 ^ 59
def prefixEnd_5997611 : Nat := 4983230072969 + 3 ^ 40 * 5997611 * 2
def baseEnd_5997611 : Nat := 3079657221693039053079995

theorem tailTrace_5997611 : CollatzResearch.WordTrace tailWord_5997611 prefixEnd_5997611 3079657221693039053079995 := by
  unfold tailWord_5997611
  simp only [CollatzResearch.WordTrace]
  refine ⟨218750844274687132254392687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145833896183124754836261791 218750844274687132254392687)
  ·
    refine ⟨328126266412030698381589031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218750844274687132254392687 328126266412030698381589031)
    ·
      refine ⟨492189399618046047572383547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328126266412030698381589031 492189399618046047572383547)
      ·
        refine ⟨738284099427069071358575321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492189399618046047572383547 738284099427069071358575321)
        ·
          refine ⟨553713074570301803518931491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738284099427069071358575321 553713074570301803518931491)
          ·
            refine ⟨830569611855452705278397237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553713074570301803518931491 830569611855452705278397237)
            ·
              refine ⟨77865901111448691119849741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 830569611855452705278397237 77865901111448691119849741)
              ·
                refine ⟨29199712916793259169943653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77865901111448691119849741 29199712916793259169943653)
                ·
                  refine ⟨5474946171898736094364435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29199712916793259169943653 5474946171898736094364435)
                  ·
                    refine ⟨8212419257848104141546653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5474946171898736094364435 8212419257848104141546653)
                    ·
                      refine ⟨3079657221693039053079995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8212419257848104141546653 3079657221693039053079995)
                      ·
                        rfl

theorem cell23_5997611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 3].length) (baseStart_5997611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997611 prefixEnd_5997611 := by exact prefixLift 5997611
  have htrace : WordTrace (prefixWord ++ tailWord_5997611) baseStart_5997611 baseEnd_5997611 := by
    simpa [prefixWord, tailWord_5997611, baseEnd_5997611] using wordTrace_append hprefix tailTrace_5997611
  have hstable : (prefixWord ++ tailWord_5997611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997611).length < 2 ^ (prefixWord ++ tailWord_5997611).sum := by decide
  have hdescent : baseEnd_5997611 < baseStart_5997611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997612 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_5997612 : Nat := 118140960795 + 5997612 * 2 ^ 59
def prefixEnd_5997612 : Nat := 4983230072969 + 3 ^ 40 * 5997612 * 2
def baseEnd_5997612 : Nat := 3079657735173693549167491

theorem tailTrace_5997612 : CollatzResearch.WordTrace tailWord_5997612 prefixEnd_5997612 3079657735173693549167491 := by
  unfold tailWord_5997612
  simp only [CollatzResearch.WordTrace]
  refine ⟨109375440373841754712589545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145833920498455672950119393 109375440373841754712589545)
  ·
    refine ⟨82031580280381316034442159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109375440373841754712589545 82031580280381316034442159)
    ·
      refine ⟨123047370420571974051663239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82031580280381316034442159 123047370420571974051663239)
      ·
        refine ⟨184571055630857961077494859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123047370420571974051663239 184571055630857961077494859)
        ·
          refine ⟨276856583446286941616242289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184571055630857961077494859 276856583446286941616242289)
          ·
            refine ⟨207642437584715206212181717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276856583446286941616242289 207642437584715206212181717)
            ·
              refine ⟨4866619630891762645598009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207642437584715206212181717 4866619630891762645598009)
              ·
                refine ⟨3649964723168821984198507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4866619630891762645598009 3649964723168821984198507)
                ·
                  refine ⟨5474947084753232976297761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649964723168821984198507 5474947084753232976297761)
                  ·
                    refine ⟨4106210313564924732223321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474947084753232976297761 4106210313564924732223321)
                    ·
                      refine ⟨3079657735173693549167491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106210313564924732223321 3079657735173693549167491)
                      ·
                        rfl

theorem cell23_5997612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_5997612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997612 prefixEnd_5997612 := by exact prefixLift 5997612
  have htrace : WordTrace (prefixWord ++ tailWord_5997612) baseStart_5997612 baseEnd_5997612 := by
    simpa [prefixWord, tailWord_5997612, baseEnd_5997612] using wordTrace_append hprefix tailTrace_5997612
  have hstable : (prefixWord ++ tailWord_5997612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997612).length < 2 ^ (prefixWord ++ tailWord_5997612).sum := by decide
  have hdescent : baseEnd_5997612 < baseStart_5997612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997621 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_5997621 : Nat := 118140960795 + 5997621 * 2 ^ 59
def prefixEnd_5997621 : Nat := 4983230072969 + 3 ^ 40 * 5997621 * 2
def baseEnd_5997621 : Nat := 3079662356499584013954949

theorem tailTrace_5997621 : CollatzResearch.WordTrace tailWord_5997621 prefixEnd_5997621 3079662356499584013954949 := by
  unfold tailWord_5997621
  simp only [CollatzResearch.WordTrace]
  refine ⟨218751209004650903962256717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145834139336433935974837811 218751209004650903962256717)
  ·
    refine ⟨82031703376744088985846269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218751209004650903962256717 82031703376744088985846269)
    ·
      refine ⟨30761888766279033369692351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82031703376744088985846269 30761888766279033369692351)
      ·
        refine ⟨46142833149418550054538527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30761888766279033369692351 46142833149418550054538527)
        ·
          refine ⟨69214249724127825081807791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46142833149418550054538527 69214249724127825081807791)
          ·
            refine ⟨103821374586191737622711687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69214249724127825081807791 103821374586191737622711687)
            ·
              refine ⟨155732061879287606434067531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103821374586191737622711687 155732061879287606434067531)
              ·
                refine ⟨233598092818931409651101297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155732061879287606434067531 233598092818931409651101297)
                ·
                  refine ⟨175198569614198557238325973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233598092818931409651101297 175198569614198557238325973)
                  ·
                    refine ⟨4106216475332778685273265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175198569614198557238325973 4106216475332778685273265)
                    ·
                      refine ⟨3079662356499584013954949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106216475332778685273265 3079662356499584013954949)
                      ·
                        rfl

theorem cell23_5997621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_5997621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997621 prefixEnd_5997621 := by exact prefixLift 5997621
  have htrace : WordTrace (prefixWord ++ tailWord_5997621) baseStart_5997621 baseEnd_5997621 := by
    simpa [prefixWord, tailWord_5997621, baseEnd_5997621] using wordTrace_append hprefix tailTrace_5997621
  have hstable : (prefixWord ++ tailWord_5997621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997621).length < 2 ^ (prefixWord ++ tailWord_5997621).sum := by decide
  have hdescent : baseEnd_5997621 < baseStart_5997621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997622 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5997622 : Nat := 118140960795 + 5997622 * 2 ^ 59
def prefixEnd_5997622 : Nat := 4983230072969 + 3 ^ 40 * 5997622 * 2
def baseEnd_5997622 : Nat := 1026554289993412836680815

theorem tailTrace_5997622 : CollatzResearch.WordTrace tailWord_5997622 prefixEnd_5997622 1026554289993412836680815 := by
  unfold tailWord_5997622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671952842352955070815195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145834163651764854088695413 13671952842352955070815195)
  ·
    refine ⟨20507929263529432606222793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13671952842352955070815195 20507929263529432606222793)
    ·
      refine ⟨15380946947647074454667095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20507929263529432606222793 15380946947647074454667095)
      ·
        refine ⟨23071420421470611682000643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15380946947647074454667095 23071420421470611682000643)
        ·
          refine ⟨34607130632205917523000965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23071420421470611682000643 34607130632205917523000965)
          ·
            refine ⟨6488836993538609535562681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34607130632205917523000965 6488836993538609535562681)
            ·
              refine ⟨4866627745153957151672011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6488836993538609535562681 4866627745153957151672011)
              ·
                refine ⟨7299941617730935727508017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866627745153957151672011 7299941617730935727508017)
                ·
                  refine ⟨5474956213298201795631013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299941617730935727508017 5474956213298201795631013)
                  ·
                    refine ⟨1026554289993412836680815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474956213298201795631013 1026554289993412836680815)
                    ·
                      rfl

theorem cell23_5997622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5997622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997622 prefixEnd_5997622 := by exact prefixLift 5997622
  have htrace : WordTrace (prefixWord ++ tailWord_5997622) baseStart_5997622 baseEnd_5997622 := by
    simpa [prefixWord, tailWord_5997622, baseEnd_5997622] using wordTrace_append hprefix tailTrace_5997622
  have hstable : (prefixWord ++ tailWord_5997622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997622).length < 2 ^ (prefixWord ++ tailWord_5997622).sum := by decide
  have hdescent : baseEnd_5997622 < baseStart_5997622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997644 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_5997644 : Nat := 118140960795 + 5997644 * 2 ^ 59
def prefixEnd_5997644 : Nat := 4983230072969 + 3 ^ 40 * 5997644 * 2
def baseEnd_5997644 : Nat := 1026558055518212474655781

theorem tailTrace_5997644 : CollatzResearch.WordTrace tailWord_5997644 prefixEnd_5997644 1026558055518212474655781 := by
  unfold tailWord_5997644
  simp only [CollatzResearch.WordTrace]
  refine ⟨109376023941783789445171993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145834698589045052593562657 109376023941783789445171993)
  ·
    refine ⟨82032017956337842083878995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109376023941783789445171993 82032017956337842083878995)
    ·
      refine ⟨123048026934506763125818493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82032017956337842083878995 123048026934506763125818493)
      ·
        refine ⟨46143010100440036172181935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123048026934506763125818493 46143010100440036172181935)
        ·
          refine ⟨69214515150660054258272903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46143010100440036172181935 69214515150660054258272903)
          ·
            refine ⟨103821772725990081387409355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69214515150660054258272903 103821772725990081387409355)
            ·
              refine ⟨155732659088985122081114033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103821772725990081387409355 155732659088985122081114033)
              ·
                refine ⟨116799494316738841560835525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155732659088985122081114033 116799494316738841560835525)
                ·
                  refine ⟨21899905184388532792656661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116799494316738841560835525 21899905184388532792656661)
                  ·
                    refine ⟨1026558055518212474655781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21899905184388532792656661 1026558055518212474655781)
                    ·
                      rfl

theorem cell23_5997644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_5997644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997644 prefixEnd_5997644 := by exact prefixLift 5997644
  have htrace : WordTrace (prefixWord ++ tailWord_5997644) baseStart_5997644 baseEnd_5997644 := by
    simpa [prefixWord, tailWord_5997644, baseEnd_5997644] using wordTrace_append hprefix tailTrace_5997644
  have hstable : (prefixWord ++ tailWord_5997644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997644).length < 2 ^ (prefixWord ++ tailWord_5997644).sum := by decide
  have hdescent : baseEnd_5997644 < baseStart_5997644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997651 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 4, 2]
def baseStart_5997651 : Nat := 118140960795 + 5997651 * 2 ^ 59
def prefixEnd_5997651 : Nat := 4983230072969 + 3 ^ 40 * 5997651 * 2
def baseEnd_5997651 : Nat := 3079677760919218896579811

theorem tailTrace_5997651 : CollatzResearch.WordTrace tailWord_5997651 prefixEnd_5997651 3079677760919218896579811 := by
  unfold tailWord_5997651
  simp only [CollatzResearch.WordTrace]
  refine ⟨218752303194542219085848807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145834868796361479390565871 218752303194542219085848807)
  ·
    refine ⟨328128454791813328628773211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218752303194542219085848807 328128454791813328628773211)
    ·
      refine ⟨492192682187719992943159817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328128454791813328628773211 492192682187719992943159817)
      ·
        refine ⟨369144511640789994707369863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492192682187719992943159817 369144511640789994707369863)
        ·
          refine ⟨553716767461184992061054795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369144511640789994707369863 553716767461184992061054795)
          ·
            refine ⟨830575151191777488091582193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553716767461184992061054795 830575151191777488091582193)
            ·
              refine ⟨622931363393833116068686645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830575151191777488091582193 622931363393833116068686645)
              ·
                refine ⟨58399815318171854631439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 622931363393833116068686645 58399815318171854631439373)
                ·
                  refine ⟨21899930744314445486789765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58399815318171854631439373 21899930744314445486789765)
                  ·
                    refine ⟨4106237014558958528773081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21899930744314445486789765 4106237014558958528773081)
                    ·
                      refine ⟨3079677760919218896579811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106237014558958528773081 3079677760919218896579811)
                      ·
                        rfl

theorem cell23_5997651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4, 2].length) (baseStart_5997651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997651 prefixEnd_5997651 := by exact prefixLift 5997651
  have htrace : WordTrace (prefixWord ++ tailWord_5997651) baseStart_5997651 baseEnd_5997651 := by
    simpa [prefixWord, tailWord_5997651, baseEnd_5997651] using wordTrace_append hprefix tailTrace_5997651
  have hstable : (prefixWord ++ tailWord_5997651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997651).length < 2 ^ (prefixWord ++ tailWord_5997651).sum := by decide
  have hdescent : baseEnd_5997651 < baseStart_5997651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997671 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_5997671 : Nat := 118140960795 + 5997671 * 2 ^ 59
def prefixEnd_5997671 : Nat := 4983230072969 + 3 ^ 40 * 5997671 * 2
def baseEnd_5997671 : Nat := 3079688030532308818329719

theorem tailTrace_5997671 : CollatzResearch.WordTrace tailWord_5997671 prefixEnd_5997671 3079688030532308818329719 := by
  unfold tailWord_5997671
  simp only [CollatzResearch.WordTrace]
  refine ⟨218753032654469762501576867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145835355102979841667717911 218753032654469762501576867)
  ·
    refine ⟨328129548981704643752365301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218753032654469762501576867 328129548981704643752365301)
    ·
      refine ⟨30762145217034810351784247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328129548981704643752365301 30762145217034810351784247)
      ·
        refine ⟨46143217825552215527676371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30762145217034810351784247 46143217825552215527676371)
        ·
          refine ⟨69214826738328323291514557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46143217825552215527676371 69214826738328323291514557)
          ·
            refine ⟨25955560026873121234317959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69214826738328323291514557 25955560026873121234317959)
            ·
              refine ⟨38933340040309681851476939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25955560026873121234317959 38933340040309681851476939)
              ·
                refine ⟨58400010060464522777215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38933340040309681851476939 58400010060464522777215409)
                ·
                  refine ⟨43800007545348392082911557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58400010060464522777215409 43800007545348392082911557)
                  ·
                    refine ⟨8212501414752823515545917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43800007545348392082911557 8212501414752823515545917)
                    ·
                      refine ⟨3079688030532308818329719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8212501414752823515545917 3079688030532308818329719)
                      ·
                        rfl

theorem cell23_5997671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_5997671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997671 prefixEnd_5997671 := by exact prefixLift 5997671
  have htrace : WordTrace (prefixWord ++ tailWord_5997671) baseStart_5997671 baseEnd_5997671 := by
    simpa [prefixWord, tailWord_5997671, baseEnd_5997671] using wordTrace_append hprefix tailTrace_5997671
  have hstable : (prefixWord ++ tailWord_5997671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997671).length < 2 ^ (prefixWord ++ tailWord_5997671).sum := by decide
  have hdescent : baseEnd_5997671 < baseStart_5997671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997738 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5997738 : Nat := 118140960795 + 5997738 * 2 ^ 59
def prefixEnd_5997738 : Nat := 4983230072969 + 3 ^ 40 * 5997738 * 2
def baseEnd_5997738 : Nat := 1026574144578720018730637

theorem tailTrace_5997738 : CollatzResearch.WordTrace tailWord_5997738 prefixEnd_5997738 1026574144578720018730637 := by
  unfold tailWord_5997738
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688869086306758236066467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145836984230151355296177245 54688869086306758236066467)
  ·
    refine ⟨82033303629460137354099701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54688869086306758236066467 82033303629460137354099701)
    ·
      refine ⟨7690622215261887876946847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82033303629460137354099701 7690622215261887876946847)
      ·
        refine ⟨11535933322892831815420271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690622215261887876946847 11535933322892831815420271)
        ·
          refine ⟨17303899984339247723130407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535933322892831815420271 17303899984339247723130407)
          ·
            refine ⟨25955849976508871584695611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17303899984339247723130407 25955849976508871584695611)
            ·
              refine ⟨38933774964763307377043417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25955849976508871584695611 38933774964763307377043417)
              ·
                refine ⟨29200331223572480532782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38933774964763307377043417 29200331223572480532782563)
                ·
                  refine ⟨43800496835358720799173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29200331223572480532782563 43800496835358720799173845)
                  ·
                    refine ⟨1026574144578720018730637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43800496835358720799173845 1026574144578720018730637)
                    ·
                      rfl

theorem cell23_5997738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5997738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997738 prefixEnd_5997738 := by exact prefixLift 5997738
  have htrace : WordTrace (prefixWord ++ tailWord_5997738) baseStart_5997738 baseEnd_5997738 := by
    simpa [prefixWord, tailWord_5997738, baseEnd_5997738] using wordTrace_append hprefix tailTrace_5997738
  have hstable : (prefixWord ++ tailWord_5997738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997738).length < 2 ^ (prefixWord ++ tailWord_5997738).sum := by decide
  have hdescent : baseEnd_5997738 < baseStart_5997738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997758 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5997758 : Nat := 118140960795 + 5997758 * 2 ^ 59
def prefixEnd_5997758 : Nat := 4983230072969 + 3 ^ 40 * 5997758 * 2
def baseEnd_5997758 : Nat := 3079732703349249977941819

theorem tailTrace_5997758 : CollatzResearch.WordTrace tailWord_5997758 prefixEnd_5997758 3079732703349249977941819 := by
  unfold tailWord_5997758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344525725644322044999241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145837470536769717573329285 27344525725644322044999241)
  ·
    refine ⟨20508394294233241533749431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27344525725644322044999241 20508394294233241533749431)
    ·
      refine ⟨30762591441349862300624147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20508394294233241533749431 30762591441349862300624147)
      ·
        refine ⟨46143887162024793450936221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30762591441349862300624147 46143887162024793450936221)
        ·
          refine ⟨17303957685759297544101083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46143887162024793450936221 17303957685759297544101083)
          ·
            refine ⟨25955936528638946316151625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17303957685759297544101083 25955936528638946316151625)
            ·
              refine ⟨19466952396479209737113719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25955936528638946316151625 19466952396479209737113719)
              ·
                refine ⟨29200428594718814605670579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19466952396479209737113719 29200428594718814605670579)
                ·
                  refine ⟨43800642892078221908505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29200428594718814605670579 43800642892078221908505869)
                  ·
                    refine ⟨16425241084529333215689701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43800642892078221908505869 16425241084529333215689701)
                    ·
                      refine ⟨3079732703349249977941819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16425241084529333215689701 3079732703349249977941819)
                      ·
                        rfl

theorem cell23_5997758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5997758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997758 prefixEnd_5997758 := by exact prefixLift 5997758
  have htrace : WordTrace (prefixWord ++ tailWord_5997758) baseStart_5997758 baseEnd_5997758 := by
    simpa [prefixWord, tailWord_5997758, baseEnd_5997758] using wordTrace_append hprefix tailTrace_5997758
  have hstable : (prefixWord ++ tailWord_5997758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997758).length < 2 ^ (prefixWord ++ tailWord_5997758).sum := by decide
  have hdescent : baseEnd_5997758 < baseStart_5997758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997835 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 2, 3, 2]
def baseStart_5997835 : Nat := 118140960795 + 5997835 * 2 ^ 59
def prefixEnd_5997835 : Nat := 4983230072969 + 3 ^ 40 * 5997835 * 2
def baseEnd_5997835 : Nat := 3079772241359646176678965

theorem tailTrace_5997835 : CollatzResearch.WordTrace tailWord_5997835 prefixEnd_5997835 3079772241359646176678965 := by
  unfold tailWord_5997835
  simp only [CollatzResearch.WordTrace]
  refine ⟨218759014225875618510546959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145839342817250412340364639 218759014225875618510546959)
  ·
    refine ⟨328138521338813427765820439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218759014225875618510546959 328138521338813427765820439)
    ·
      refine ⟨492207782008220141648730659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328138521338813427765820439 492207782008220141648730659)
      ·
        refine ⟨738311673012330212473095989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492207782008220141648730659 738311673012330212473095989)
        ·
          refine ⟨69216719344905957419352749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 738311673012330212473095989 69216719344905957419352749)
          ·
            refine ⟨25956269754339734032257281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69216719344905957419352749 25956269754339734032257281)
            ·
              refine ⟨19467202315754800524192961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25956269754339734032257281 19467202315754800524192961)
              ·
                refine ⟨14600401736816100393144721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19467202315754800524192961 14600401736816100393144721)
                ·
                  refine ⟨10950301302612075294858541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14600401736816100393144721 10950301302612075294858541)
                  ·
                    refine ⟨4106362988479528235571953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10950301302612075294858541 4106362988479528235571953)
                    ·
                      refine ⟨3079772241359646176678965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106362988479528235571953 3079772241359646176678965)
                      ·
                        rfl

theorem cell23_5997835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3, 2].length) (baseStart_5997835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997835 prefixEnd_5997835 := by exact prefixLift 5997835
  have htrace : WordTrace (prefixWord ++ tailWord_5997835) baseStart_5997835 baseEnd_5997835 := by
    simpa [prefixWord, tailWord_5997835, baseEnd_5997835] using wordTrace_append hprefix tailTrace_5997835
  have hstable : (prefixWord ++ tailWord_5997835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997835).length < 2 ^ (prefixWord ++ tailWord_5997835).sum := by decide
  have hdescent : baseEnd_5997835 < baseStart_5997835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997841 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_5997841 : Nat := 118140960795 + 5997841 * 2 ^ 59
def prefixEnd_5997841 : Nat := 4983230072969 + 3 ^ 40 * 5997841 * 2
def baseEnd_5997841 : Nat := 1026591774081191051067979

theorem tailTrace_5997841 : CollatzResearch.WordTrace tailWord_5997841 prefixEnd_5997841 1026591774081191051067979 := by
  unfold tailWord_5997841
  simp only [CollatzResearch.WordTrace]
  refine ⟨218759233063853881535265377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145839488709235921023510251 218759233063853881535265377)
  ·
    refine ⟨164069424797890411151449033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218759233063853881535265377 164069424797890411151449033)
    ·
      refine ⟨123052068598417808363586775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164069424797890411151449033 123052068598417808363586775)
      ·
        refine ⟨184578102897626712545380163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123052068598417808363586775 184578102897626712545380163)
        ·
          refine ⟨276867154346440068818070245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184578102897626712545380163 276867154346440068818070245)
          ·
            refine ⟨51912591439957512903388171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276867154346440068818070245 51912591439957512903388171)
            ·
              refine ⟨77868887159936269355082257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51912591439957512903388171 77868887159936269355082257)
              ·
                refine ⟨58401665369952202016311693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77868887159936269355082257 58401665369952202016311693)
                ·
                  refine ⟨21900624513732075756116885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58401665369952202016311693 21900624513732075756116885)
                  ·
                    refine ⟨1026591774081191051067979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21900624513732075756116885 1026591774081191051067979)
                    ·
                      rfl

theorem cell23_5997841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_5997841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997841 prefixEnd_5997841 := by exact prefixLift 5997841
  have htrace : WordTrace (prefixWord ++ tailWord_5997841) baseStart_5997841 baseEnd_5997841 := by
    simpa [prefixWord, tailWord_5997841, baseEnd_5997841] using wordTrace_append hprefix tailTrace_5997841
  have hstable : (prefixWord ++ tailWord_5997841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997841).length < 2 ^ (prefixWord ++ tailWord_5997841).sum := by decide
  have hdescent : baseEnd_5997841 < baseStart_5997841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997848 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5997848 : Nat := 118140960795 + 5997848 * 2 ^ 59
def prefixEnd_5997848 : Nat := 4983230072969 + 3 ^ 40 * 5997848 * 2
def baseEnd_5997848 : Nat := 3079778916608154625816405

theorem tailTrace_5997848 : CollatzResearch.WordTrace tailWord_5997848 prefixEnd_5997848 3079778916608154625816405 := by
  unfold tailWord_5997848
  simp only [CollatzResearch.WordTrace]
  refine ⟨109379744187414260865385099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145839658916552347820513465 109379744187414260865385099)
  ·
    refine ⟨164069616281121391298077649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109379744187414260865385099 164069616281121391298077649)
    ·
      refine ⟨123052212210841043473558237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164069616281121391298077649 123052212210841043473558237)
      ·
        refine ⟨46144579579065391302584339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123052212210841043473558237 46144579579065391302584339)
        ·
          refine ⟨69216869368598086953876509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46144579579065391302584339 69216869368598086953876509)
          ·
            refine ⟨25956326013224282607703691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69216869368598086953876509 25956326013224282607703691)
            ·
              refine ⟨38934489019836423911555537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25956326013224282607703691 38934489019836423911555537)
              ·
                refine ⟨29200866764877317933666653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38934489019836423911555537 29200866764877317933666653)
                ·
                  refine ⟨10950325036828994225124995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29200866764877317933666653 10950325036828994225124995)
                  ·
                    refine ⟨16425487555243491337687493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10950325036828994225124995 16425487555243491337687493)
                    ·
                      refine ⟨3079778916608154625816405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16425487555243491337687493 3079778916608154625816405)
                      ·
                        rfl

theorem cell23_5997848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5997848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997848 prefixEnd_5997848 := by exact prefixLift 5997848
  have htrace : WordTrace (prefixWord ++ tailWord_5997848) baseStart_5997848 baseEnd_5997848 := by
    simpa [prefixWord, tailWord_5997848, baseEnd_5997848] using wordTrace_append hprefix tailTrace_5997848
  have hstable : (prefixWord ++ tailWord_5997848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997848).length < 2 ^ (prefixWord ++ tailWord_5997848).sum := by decide
  have hdescent : baseEnd_5997848 < baseStart_5997848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997851 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_5997851 : Nat := 118140960795 + 5997851 * 2 ^ 59
def prefixEnd_5997851 : Nat := 4983230072969 + 3 ^ 40 * 5997851 * 2
def baseEnd_5997851 : Nat := 3079780457050118114078891

theorem tailTrace_5997851 : CollatzResearch.WordTrace tailWord_5997851 prefixEnd_5997851 3079780457050118114078891 := by
  unfold tailWord_5997851
  simp only [CollatzResearch.WordTrace]
  refine ⟨218759597793817653243129407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145839731862545102162086271 218759597793817653243129407)
  ·
    refine ⟨328139396690726479864694111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218759597793817653243129407 328139396690726479864694111)
    ·
      refine ⟨492209095036089719797041167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328139396690726479864694111 492209095036089719797041167)
      ·
        refine ⟨738313642554134579695561751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492209095036089719797041167 738313642554134579695561751)
        ·
          refine ⟨1107470463831201869543342627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738313642554134579695561751 1107470463831201869543342627)
          ·
            refine ⟨1661205695746802804315013941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107470463831201869543342627 1661205695746802804315013941)
            ·
              refine ⟨155738033976262762904532557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1661205695746802804315013941 155738033976262762904532557)
              ·
                refine ⟨58401762741098536089199709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155738033976262762904532557 58401762741098536089199709)
                ·
                  refine ⟨21900661027911951033449891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58401762741098536089199709 21900661027911951033449891)
                  ·
                    refine ⟨32850991541867926550174837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21900661027911951033449891 32850991541867926550174837)
                    ·
                      refine ⟨3079780457050118114078891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32850991541867926550174837 3079780457050118114078891)
                      ·
                        rfl

theorem cell23_5997851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_5997851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997851 prefixEnd_5997851 := by exact prefixLift 5997851
  have htrace : WordTrace (prefixWord ++ tailWord_5997851) baseStart_5997851 baseEnd_5997851 := by
    simpa [prefixWord, tailWord_5997851, baseEnd_5997851] using wordTrace_append hprefix tailTrace_5997851
  have hstable : (prefixWord ++ tailWord_5997851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997851).length < 2 ^ (prefixWord ++ tailWord_5997851).sum := by decide
  have hdescent : baseEnd_5997851 < baseStart_5997851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997869 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5997869 : Nat := 118140960795 + 5997869 * 2 ^ 59
def prefixEnd_5997869 : Nat := 4983230072969 + 3 ^ 40 * 5997869 * 2
def baseEnd_5997869 : Nat := 3079789699701899043653809

theorem tailTrace_5997869 : CollatzResearch.WordTrace tailWord_5997869 prefixEnd_5997869 3079789699701899043653809 := by
  unfold tailWord_5997869
  simp only [CollatzResearch.WordTrace]
  refine ⟨218760254307752442317284661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145840169538501628211523107 218760254307752442317284661)
  ·
    refine ⟨20508773841351791467245437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218760254307752442317284661 20508773841351791467245437)
    ·
      refine ⟨7690790190506921800217039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20508773841351791467245437 7690790190506921800217039)
      ·
        refine ⟨11536185285760382700325559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690790190506921800217039 11536185285760382700325559)
        ·
          refine ⟨17304277928640574050488339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536185285760382700325559 17304277928640574050488339)
          ·
            refine ⟨25956416892960861075732509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17304277928640574050488339 25956416892960861075732509)
            ·
              refine ⟨9733656334860322903399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25956416892960861075732509 9733656334860322903399691)
              ·
                refine ⟨14600484502290484355099537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733656334860322903399691 14600484502290484355099537)
                ·
                  refine ⟨10950363376717863266324653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14600484502290484355099537 10950363376717863266324653)
                  ·
                    refine ⟨4106386266269198724871745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10950363376717863266324653 4106386266269198724871745)
                    ·
                      refine ⟨3079789699701899043653809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106386266269198724871745 3079789699701899043653809)
                      ·
                        rfl

theorem cell23_5997869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5997869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997869 prefixEnd_5997869 := by exact prefixLift 5997869
  have htrace : WordTrace (prefixWord ++ tailWord_5997869) baseStart_5997869 baseEnd_5997869 := by
    simpa [prefixWord, tailWord_5997869, baseEnd_5997869] using wordTrace_append hprefix tailTrace_5997869
  have hstable : (prefixWord ++ tailWord_5997869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997869).length < 2 ^ (prefixWord ++ tailWord_5997869).sum := by decide
  have hdescent : baseEnd_5997869 < baseStart_5997869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997891 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_5997891 : Nat := 118140960795 + 5997891 * 2 ^ 59
def prefixEnd_5997891 : Nat := 4983230072969 + 3 ^ 40 * 5997891 * 2
def baseEnd_5997891 : Nat := 3079800996276297957578707

theorem tailTrace_5997891 : CollatzResearch.WordTrace tailWord_5997891 prefixEnd_5997891 3079800996276297957578707 := by
  unfold tailWord_5997891
  simp only [CollatzResearch.WordTrace]
  refine ⟨218761056713672740074585527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145840704475781826716390351 218761056713672740074585527)
  ·
    refine ⟨328141585070509110111878291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218761056713672740074585527 328141585070509110111878291)
    ·
      refine ⟨492212377605763665167817437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328141585070509110111878291 492212377605763665167817437)
      ·
        refine ⟨184579641602161374437931539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492212377605763665167817437 184579641602161374437931539)
        ·
          refine ⟨276869462403242061656897309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184579641602161374437931539 276869462403242061656897309)
          ·
            refine ⟨103826048401215773121336491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276869462403242061656897309 103826048401215773121336491)
            ·
              refine ⟨155739072601823659682004737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103826048401215773121336491 155739072601823659682004737)
              ·
                refine ⟨116804304451367744761503553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155739072601823659682004737 116804304451367744761503553)
                ·
                  refine ⟨87603228338525808571127665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116804304451367744761503553 87603228338525808571127665)
                  ·
                    refine ⟨65702421253894356428345749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87603228338525808571127665 65702421253894356428345749)
                    ·
                      refine ⟨3079800996276297957578707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65702421253894356428345749 3079800996276297957578707)
                      ·
                        rfl

theorem cell23_5997891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_5997891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997891 prefixEnd_5997891 := by exact prefixLift 5997891
  have htrace : WordTrace (prefixWord ++ tailWord_5997891) baseStart_5997891 baseEnd_5997891 := by
    simpa [prefixWord, tailWord_5997891, baseEnd_5997891] using wordTrace_append hprefix tailTrace_5997891
  have hstable : (prefixWord ++ tailWord_5997891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997891).length < 2 ^ (prefixWord ++ tailWord_5997891).sum := by decide
  have hdescent : baseEnd_5997891 < baseStart_5997891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997892 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5997892 : Nat := 118140960795 + 5997892 * 2 ^ 59
def prefixEnd_5997892 : Nat := 4983230072969 + 3 ^ 40 * 5997892 * 2
def baseEnd_5997892 : Nat := 1026600503252317484555401

theorem tailTrace_5997892 : CollatzResearch.WordTrace tailWord_5997892 prefixEnd_5997892 1026600503252317484555401 := by
  unfold tailWord_5997892
  simp only [CollatzResearch.WordTrace]
  refine ⟨109380546593334558622685965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145840728791112744830247953 109380546593334558622685965)
  ·
    refine ⟨41017704972500459483507237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109380546593334558622685965 41017704972500459483507237)
    ·
      refine ⟨7690819682343836153157607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41017704972500459483507237 7690819682343836153157607)
      ·
        refine ⟨11536229523515754229736411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690819682343836153157607 11536229523515754229736411)
        ·
          refine ⟨17304344285273631344604617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536229523515754229736411 17304344285273631344604617)
          ·
            refine ⟨12978258213955223508453463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17304344285273631344604617 12978258213955223508453463)
            ·
              refine ⟨19467387320932835262680195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978258213955223508453463 19467387320932835262680195)
              ·
                refine ⟨29201080981399252894020293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19467387320932835262680195 29201080981399252894020293)
                ·
                  refine ⟨5475202684012359917628805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29201080981399252894020293 5475202684012359917628805)
                  ·
                    refine ⟨1026600503252317484555401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475202684012359917628805 1026600503252317484555401)
                    ·
                      rfl

theorem cell23_5997892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5997892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997892 prefixEnd_5997892 := by exact prefixLift 5997892
  have htrace : WordTrace (prefixWord ++ tailWord_5997892) baseStart_5997892 baseEnd_5997892 := by
    simpa [prefixWord, tailWord_5997892, baseEnd_5997892] using wordTrace_append hprefix tailTrace_5997892
  have hstable : (prefixWord ++ tailWord_5997892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997892).length < 2 ^ (prefixWord ++ tailWord_5997892).sum := by decide
  have hdescent : baseEnd_5997892 < baseStart_5997892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997898 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_5997898 : Nat := 118140960795 + 5997898 * 2 ^ 59
def prefixEnd_5997898 : Nat := 4983230072969 + 3 ^ 40 * 5997898 * 2
def baseEnd_5997898 : Nat := 3079804590640879430191175

theorem tailTrace_5997898 : CollatzResearch.WordTrace tailWord_5997898 prefixEnd_5997898 3079804590640879430191175 := by
  unfold tailWord_5997898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54690328006161845067522587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145840874683098253513393565 54690328006161845067522587)
  ·
    refine ⟨82035492009242767601283881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54690328006161845067522587 82035492009242767601283881)
    ·
      refine ⟨61526619006932075700962911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82035492009242767601283881 61526619006932075700962911)
      ·
        refine ⟨92289928510398113551444367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61526619006932075700962911 92289928510398113551444367)
        ·
          refine ⟨138434892765597170327166551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92289928510398113551444367 138434892765597170327166551)
          ·
            refine ⟨207652339148395755490749827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138434892765597170327166551 207652339148395755490749827)
            ·
              refine ⟨311478508722593633236124741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207652339148395755490749827 311478508722593633236124741)
              ·
                refine ⟨58402220385486306231773389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311478508722593633236124741 58402220385486306231773389)
                ·
                  refine ⟨21900832644557364836915021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58402220385486306231773389 21900832644557364836915021)
                  ·
                    refine ⟨8212812241709011813843133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21900832644557364836915021 8212812241709011813843133)
                    ·
                      refine ⟨3079804590640879430191175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8212812241709011813843133 3079804590640879430191175)
                      ·
                        rfl

theorem cell23_5997898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_5997898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997898 prefixEnd_5997898 := by exact prefixLift 5997898
  have htrace : WordTrace (prefixWord ++ tailWord_5997898) baseStart_5997898 baseEnd_5997898 := by
    simpa [prefixWord, tailWord_5997898, baseEnd_5997898] using wordTrace_append hprefix tailTrace_5997898
  have hstable : (prefixWord ++ tailWord_5997898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997898).length < 2 ^ (prefixWord ++ tailWord_5997898).sum := by decide
  have hdescent : baseEnd_5997898 < baseStart_5997898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997950 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5997950 : Nat := 118140960795 + 5997950 * 2 ^ 59
def prefixEnd_5997950 : Nat := 4983230072969 + 3 ^ 40 * 5997950 * 2
def baseEnd_5997950 : Nat := 3079831291634913226740937

theorem tailTrace_5997950 : CollatzResearch.WordTrace tailWord_5997950 prefixEnd_5997950 3079831291634913226740937 := by
  unfold tailWord_5997950
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345401077557374143872913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145842139080305995433988869 27345401077557374143872913)
  ·
    refine ⟨20509050808168030607904685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27345401077557374143872913 20509050808168030607904685)
    ·
      refine ⟨7690894053063011477964257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20509050808168030607904685 7690894053063011477964257)
      ·
        refine ⟨5768170539797258608473193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7690894053063011477964257 5768170539797258608473193)
        ·
          refine ⟨4326127904847943956354895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5768170539797258608473193 4326127904847943956354895)
          ·
            refine ⟨6489191857271915934532343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326127904847943956354895 6489191857271915934532343)
            ·
              refine ⟨9733787785907873901798515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489191857271915934532343 9733787785907873901798515)
              ·
                refine ⟨14600681678861810852697773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733787785907873901798515 14600681678861810852697773)
                ·
                  refine ⟨5475255629573179069761665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14600681678861810852697773 5475255629573179069761665)
                  ·
                    refine ⟨4106441722179884302321249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475255629573179069761665 4106441722179884302321249)
                    ·
                      refine ⟨3079831291634913226740937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106441722179884302321249 3079831291634913226740937)
                      ·
                        rfl

theorem cell23_5997950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5997950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997950 prefixEnd_5997950 := by exact prefixLift 5997950
  have htrace : WordTrace (prefixWord ++ tailWord_5997950) baseStart_5997950 baseEnd_5997950 := by
    simpa [prefixWord, tailWord_5997950, baseEnd_5997950] using wordTrace_append hprefix tailTrace_5997950
  have hstable : (prefixWord ++ tailWord_5997950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997950).length < 2 ^ (prefixWord ++ tailWord_5997950).sum := by decide
  have hdescent : baseEnd_5997950 < baseStart_5997950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997976 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5997976 : Nat := 118140960795 + 5997976 * 2 ^ 59
def prefixEnd_5997976 : Nat := 4983230072969 + 3 ^ 40 * 5997976 * 2
def baseEnd_5997976 : Nat := 3079844642131930125015817

theorem tailTrace_5997976 : CollatzResearch.WordTrace tailWord_5997976 prefixEnd_5997976 3079844642131930125015817 := by
  unfold tailWord_5997976
  simp only [CollatzResearch.WordTrace]
  refine ⟨109382078459182399795714891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145842771278909866394286521 109382078459182399795714891)
  ·
    refine ⟨164073117688773599693572337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109382078459182399795714891 164073117688773599693572337)
    ·
      refine ⟨123054838266580199770179253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164073117688773599693572337 123054838266580199770179253)
      ·
        refine ⟨11536391087491893728454305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123054838266580199770179253 11536391087491893728454305)
        ·
          refine ⟨8652293315618920296340729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11536391087491893728454305 8652293315618920296340729)
          ·
            refine ⟨6489219986714190222255547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8652293315618920296340729 6489219986714190222255547)
            ·
              refine ⟨9733829980071285333383321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489219986714190222255547 9733829980071285333383321)
              ·
                refine ⟨7300372485053464000037491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9733829980071285333383321 7300372485053464000037491)
                ·
                  refine ⟨10950558727580196000056237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7300372485053464000037491 10950558727580196000056237)
                  ·
                    refine ⟨4106459522842573500021089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10950558727580196000056237 4106459522842573500021089)
                    ·
                      refine ⟨3079844642131930125015817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106459522842573500021089 3079844642131930125015817)
                      ·
                        rfl

theorem cell23_5997976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5997976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997976 prefixEnd_5997976 := by exact prefixLift 5997976
  have htrace : WordTrace (prefixWord ++ tailWord_5997976) baseStart_5997976 baseEnd_5997976 := by
    simpa [prefixWord, tailWord_5997976, baseEnd_5997976] using wordTrace_append hprefix tailTrace_5997976
  have hstable : (prefixWord ++ tailWord_5997976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997976).length < 2 ^ (prefixWord ++ tailWord_5997976).sum := by decide
  have hdescent : baseEnd_5997976 < baseStart_5997976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5997978 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_5997978 : Nat := 118140960795 + 5997978 * 2 ^ 59
def prefixEnd_5997978 : Nat := 4983230072969 + 3 ^ 40 * 5997978 * 2
def baseEnd_5997978 : Nat := 342205074343693235243423

theorem tailTrace_5997978 : CollatzResearch.WordTrace tailWord_5997978 prefixEnd_5997978 342205074343693235243423 := by
  unfold tailWord_5997978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691057466089388483250647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145842819909571702622001725 54691057466089388483250647)
  ·
    refine ⟨82036586199134082724875971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54691057466089388483250647 82036586199134082724875971)
    ·
      refine ⟨123054879298701124087313957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82036586199134082724875971 123054879298701124087313957)
      ·
        refine ⟨23072789868506460766371367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123054879298701124087313957 23072789868506460766371367)
        ·
          refine ⟨34609184802759691149557051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23072789868506460766371367 34609184802759691149557051)
          ·
            refine ⟨51913777204139536724335577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34609184802759691149557051 51913777204139536724335577)
            ·
              refine ⟨38935332903104652543251683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51913777204139536724335577 38935332903104652543251683)
              ·
                refine ⟨58402999354656978814877525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38935332903104652543251683 58402999354656978814877525)
                ·
                  refine ⟨342205074343693235243423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58402999354656978814877525 342205074343693235243423)
                  ·
                    rfl

theorem cell23_5997978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_5997978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5997978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5997978 prefixEnd_5997978 := by exact prefixLift 5997978
  have htrace : WordTrace (prefixWord ++ tailWord_5997978) baseStart_5997978 baseEnd_5997978 := by
    simpa [prefixWord, tailWord_5997978, baseEnd_5997978] using wordTrace_append hprefix tailTrace_5997978
  have hstable : (prefixWord ++ tailWord_5997978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5997978).length < 2 ^ (prefixWord ++ tailWord_5997978).sum := by decide
  have hdescent : baseEnd_5997978 < baseStart_5997978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5997978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998042 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_5998042 : Nat := 118140960795 + 5998042 * 2 ^ 59
def prefixEnd_5998042 : Nat := 4983230072969 + 3 ^ 40 * 5998042 * 2
def baseEnd_5998042 : Nat := 1026626177285042288930171

theorem tailTrace_5998042 : CollatzResearch.WordTrace tailWord_5998042 prefixEnd_5998042 1026626177285042288930171 := by
  unfold tailWord_5998042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691641034031423215833095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145844376090750461908888253 54691641034031423215833095)
  ·
    refine ⟨82037461551047134823749643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54691641034031423215833095 82037461551047134823749643)
    ·
      refine ⟨123056192326570702235624465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82037461551047134823749643 123056192326570702235624465)
      ·
        refine ⟨92292144244928026676718349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123056192326570702235624465 92292144244928026676718349)
        ·
          refine ⟨34609554091848010003769381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92292144244928026676718349 34609554091848010003769381)
          ·
            refine ⟨6489291392221501875706759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34609554091848010003769381 6489291392221501875706759)
            ·
              refine ⟨9733937088332252813560139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489291392221501875706759 9733937088332252813560139)
              ·
                refine ⟨14600905632498379220340209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733937088332252813560139 14600905632498379220340209)
                ·
                  refine ⟨10950679224373784415255157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14600905632498379220340209 10950679224373784415255157)
                  ·
                    refine ⟨1026626177285042288930171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10950679224373784415255157 1026626177285042288930171)
                    ·
                      rfl

theorem cell23_5998042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_5998042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998042 prefixEnd_5998042 := by exact prefixLift 5998042
  have htrace : WordTrace (prefixWord ++ tailWord_5998042) baseStart_5998042 baseEnd_5998042 := by
    simpa [prefixWord, tailWord_5998042, baseEnd_5998042] using wordTrace_append hprefix tailTrace_5998042
  have hstable : (prefixWord ++ tailWord_5998042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998042).length < 2 ^ (prefixWord ++ tailWord_5998042).sum := by decide
  have hdescent : baseEnd_5998042 < baseStart_5998042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998048 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5998048 : Nat := 118140960795 + 5998048 * 2 ^ 59
def prefixEnd_5998048 : Nat := 4983230072969 + 3 ^ 40 * 5998048 * 2
def baseEnd_5998048 : Nat := 3079881612739053843315485

theorem tailTrace_5998048 : CollatzResearch.WordTrace tailWord_5998048 prefixEnd_5998048 3079881612739053843315485 := by
  unfold tailWord_5998048
  simp only [CollatzResearch.WordTrace]
  refine ⟨109383391487051977944025399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145844521982735970592033865 109383391487051977944025399)
  ·
    refine ⟨164075087230577966916038099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109383391487051977944025399 164075087230577966916038099)
    ·
      refine ⟨246112630845866950374057149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164075087230577966916038099 246112630845866950374057149)
      ·
        refine ⟨92292236567200106390271431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246112630845866950374057149 92292236567200106390271431)
        ·
          refine ⟨138438354850800159585407147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92292236567200106390271431 138438354850800159585407147)
          ·
            refine ⟨207657532276200239378110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138438354850800159585407147 207657532276200239378110721)
            ·
              refine ⟨155743149207150179533583041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207657532276200239378110721 155743149207150179533583041)
              ·
                refine ⟨116807361905362634650187281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155743149207150179533583041 116807361905362634650187281)
                ·
                  refine ⟨87605521429021975987640461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116807361905362634650187281 87605521429021975987640461)
                  ·
                    refine ⟨32852070535883240995365173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87605521429021975987640461 32852070535883240995365173)
                    ·
                      refine ⟨3079881612739053843315485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32852070535883240995365173 3079881612739053843315485)
                      ·
                        rfl

theorem cell23_5998048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5998048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998048 prefixEnd_5998048 := by exact prefixLift 5998048
  have htrace : WordTrace (prefixWord ++ tailWord_5998048) baseStart_5998048 baseEnd_5998048 := by
    simpa [prefixWord, tailWord_5998048, baseEnd_5998048] using wordTrace_append hprefix tailTrace_5998048
  have hstable : (prefixWord ++ tailWord_5998048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998048).length < 2 ^ (prefixWord ++ tailWord_5998048).sum := by decide
  have hdescent : baseEnd_5998048 < baseStart_5998048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998062 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_5998062 : Nat := 118140960795 + 5998062 * 2 ^ 59
def prefixEnd_5998062 : Nat := 4983230072969 + 3 ^ 40 * 5998062 * 2
def baseEnd_5998062 : Nat := 3079888801468216788540421

theorem tailTrace_5998062 : CollatzResearch.WordTrace tailWord_5998062 prefixEnd_5998062 3079888801468216788540421 := by
  unfold tailWord_5998062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345911699506654534882555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145844862397368824186040293 27345911699506654534882555)
  ·
    refine ⟨41018867549259981802323833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27345911699506654534882555 41018867549259981802323833)
    ·
      refine ⟨30764150661944986351742875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41018867549259981802323833 30764150661944986351742875)
      ·
        refine ⟨46146225992917479527614313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30764150661944986351742875 46146225992917479527614313)
        ·
          refine ⟨34609669494688109645710735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46146225992917479527614313 34609669494688109645710735)
          ·
            refine ⟨51914504242032164468566103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34609669494688109645710735 51914504242032164468566103)
            ·
              refine ⟨77871756363048246702849155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51914504242032164468566103 77871756363048246702849155)
              ·
                refine ⟨116807634544572370054273733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77871756363048246702849155 116807634544572370054273733)
                ·
                  refine ⟨21901431477107319385176325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116807634544572370054273733 21901431477107319385176325)
                  ·
                    refine ⟨4106518401957622384720561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21901431477107319385176325 4106518401957622384720561)
                    ·
                      refine ⟨3079888801468216788540421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106518401957622384720561 3079888801468216788540421)
                      ·
                        rfl

theorem cell23_5998062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_5998062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998062 prefixEnd_5998062 := by exact prefixLift 5998062
  have htrace : WordTrace (prefixWord ++ tailWord_5998062) baseStart_5998062 baseEnd_5998062 := by
    simpa [prefixWord, tailWord_5998062, baseEnd_5998062] using wordTrace_append hprefix tailTrace_5998062
  have hstable : (prefixWord ++ tailWord_5998062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998062).length < 2 ^ (prefixWord ++ tailWord_5998062).sum := by decide
  have hdescent : baseEnd_5998062 < baseStart_5998062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998072 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_5998072 : Nat := 118140960795 + 5998072 * 2 ^ 59
def prefixEnd_5998072 : Nat := 4983230072969 + 3 ^ 40 * 5998072 * 2
def baseEnd_5998072 : Nat := 1026631312091587249805125

theorem tailTrace_5998072 : CollatzResearch.WordTrace tailWord_5998072 prefixEnd_5998072 1026631312091587249805125 := by
  unfold tailWord_5998072
  simp only [CollatzResearch.WordTrace]
  refine ⟨109383829163008503993462235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145845105550678005324616313 109383829163008503993462235)
  ·
    refine ⟨164075743744512755990193353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109383829163008503993462235 164075743744512755990193353)
    ·
      refine ⟨123056807808384566992645015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164075743744512755990193353 123056807808384566992645015)
      ·
        refine ⟨184585211712576850488967523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123056807808384566992645015 184585211712576850488967523)
        ·
          refine ⟨276877817568865275733451285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184585211712576850488967523 276877817568865275733451285)
          ·
            refine ⟨12978647698540559800005529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276877817568865275733451285 12978647698540559800005529)
            ·
              refine ⟨9733985773905419850004147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12978647698540559800005529 9733985773905419850004147)
              ·
                refine ⟨14600978660858129775006221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733985773905419850004147 14600978660858129775006221)
                ·
                  refine ⟨5475366997821798665627333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14600978660858129775006221 5475366997821798665627333)
                  ·
                    refine ⟨1026631312091587249805125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475366997821798665627333 1026631312091587249805125)
                    ·
                      rfl

theorem cell23_5998072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_5998072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998072 prefixEnd_5998072 := by exact prefixLift 5998072
  have htrace : WordTrace (prefixWord ++ tailWord_5998072) baseStart_5998072 baseEnd_5998072 := by
    simpa [prefixWord, tailWord_5998072, baseEnd_5998072] using wordTrace_append hprefix tailTrace_5998072
  have hstable : (prefixWord ++ tailWord_5998072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998072).length < 2 ^ (prefixWord ++ tailWord_5998072).sum := by decide
  have hdescent : baseEnd_5998072 < baseStart_5998072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998162 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_5998162 : Nat := 118140960795 + 5998162 * 2 ^ 59
def prefixEnd_5998162 : Nat := 4983230072969 + 3 ^ 40 * 5998162 * 2
def baseEnd_5998162 : Nat := 1026646716511222132429987

theorem tailTrace_5998162 : CollatzResearch.WordTrace tailWord_5998162 prefixEnd_5998162 1026646716511222132429987 := by
  unfold tailWord_5998162
  simp only [CollatzResearch.WordTrace]
  refine ⟨54692735223922738339425185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145847293930460635571800493 54692735223922738339425185)
  ·
    refine ⟨41019551417942053754568889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54692735223922738339425185 41019551417942053754568889)
    ·
      refine ⟨30764663563456540315926667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41019551417942053754568889 30764663563456540315926667)
      ·
        refine ⟨46146995345184810473890001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30764663563456540315926667 46146995345184810473890001)
        ·
          refine ⟨34610246508888607855417501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46146995345184810473890001 34610246508888607855417501)
          ·
            refine ⟨12978842440833227945781563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34610246508888607855417501 12978842440833227945781563)
            ·
              refine ⟨19468263661249841918672345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978842440833227945781563 19468263661249841918672345)
              ·
                refine ⟨14601197745937381439004259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19468263661249841918672345 14601197745937381439004259)
                ·
                  refine ⟨21901796618906072158506389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14601197745937381439004259 21901796618906072158506389)
                  ·
                    refine ⟨1026646716511222132429987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21901796618906072158506389 1026646716511222132429987)
                    ·
                      rfl

theorem cell23_5998162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_5998162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998162 prefixEnd_5998162 := by exact prefixLift 5998162
  have htrace : WordTrace (prefixWord ++ tailWord_5998162) baseStart_5998162 baseEnd_5998162 := by
    simpa [prefixWord, tailWord_5998162, baseEnd_5998162] using wordTrace_append hprefix tailTrace_5998162
  have hstable : (prefixWord ++ tailWord_5998162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998162).length < 2 ^ (prefixWord ++ tailWord_5998162).sum := by decide
  have hdescent : baseEnd_5998162 < baseStart_5998162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998179 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 2, 4]
def baseStart_5998179 : Nat := 118140960795 + 5998179 * 2 ^ 59
def prefixEnd_5998179 : Nat := 4983230072969 + 3 ^ 40 * 5998179 * 2
def baseEnd_5998179 : Nat := 1026649626234930943592461

theorem tailTrace_5998179 : CollatzResearch.WordTrace tailWord_5998179 prefixEnd_5998179 1026649626234930943592461 := by
  unfold tailWord_5998179
  simp only [CollatzResearch.WordTrace]
  refine ⟨218771560936629365261069591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145847707291086243507379727 218771560936629365261069591)
  ·
    refine ⟨328157341404944047891604387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218771560936629365261069591 328157341404944047891604387)
    ·
      refine ⟨492236012107416071837406581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328157341404944047891604387 492236012107416071837406581)
      ·
        refine ⟨46147126135070256734756867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 492236012107416071837406581 46147126135070256734756867)
        ·
          refine ⟨69220689202605385102135301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46147126135070256734756867 69220689202605385102135301)
          ·
            refine ⟨12978879225488509706650369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69220689202605385102135301 12978879225488509706650369)
            ·
              refine ⟨9734159419116382279987777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12978879225488509706650369 9734159419116382279987777)
              ·
                refine ⟨7300619564337286709990833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9734159419116382279987777 7300619564337286709990833)
                ·
                  refine ⟨5475464673252965032493125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300619564337286709990833 5475464673252965032493125)
                  ·
                    refine ⟨1026649626234930943592461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475464673252965032493125 1026649626234930943592461)
                    ·
                      rfl

theorem cell23_5998179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 4].length) (baseStart_5998179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998179 prefixEnd_5998179 := by exact prefixLift 5998179
  have htrace : WordTrace (prefixWord ++ tailWord_5998179) baseStart_5998179 baseEnd_5998179 := by
    simpa [prefixWord, tailWord_5998179, baseEnd_5998179] using wordTrace_append hprefix tailTrace_5998179
  have hstable : (prefixWord ++ tailWord_5998179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998179).length < 2 ^ (prefixWord ++ tailWord_5998179).sum := by decide
  have hdescent : baseEnd_5998179 < baseStart_5998179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998192 : List Nat := [2, 1, 1, 1, 6, 3, 1, 8]
def baseStart_5998192 : Nat := 118140960795 + 5998192 * 2 ^ 59
def prefixEnd_5998192 : Nat := 4983230072969 + 3 ^ 40 * 5998192 * 2
def baseEnd_5998192 : Nat := 114072427924196343700549

theorem tailTrace_5998192 : CollatzResearch.WordTrace tailWord_5998192 prefixEnd_5998192 114072427924196343700549 := by
  unfold tailWord_5998192
  simp only [CollatzResearch.WordTrace]
  refine ⟨109386017542791134240646415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145848023390388178987528553 109386017542791134240646415)
  ·
    refine ⟨164079026314186701360969623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109386017542791134240646415 164079026314186701360969623)
    ·
      refine ⟨246118539471280052041454435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164079026314186701360969623 246118539471280052041454435)
      ·
        refine ⟨369177809206920078062181653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246118539471280052041454435 369177809206920078062181653)
        ·
          refine ⟨17305209806574378659164765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369177809206920078062181653 17305209806574378659164765)
          ·
            refine ⟨6489453677465391997186787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17305209806574378659164765 6489453677465391997186787)
            ·
              refine ⟨9734180516198087995780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489453677465391997186787 9734180516198087995780181)
              ·
                refine ⟨114072427924196343700549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9734180516198087995780181 114072427924196343700549)
                ·
                  rfl

theorem cell23_5998192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_5998192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998192 prefixEnd_5998192 := by exact prefixLift 5998192
  have htrace : WordTrace (prefixWord ++ tailWord_5998192) baseStart_5998192 baseEnd_5998192 := by
    simpa [prefixWord, tailWord_5998192, baseEnd_5998192] using wordTrace_append hprefix tailTrace_5998192
  have hstable : (prefixWord ++ tailWord_5998192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998192).length < 2 ^ (prefixWord ++ tailWord_5998192).sum := by decide
  have hdescent : baseEnd_5998192 < baseStart_5998192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998225 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_5998225 : Nat := 118140960795 + 5998225 * 2 ^ 59
def prefixEnd_5998225 : Nat := 4983230072969 + 3 ^ 40 * 5998225 * 2
def baseEnd_5998225 : Nat := 3079972498814899650802171

theorem tailTrace_5998225 : CollatzResearch.WordTrace tailWord_5998225 prefixEnd_5998225 3079972498814899650802171 := by
  unfold tailWord_5998225
  simp only [CollatzResearch.WordTrace]
  refine ⟨218773238694462715117244129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145848825796308476744829419 218773238694462715117244129)
  ·
    refine ⟨164079929020847036337933097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218773238694462715117244129 164079929020847036337933097)
    ·
      refine ⟨123059946765635277253449823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164079929020847036337933097 123059946765635277253449823)
      ·
        refine ⟨184589920148452915880174735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123059946765635277253449823 184589920148452915880174735)
        ·
          refine ⟨276884880222679373820262103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184589920148452915880174735 276884880222679373820262103)
          ·
            refine ⟨415327320334019060730393155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276884880222679373820262103 415327320334019060730393155)
            ·
              refine ⟨622990980501028591095589733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415327320334019060730393155 622990980501028591095589733)
              ·
                refine ⟨116810808843942860830423075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622990980501028591095589733 116810808843942860830423075)
                ·
                  refine ⟨175216213265914291245634613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116810808843942860830423075 175216213265914291245634613)
                  ·
                    refine ⟨16426519993679464804278245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175216213265914291245634613 16426519993679464804278245)
                    ·
                      refine ⟨3079972498814899650802171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16426519993679464804278245 3079972498814899650802171)
                      ·
                        rfl

theorem cell23_5998225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_5998225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998225 prefixEnd_5998225 := by exact prefixLift 5998225
  have htrace : WordTrace (prefixWord ++ tailWord_5998225) baseStart_5998225 baseEnd_5998225 := by
    simpa [prefixWord, tailWord_5998225, baseEnd_5998225] using wordTrace_append hprefix tailTrace_5998225
  have hstable : (prefixWord ++ tailWord_5998225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998225).length < 2 ^ (prefixWord ++ tailWord_5998225).sum := by decide
  have hdescent : baseEnd_5998225 < baseStart_5998225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998236 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5998236 : Nat := 118140960795 + 5998236 * 2 ^ 59
def prefixEnd_5998236 : Nat := 4983230072969 + 3 ^ 40 * 5998236 * 2
def baseEnd_5998236 : Nat := 3079978147102099107764621

theorem tailTrace_5998236 : CollatzResearch.WordTrace tailWord_5998236 prefixEnd_5998236 3079978147102099107764621 := by
  unfold tailWord_5998236
  simp only [CollatzResearch.WordTrace]
  refine ⟨109386819948711431997947281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145849093264948575997263041 109386819948711431997947281)
  ·
    refine ⟨82040114961533573998460461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109386819948711431997947281 82040114961533573998460461)
    ·
      refine ⟨30765043110575090249422673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82040114961533573998460461 30765043110575090249422673)
      ·
        refine ⟨23073782332931317687067005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30765043110575090249422673 23073782332931317687067005)
        ·
          refine ⟨8652668374849244132650127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23073782332931317687067005 8652668374849244132650127)
          ·
            refine ⟨12979002562273866198975191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652668374849244132650127 12979002562273866198975191)
            ·
              refine ⟨19468503843410799298462787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979002562273866198975191 19468503843410799298462787)
              ·
                refine ⟨29202755765116198947694181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19468503843410799298462787 29202755765116198947694181)
                ·
                  refine ⟨5475516705959287302692659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29202755765116198947694181 5475516705959287302692659)
                  ·
                    refine ⟨8213275058938930954038989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475516705959287302692659 8213275058938930954038989)
                    ·
                      refine ⟨3079978147102099107764621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213275058938930954038989 3079978147102099107764621)
                      ·
                        rfl

theorem cell23_5998236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5998236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998236 prefixEnd_5998236 := by exact prefixLift 5998236
  have htrace : WordTrace (prefixWord ++ tailWord_5998236) baseStart_5998236 baseEnd_5998236 := by
    simpa [prefixWord, tailWord_5998236, baseEnd_5998236] using wordTrace_append hprefix tailTrace_5998236
  have hstable : (prefixWord ++ tailWord_5998236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998236).length < 2 ^ (prefixWord ++ tailWord_5998236).sum := by decide
  have hdescent : baseEnd_5998236 < baseStart_5998236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998253 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_5998253 : Nat := 118140960795 + 5998253 * 2 ^ 59
def prefixEnd_5998253 : Nat := 4983230072969 + 3 ^ 40 * 5998253 * 2
def baseEnd_5998253 : Nat := 3079986876273225541252043

theorem tailTrace_5998253 : CollatzResearch.WordTrace tailWord_5998253 prefixEnd_5998253 3079986876273225541252043 := by
  unfold tailWord_5998253
  simp only [CollatzResearch.WordTrace]
  refine ⟨218774259938361275899263413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145849506625574183932842275 218774259938361275899263413)
  ·
    refine ⟨20510086869221369615555945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218774259938361275899263413 20510086869221369615555945)
    ·
      refine ⟨15382565151916027211666959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20510086869221369615555945 15382565151916027211666959)
      ·
        refine ⟨23073847727874040817500439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382565151916027211666959 23073847727874040817500439)
        ·
          refine ⟨34610771591811061226250659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23073847727874040817500439 34610771591811061226250659)
          ·
            refine ⟨51916157387716591839375989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34610771591811061226250659 51916157387716591839375989)
            ·
              refine ⟨4867139755098430484941499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51916157387716591839375989 4867139755098430484941499)
              ·
                refine ⟨7300709632647645727412249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867139755098430484941499 7300709632647645727412249)
                ·
                  refine ⟨5475532224485734295559187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300709632647645727412249 5475532224485734295559187)
                  ·
                    refine ⟨8213298336728601443338781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475532224485734295559187 8213298336728601443338781)
                    ·
                      refine ⟨3079986876273225541252043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213298336728601443338781 3079986876273225541252043)
                      ·
                        rfl

theorem cell23_5998253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_5998253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998253 prefixEnd_5998253 := by exact prefixLift 5998253
  have htrace : WordTrace (prefixWord ++ tailWord_5998253) baseStart_5998253 baseEnd_5998253 := by
    simpa [prefixWord, tailWord_5998253, baseEnd_5998253] using wordTrace_append hprefix tailTrace_5998253
  have hstable : (prefixWord ++ tailWord_5998253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998253).length < 2 ^ (prefixWord ++ tailWord_5998253).sum := by decide
  have hdescent : baseEnd_5998253 < baseStart_5998253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998276 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5998276 : Nat := 118140960795 + 5998276 * 2 ^ 59
def prefixEnd_5998276 : Nat := 4983230072969 + 3 ^ 40 * 5998276 * 2
def baseEnd_5998276 : Nat := 3079998686328278951264437

theorem tailTrace_5998276 : CollatzResearch.WordTrace tailWord_5998276 prefixEnd_5998276 3079998686328278951264437 := by
  unfold tailWord_5998276
  simp only [CollatzResearch.WordTrace]
  refine ⟨109387549408638975413675341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145850065878185300551567121 109387549408638975413675341)
  ·
    refine ⟨41020331028239615780128253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109387549408638975413675341 41020331028239615780128253)
    ·
      refine ⟨15382624135589855917548095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41020331028239615780128253 15382624135589855917548095)
      ·
        refine ⟨23073936203384783876322143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382624135589855917548095 23073936203384783876322143)
        ·
          refine ⟨34610904305077175814483215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23073936203384783876322143 34610904305077175814483215)
          ·
            refine ⟨51916356457615763721724823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34610904305077175814483215 51916356457615763721724823)
            ·
              refine ⟨77874534686423645582587235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51916356457615763721724823 77874534686423645582587235)
              ·
                refine ⟨116811802029635468373880853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77874534686423645582587235 116811802029635468373880853)
                ·
                  refine ⟨5475553220139162580025665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116811802029635468373880853 5475553220139162580025665)
                  ·
                    refine ⟨4106664915104371935019249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475553220139162580025665 4106664915104371935019249)
                    ·
                      refine ⟨3079998686328278951264437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4106664915104371935019249 3079998686328278951264437)
                      ·
                        rfl

theorem cell23_5998276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5998276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998276 prefixEnd_5998276 := by exact prefixLift 5998276
  have htrace : WordTrace (prefixWord ++ tailWord_5998276) baseStart_5998276 baseEnd_5998276 := by
    simpa [prefixWord, tailWord_5998276, baseEnd_5998276] using wordTrace_append hprefix tailTrace_5998276
  have hstable : (prefixWord ++ tailWord_5998276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998276).length < 2 ^ (prefixWord ++ tailWord_5998276).sum := by decide
  have hdescent : baseEnd_5998276 < baseStart_5998276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998322 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5998322 : Nat := 118140960795 + 5998322 * 2 ^ 59
def prefixEnd_5998322 : Nat := 4983230072969 + 3 ^ 40 * 5998322 * 2
def baseEnd_5998322 : Nat := 3080022306438385771289225

theorem tailTrace_5998322 : CollatzResearch.WordTrace tailWord_5998322 prefixEnd_5998322 3080022306438385771289225 := by
  unfold tailWord_5998322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54694194143777825170881305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145851184383407533789016813 54694194143777825170881305)
  ·
    refine ⟨41020645607833368878160979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54694194143777825170881305 41020645607833368878160979)
    ·
      refine ⟨61530968411750053317241469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41020645607833368878160979 61530968411750053317241469)
      ·
        refine ⟨23074113154406269993965551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61530968411750053317241469 23074113154406269993965551)
        ·
          refine ⟨34611169731609404990948327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23074113154406269993965551 34611169731609404990948327)
          ·
            refine ⟨51916754597414107486422491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34611169731609404990948327 51916754597414107486422491)
            ·
              refine ⟨77875131896121161229633737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51916754597414107486422491 77875131896121161229633737)
              ·
                refine ⟨58406348922090870922225303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77875131896121161229633737 58406348922090870922225303)
                ·
                  refine ⟨87609523383136306383337955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58406348922090870922225303 87609523383136306383337955)
                  ·
                    refine ⟨131414285074704459575006933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87609523383136306383337955 131414285074704459575006933)
                    ·
                      refine ⟨3080022306438385771289225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131414285074704459575006933 3080022306438385771289225)
                      ·
                        rfl

theorem cell23_5998322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5998322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998322 prefixEnd_5998322 := by exact prefixLift 5998322
  have htrace : WordTrace (prefixWord ++ tailWord_5998322) baseStart_5998322 baseEnd_5998322 := by
    simpa [prefixWord, tailWord_5998322, baseEnd_5998322] using wordTrace_append hprefix tailTrace_5998322
  have hstable : (prefixWord ++ tailWord_5998322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998322).length < 2 ^ (prefixWord ++ tailWord_5998322).sum := by decide
  have hdescent : baseEnd_5998322 < baseStart_5998322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998376 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5998376 : Nat := 118140960795 + 5998376 * 2 ^ 59
def prefixEnd_5998376 : Nat := 4983230072969 + 3 ^ 40 * 5998376 * 2
def baseEnd_5998376 : Nat := 1026683344797909520004659

theorem tailTrace_5998376 : CollatzResearch.WordTrace tailWord_5998376 prefixEnd_5998376 1026683344797909520004659 := by
  unfold tailWord_5998376
  simp only [CollatzResearch.WordTrace]
  refine ⟨109389373058457833952995491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145852497411277111937327321 109389373058457833952995491)
  ·
    refine ⟨164084059587686750929493237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109389373058457833952995491 164084059587686750929493237)
    ·
      refine ⟨15382880586345632899639991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164084059587686750929493237 15382880586345632899639991)
      ·
        refine ⟨23074320879518449349459987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382880586345632899639991 23074320879518449349459987)
        ·
          refine ⟨34611481319277674024189981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23074320879518449349459987 34611481319277674024189981)
          ·
            refine ⟨12979305494729127759071243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34611481319277674024189981 12979305494729127759071243)
            ·
              refine ⟨19468958242093691638606865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979305494729127759071243 19468958242093691638606865)
              ·
                refine ⟨14601718681570268728955149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19468958242093691638606865 14601718681570268728955149)
                ·
                  refine ⟨5475644505588850773358181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14601718681570268728955149 5475644505588850773358181)
                  ·
                    refine ⟨1026683344797909520004659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475644505588850773358181 1026683344797909520004659)
                    ·
                      rfl

theorem cell23_5998376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5998376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998376 prefixEnd_5998376 := by exact prefixLift 5998376
  have htrace : WordTrace (prefixWord ++ tailWord_5998376) baseStart_5998376 baseEnd_5998376 := by
    simpa [prefixWord, tailWord_5998376, baseEnd_5998376] using wordTrace_append hprefix tailTrace_5998376
  have hstable : (prefixWord ++ tailWord_5998376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998376).length < 2 ^ (prefixWord ++ tailWord_5998376).sum := by decide
  have hdescent : baseEnd_5998376 < baseStart_5998376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998386 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_5998386 : Nat := 118140960795 + 5998386 * 2 ^ 59
def prefixEnd_5998386 : Nat := 4983230072969 + 3 ^ 40 * 5998386 * 2
def baseEnd_5998386 : Nat := 3080055169200273520888931

theorem tailTrace_5998386 : CollatzResearch.WordTrace tailWord_5998386 prefixEnd_5998386 3080055169200273520888931 := by
  unfold tailWord_5998386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54694777711719859903463753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145852740564586293075903341 54694777711719859903463753)
  ·
    refine ⟨41021083283789894927597815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54694777711719859903463753 41021083283789894927597815)
    ·
      refine ⟨61531624925684842391396723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41021083283789894927597815 61531624925684842391396723)
      ·
        refine ⟨92297437388527263587095085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61531624925684842391396723 92297437388527263587095085)
        ·
          refine ⟨34611539020697723845160657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92297437388527263587095085 34611539020697723845160657)
          ·
            refine ⟨25958654265523292883870493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34611539020697723845160657 25958654265523292883870493)
            ·
              refine ⟨9734495349571234831451435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25958654265523292883870493 9734495349571234831451435)
              ·
                refine ⟨14601743024356852247177153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9734495349571234831451435 14601743024356852247177153)
                ·
                  refine ⟨10951307268267639185382865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14601743024356852247177153 10951307268267639185382865)
                  ·
                    refine ⟨8213480451200729389037149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10951307268267639185382865 8213480451200729389037149)
                    ·
                      refine ⟨3080055169200273520888931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213480451200729389037149 3080055169200273520888931)
                      ·
                        rfl

theorem cell23_5998386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_5998386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998386 prefixEnd_5998386 := by exact prefixLift 5998386
  have htrace : WordTrace (prefixWord ++ tailWord_5998386) baseStart_5998386 baseEnd_5998386 := by
    simpa [prefixWord, tailWord_5998386, baseEnd_5998386] using wordTrace_append hprefix tailTrace_5998386
  have hstable : (prefixWord ++ tailWord_5998386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998386).length < 2 ^ (prefixWord ++ tailWord_5998386).sum := by decide
  have hdescent : baseEnd_5998386 < baseStart_5998386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998449 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_5998449 : Nat := 118140960795 + 5998449 * 2 ^ 59
def prefixEnd_5998449 : Nat := 4983230072969 + 3 ^ 40 * 5998449 * 2
def baseEnd_5998449 : Nat := 1026695839493835591467047

theorem tailTrace_5998449 : CollatzResearch.WordTrace tailWord_5998449 prefixEnd_5998449 1026695839493835591467047 := by
  unfold tailWord_5998449
  simp only [CollatzResearch.WordTrace]
  refine ⟨218781408645651201373398401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145854272430434134248932267 218781408645651201373398401)
  ·
    refine ⟨164086056484238401030048801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218781408645651201373398401 164086056484238401030048801)
    ·
      refine ⟨123064542363178800772536601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164086056484238401030048801 123064542363178800772536601)
      ·
        refine ⟨92298406772384100579402451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123064542363178800772536601 92298406772384100579402451)
        ·
          refine ⟨138447610158576150869103677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92298406772384100579402451 138447610158576150869103677)
          ·
            refine ⟨51917853809466056575913879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138447610158576150869103677 51917853809466056575913879)
            ·
              refine ⟨77876780714199084863870819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51917853809466056575913879 77876780714199084863870819)
              ·
                refine ⟨116815171071298627295806229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77876780714199084863870819 116815171071298627295806229)
                ·
                  refine ⟨5475711143967123154490917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116815171071298627295806229 5475711143967123154490917)
                  ·
                    refine ⟨1026695839493835591467047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475711143967123154490917 1026695839493835591467047)
                    ·
                      rfl

theorem cell23_5998449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_5998449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998449 prefixEnd_5998449 := by exact prefixLift 5998449
  have htrace : WordTrace (prefixWord ++ tailWord_5998449) baseStart_5998449 baseEnd_5998449 := by
    simpa [prefixWord, tailWord_5998449, baseEnd_5998449] using wordTrace_append hprefix tailTrace_5998449
  have hstable : (prefixWord ++ tailWord_5998449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998449).length < 2 ^ (prefixWord ++ tailWord_5998449).sum := by decide
  have hdescent : baseEnd_5998449 < baseStart_5998449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998459 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3]
def baseStart_5998459 : Nat := 118140960795 + 5998459 * 2 ^ 59
def prefixEnd_5998459 : Nat := 4983230072969 + 3 ^ 40 * 5998459 * 2
def baseEnd_5998459 : Nat := 3080092653288051735276095

theorem tailTrace_5998459 : CollatzResearch.WordTrace tailWord_5998459 prefixEnd_5998459 3080092653288051735276095 := by
  unfold tailWord_5998459
  simp only [CollatzResearch.WordTrace]
  refine ⟨218781773375614973081262431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145854515583743315387508287 218781773375614973081262431)
  ·
    refine ⟨328172660063422459621893647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218781773375614973081262431 328172660063422459621893647)
    ·
      refine ⟨492258990095133689432840471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328172660063422459621893647 492258990095133689432840471)
      ·
        refine ⟨738388485142700534149260707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492258990095133689432840471 738388485142700534149260707)
        ·
          refine ⟨1107582727714050801223891061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738388485142700534149260707 1107582727714050801223891061)
          ·
            refine ⟨103835880723192262614739787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1107582727714050801223891061 103835880723192262614739787)
            ·
              refine ⟨155753821084788393922109681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103835880723192262614739787 155753821084788393922109681)
              ·
                refine ⟨116815365813591295441582261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155753821084788393922109681 116815365813591295441582261)
                ·
                  refine ⟨10951440545024183947648337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116815365813591295441582261 10951440545024183947648337)
                  ·
                    refine ⟨8213580408768137960736253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10951440545024183947648337 8213580408768137960736253)
                    ·
                      refine ⟨3080092653288051735276095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213580408768137960736253 3080092653288051735276095)
                      ·
                        rfl

theorem cell23_5998459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].length) (baseStart_5998459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998459 prefixEnd_5998459 := by exact prefixLift 5998459
  have htrace : WordTrace (prefixWord ++ tailWord_5998459) baseStart_5998459 baseEnd_5998459 := by
    simpa [prefixWord, tailWord_5998459, baseEnd_5998459] using wordTrace_append hprefix tailTrace_5998459
  have hstable : (prefixWord ++ tailWord_5998459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998459).length < 2 ^ (prefixWord ++ tailWord_5998459).sum := by decide
  have hdescent : baseEnd_5998459 < baseStart_5998459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5998493 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5998493 : Nat := 118140960795 + 5998493 * 2 ^ 59
def prefixEnd_5998493 : Nat := 4983230072969 + 3 ^ 40 * 5998493 * 2
def baseEnd_5998493 : Nat := 3080110111630304602250939

theorem tailTrace_5998493 : CollatzResearch.WordTrace tailWord_5998493 prefixEnd_5998493 3080110111630304602250939 := by
  unfold tailWord_5998493
  simp only [CollatzResearch.WordTrace]
  refine ⟨218783013457491796888000133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145855342304994531258666755 218783013457491796888000133)
  ·
    refine ⟨41021815023279711916500025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218783013457491796888000133 41021815023279711916500025)
    ·
      refine ⟨30766361267459783937375019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41021815023279711916500025 30766361267459783937375019)
      ·
        refine ⟨46149541901189675906062529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30766361267459783937375019 46149541901189675906062529)
        ·
          refine ⟨34612156425892256929546897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46149541901189675906062529 34612156425892256929546897)
          ·
            refine ⟨25959117319419192697160173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34612156425892256929546897 25959117319419192697160173)
            ·
              refine ⟨9734668994782197261435065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25959117319419192697160173 9734668994782197261435065)
              ·
                refine ⟨7301001746086647946076299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9734668994782197261435065 7301001746086647946076299)
                ·
                  refine ⟨10951502619129971919114449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301001746086647946076299 10951502619129971919114449)
                  ·
                    refine ⟨8213626964347478939335837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10951502619129971919114449 8213626964347478939335837)
                    ·
                      refine ⟨3080110111630304602250939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8213626964347478939335837 3080110111630304602250939)
                      ·
                        rfl

theorem cell23_5998493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5998493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5998493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5998493 prefixEnd_5998493 := by exact prefixLift 5998493
  have htrace : WordTrace (prefixWord ++ tailWord_5998493) baseStart_5998493 baseEnd_5998493 := by
    simpa [prefixWord, tailWord_5998493, baseEnd_5998493] using wordTrace_append hprefix tailTrace_5998493
  have hstable : (prefixWord ++ tailWord_5998493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5998493).length < 2 ^ (prefixWord ++ tailWord_5998493).sum := by decide
  have hdescent : baseEnd_5998493 < baseStart_5998493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5998493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
