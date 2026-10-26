import V185TrunkScan23Chunk0386

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2287324 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2287324 : Nat := 118140960795 + 2287324 * 2 ^ 59
def prefixEnd_2287324 : Nat := 4983230072969 + 3 ^ 40 * 2287324 * 2
def baseEnd_2287324 : Nat := 1174496624564714068030795

theorem tailTrace_2287324 : CollatzResearch.WordTrace tailWord_2287324 prefixEnd_2287324 1174496624564714068030795 := by
  unfold tailWord_2287324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41712779982711633341782513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55617039976948844455710017 41712779982711633341782513)
  ·
    refine ⟨31284584987033725006336885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41712779982711633341782513 31284584987033725006336885)
    ·
      refine ⟨2932929842534411719344083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31284584987033725006336885 2932929842534411719344083)
      ·
        refine ⟨4399394763801617579016125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932929842534411719344083 4399394763801617579016125)
        ·
          refine ⟨1649773036425606592131047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4399394763801617579016125 1649773036425606592131047)
          ·
            refine ⟨2474659554638409888196571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649773036425606592131047 2474659554638409888196571)
            ·
              refine ⟨3711989331957614832294857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474659554638409888196571 3711989331957614832294857)
              ·
                refine ⟨2783991998968211124221143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711989331957614832294857 2783991998968211124221143)
                ·
                  refine ⟨4175987998452316686331715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783991998968211124221143 4175987998452316686331715)
                  ·
                    refine ⟨6263981997678475029497573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175987998452316686331715 6263981997678475029497573)
                    ·
                      refine ⟨1174496624564714068030795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6263981997678475029497573 1174496624564714068030795)
                      ·
                        rfl

theorem cell23_2287324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2287324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287324 prefixEnd_2287324 := by exact prefixLift 2287324
  have htrace : WordTrace (prefixWord ++ tailWord_2287324) baseStart_2287324 baseEnd_2287324 := by
    simpa [prefixWord, tailWord_2287324, baseEnd_2287324] using wordTrace_append hprefix tailTrace_2287324
  have hstable : (prefixWord ++ tailWord_2287324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287324).length < 2 ^ (prefixWord ++ tailWord_2287324).sum := by decide
  have hdescent : baseEnd_2287324 < baseStart_2287324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287356 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2287356 : Nat := 118140960795 + 2287356 * 2 ^ 59
def prefixEnd_2287356 : Nat := 4983230072969 + 3 ^ 40 * 2287356 * 2
def baseEnd_2287356 : Nat := 391504351981885980943549

theorem tailTrace_2287356 : CollatzResearch.WordTrace tailWord_2287356 prefixEnd_2287356 391504351981885980943549 := by
  unfold tailWord_2287356
  simp only [CollatzResearch.WordTrace]
  refine ⟨41713363550653668074364961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55617818067538224099153281 41713363550653668074364961)
  ·
    refine ⟨31285022662990251055773721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41713363550653668074364961 31285022662990251055773721)
    ·
      refine ⟨23463766997242688291830291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31285022662990251055773721 23463766997242688291830291)
      ·
        refine ⟨35195650495864032437745437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23463766997242688291830291 35195650495864032437745437)
        ·
          refine ⟨13198368935949012164154539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35195650495864032437745437 13198368935949012164154539)
          ·
            refine ⟨19797553403923518246231809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13198368935949012164154539 19797553403923518246231809)
            ·
              refine ⟨14848165052942638684673857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19797553403923518246231809 14848165052942638684673857)
              ·
                refine ⟨11136123789706979013505393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14848165052942638684673857 11136123789706979013505393)
                ·
                  refine ⟨8352092842280234260129045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11136123789706979013505393 8352092842280234260129045)
                  ·
                    refine ⟨391504351981885980943549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8352092842280234260129045 391504351981885980943549)
                    ·
                      rfl

theorem cell23_2287356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2287356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287356 prefixEnd_2287356 := by exact prefixLift 2287356
  have htrace : WordTrace (prefixWord ++ tailWord_2287356) baseStart_2287356 baseEnd_2287356 := by
    simpa [prefixWord, tailWord_2287356, baseEnd_2287356] using wordTrace_append hprefix tailTrace_2287356
  have hstable : (prefixWord ++ tailWord_2287356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287356).length < 2 ^ (prefixWord ++ tailWord_2287356).sum := by decide
  have hdescent : baseEnd_2287356 < baseStart_2287356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287358 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_2287358 : Nat := 118140960795 + 2287358 * 2 ^ 59
def prefixEnd_2287358 : Nat := 4983230072969 + 3 ^ 40 * 2287358 * 2
def baseEnd_2287358 : Nat := 1174514082906966935005639

theorem tailTrace_2287358 : CollatzResearch.WordTrace tailWord_2287358 prefixEnd_2287358 1174514082906966935005639 := by
  unfold tailWord_2287358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428350005912511311287841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55617866698200060326868485 10428350005912511311287841)
  ·
    refine ⟨7821262504434383483465881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10428350005912511311287841 7821262504434383483465881)
    ·
      refine ⟨5865946878325787612599411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7821262504434383483465881 5865946878325787612599411)
      ·
        refine ⟨8798920317488681418899117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865946878325787612599411 8798920317488681418899117)
        ·
          refine ⟨3299595119058255532087169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8798920317488681418899117 3299595119058255532087169)
          ·
            refine ⟨2474696339293691649065377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299595119058255532087169 2474696339293691649065377)
            ·
              refine ⟨1856022254470268736799033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474696339293691649065377 1856022254470268736799033)
              ·
                refine ⟨1392016690852701552599275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856022254470268736799033 1392016690852701552599275)
                ·
                  refine ⟨2088025036279052328898913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392016690852701552599275 2088025036279052328898913)
                  ·
                    refine ⟨1566018777209289246674185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088025036279052328898913 1566018777209289246674185)
                    ·
                      refine ⟨1174514082906966935005639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566018777209289246674185 1174514082906966935005639)
                      ·
                        rfl

theorem cell23_2287358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_2287358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287358 prefixEnd_2287358 := by exact prefixLift 2287358
  have htrace : WordTrace (prefixWord ++ tailWord_2287358) baseStart_2287358 baseEnd_2287358 := by
    simpa [prefixWord, tailWord_2287358, baseEnd_2287358] using wordTrace_append hprefix tailTrace_2287358
  have hstable : (prefixWord ++ tailWord_2287358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287358).length < 2 ^ (prefixWord ++ tailWord_2287358).sum := by decide
  have hdescent : baseEnd_2287358 < baseStart_2287358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287386 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_2287386 : Nat := 118140960795 + 2287386 * 2 ^ 59
def prefixEnd_2287386 : Nat := 4983230072969 + 3 ^ 40 * 2287386 * 2
def baseEnd_2287386 : Nat := 130503162262810313939501

theorem tailTrace_2287386 : CollatzResearch.WordTrace tailWord_2287386 prefixEnd_2287386 130503162262810313939501 := by
  unfold tailWord_2287386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20856955322799662818080503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55618547527465767514881341 20856955322799662818080503)
  ·
    refine ⟨31285432984199494227120755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20856955322799662818080503 31285432984199494227120755)
    ·
      refine ⟨46928149476299241340681133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31285432984199494227120755 46928149476299241340681133)
      ·
        refine ⟨17598056053612215502755425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46928149476299241340681133 17598056053612215502755425)
        ·
          refine ⟨13198542040209161627066569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17598056053612215502755425 13198542040209161627066569)
          ·
            refine ⟨9898906530156871220299927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13198542040209161627066569 9898906530156871220299927)
            ·
              refine ⟨14848359795235306830449891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9898906530156871220299927 14848359795235306830449891)
              ·
                refine ⟨22272539692852960245674837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14848359795235306830449891 22272539692852960245674837)
                ·
                  refine ⟨130503162262810313939501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22272539692852960245674837 130503162262810313939501)
                  ·
                    rfl

theorem cell23_2287386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_2287386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287386 prefixEnd_2287386 := by exact prefixLift 2287386
  have htrace : WordTrace (prefixWord ++ tailWord_2287386) baseStart_2287386 baseEnd_2287386 := by
    simpa [prefixWord, tailWord_2287386, baseEnd_2287386] using wordTrace_append hprefix tailTrace_2287386
  have hstable : (prefixWord ++ tailWord_2287386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287386).length < 2 ^ (prefixWord ++ tailWord_2287386).sum := by decide
  have hdescent : baseEnd_2287386 < baseStart_2287386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287414 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2287414 : Nat := 118140960795 + 2287414 * 2 ^ 59
def prefixEnd_2287414 : Nat := 4983230072969 + 3 ^ 40 * 2287414 * 2
def baseEnd_2287414 : Nat := 1174542837823618715905381

theorem tailTrace_2287414 : CollatzResearch.WordTrace tailWord_2287414 prefixEnd_2287414 1174542837823618715905381 := by
  unfold tailWord_2287414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214302658443575753396331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55619228356731474702894197 5214302658443575753396331)
  ·
    refine ⟨7821453987665363630094497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5214302658443575753396331 7821453987665363630094497)
    ·
      refine ⟨5866090490749022722570873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7821453987665363630094497 5866090490749022722570873)
      ·
        refine ⟨4399567868061767041928155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866090490749022722570873 4399567868061767041928155)
        ·
          refine ⟨6599351802092650562892233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399567868061767041928155 6599351802092650562892233)
          ·
            refine ⟨4949513851569487922169175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6599351802092650562892233 4949513851569487922169175)
            ·
              refine ⟨7424270777354231883253763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949513851569487922169175 7424270777354231883253763)
              ·
                refine ⟨11136406166031347824880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424270777354231883253763 11136406166031347824880645)
                ·
                  refine ⟨2088076156130877717165121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11136406166031347824880645 2088076156130877717165121)
                  ·
                    refine ⟨1566057117098158287873841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088076156130877717165121 1566057117098158287873841)
                    ·
                      refine ⟨1174542837823618715905381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566057117098158287873841 1174542837823618715905381)
                      ·
                        rfl

theorem cell23_2287414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2287414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287414 prefixEnd_2287414 := by exact prefixLift 2287414
  have htrace : WordTrace (prefixWord ++ tailWord_2287414) baseStart_2287414 baseEnd_2287414 := by
    simpa [prefixWord, tailWord_2287414, baseEnd_2287414] using wordTrace_append hprefix tailTrace_2287414
  have hstable : (prefixWord ++ tailWord_2287414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287414).length < 2 ^ (prefixWord ++ tailWord_2287414).sum := by decide
  have hdescent : baseEnd_2287414 < baseStart_2287414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287470 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2287470 : Nat := 118140960795 + 2287470 * 2 ^ 59
def prefixEnd_2287470 : Nat := 4983230072969 + 3 ^ 40 * 2287470 * 2
def baseEnd_2287470 : Nat := 1174571592740270496805123

theorem tailTrace_2287470 : CollatzResearch.WordTrace tailWord_2287470 prefixEnd_2287470 1174571592740270496805123 := by
  unfold tailWord_2287470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428860627861791702297483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55620590015262889078919909 10428860627861791702297483)
  ·
    refine ⟨15643290941792687553446225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428860627861791702297483 15643290941792687553446225)
    ·
      refine ⟨11732468206344515665084669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15643290941792687553446225 11732468206344515665084669)
      ·
        refine ⟨4399675577379193374406751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11732468206344515665084669 4399675577379193374406751)
        ·
          refine ⟨6599513366068790061610127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399675577379193374406751 6599513366068790061610127)
          ·
            refine ⟨9899270049103185092415191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599513366068790061610127 9899270049103185092415191)
            ·
              refine ⟨14848905073654777638622787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899270049103185092415191 14848905073654777638622787)
              ·
                refine ⟨22273357610482166457934181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14848905073654777638622787 22273357610482166457934181)
                ·
                  refine ⟨4176254551965406210862659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22273357610482166457934181 4176254551965406210862659)
                  ·
                    refine ⟨6264381827948109316293989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176254551965406210862659 6264381827948109316293989)
                    ·
                      refine ⟨1174571592740270496805123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6264381827948109316293989 1174571592740270496805123)
                      ·
                        rfl

theorem cell23_2287470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2287470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287470 prefixEnd_2287470 := by exact prefixLift 2287470
  have htrace : WordTrace (prefixWord ++ tailWord_2287470) baseStart_2287470 baseEnd_2287470 := by
    simpa [prefixWord, tailWord_2287470, baseEnd_2287470] using wordTrace_append hprefix tailTrace_2287470
  have hstable : (prefixWord ++ tailWord_2287470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287470).length < 2 ^ (prefixWord ++ tailWord_2287470).sum := by decide
  have hdescent : baseEnd_2287470 < baseStart_2287470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287493 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 6]
def baseStart_2287493 : Nat := 118140960795 + 2287493 * 2 ^ 59
def prefixEnd_2287493 : Nat := 4983230072969 + 3 ^ 40 * 2287493 * 2
def baseEnd_2287493 : Nat := 130509266977258211868613

theorem tailTrace_2287493 : CollatzResearch.WordTrace tailWord_2287493 prefixEnd_2287493 130509266977258211868613 := by
  unfold tailWord_2287493
  simp only [CollatzResearch.WordTrace]
  refine ⟨83431723901811008546467133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55621149267874005697644755 83431723901811008546467133)
  ·
    refine ⟨31286896463179128204925175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83431723901811008546467133 31286896463179128204925175)
    ·
      refine ⟨46930344694768692307387763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31286896463179128204925175 46930344694768692307387763)
      ·
        refine ⟨70395517042153038461081645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46930344694768692307387763 70395517042153038461081645)
        ·
          refine ⟨26398318890807389422905617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70395517042153038461081645 26398318890807389422905617)
          ·
            refine ⟨19798739168105542067179213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26398318890807389422905617 19798739168105542067179213)
            ·
              refine ⟨7424527188039578275192205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19798739168105542067179213 7424527188039578275192205)
              ·
                refine ⟨2784197695514841853197077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7424527188039578275192205 2784197695514841853197077)
                ·
                  refine ⟨130509266977258211868613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2784197695514841853197077 130509266977258211868613)
                  ·
                    rfl

theorem cell23_2287493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_2287493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287493 prefixEnd_2287493 := by exact prefixLift 2287493
  have htrace : WordTrace (prefixWord ++ tailWord_2287493) baseStart_2287493 baseEnd_2287493 := by
    simpa [prefixWord, tailWord_2287493, baseEnd_2287493] using wordTrace_append hprefix tailTrace_2287493
  have hstable : (prefixWord ++ tailWord_2287493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287493).length < 2 ^ (prefixWord ++ tailWord_2287493).sum := by decide
  have hdescent : baseEnd_2287493 < baseStart_2287493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287560 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2287560 : Nat := 118140960795 + 2287560 * 2 ^ 59
def prefixEnd_2287560 : Nat := 4983230072969 + 3 ^ 40 * 2287560 * 2
def baseEnd_2287560 : Nat := 1174617805999175144679709

theorem tailTrace_2287560 : CollatzResearch.WordTrace tailWord_2287560 prefixEnd_2287560 1174617805999175144679709 := by
  unfold tailWord_2287560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41717083796284139494578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55622778395045519326104089 41717083796284139494578067)
  ·
    refine ⟨62575625694426209241867101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41717083796284139494578067 62575625694426209241867101)
    ·
      refine ⟨23465859635409828465700163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62575625694426209241867101 23465859635409828465700163)
      ·
        refine ⟨35198789453114742698550245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23465859635409828465700163 35198789453114742698550245)
        ·
          refine ⟨6599773022459014255978171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35198789453114742698550245 6599773022459014255978171)
          ·
            refine ⟨9899659533688521383967257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599773022459014255978171 9899659533688521383967257)
            ·
              refine ⟨7424744650266391037975443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9899659533688521383967257 7424744650266391037975443)
              ·
                refine ⟨11137116975399586556963165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424744650266391037975443 11137116975399586556963165)
                ·
                  refine ⟨4176418865774844958861187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11137116975399586556963165 4176418865774844958861187)
                  ·
                    refine ⟨6264628298662267438291781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176418865774844958861187 6264628298662267438291781)
                    ·
                      refine ⟨1174617805999175144679709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6264628298662267438291781 1174617805999175144679709)
                      ·
                        rfl

theorem cell23_2287560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2287560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287560 prefixEnd_2287560 := by exact prefixLift 2287560
  have htrace : WordTrace (prefixWord ++ tailWord_2287560) baseStart_2287560 baseEnd_2287560 := by
    simpa [prefixWord, tailWord_2287560, baseEnd_2287560] using wordTrace_append hprefix tailTrace_2287560
  have hstable : (prefixWord ++ tailWord_2287560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287560).length < 2 ^ (prefixWord ++ tailWord_2287560).sum := by decide
  have hdescent : baseEnd_2287560 < baseStart_2287560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287564 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2287564 : Nat := 118140960795 + 2287564 * 2 ^ 59
def prefixEnd_2287564 : Nat := 4983230072969 + 3 ^ 40 * 2287564 * 2
def baseEnd_2287564 : Nat := 1174619859921793129029691

theorem tailTrace_2287564 : CollatzResearch.WordTrace tailWord_2287564 prefixEnd_2287564 1174619859921793129029691 := by
  unfold tailWord_2287564
  simp only [CollatzResearch.WordTrace]
  refine ⟨41717156742276893836150873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55622875656369191781534497 41717156742276893836150873)
  ·
    refine ⟨31287867556707670377113155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41717156742276893836150873 31287867556707670377113155)
    ·
      refine ⟨46931801335061505565669733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31287867556707670377113155 46931801335061505565669733)
      ·
        refine ⟨8799712750324032293563075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46931801335061505565669733 8799712750324032293563075)
        ·
          refine ⟨13199569125486048440344613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799712750324032293563075 13199569125486048440344613)
          ·
            refine ⟨2474919211028634082564615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13199569125486048440344613 2474919211028634082564615)
            ·
              refine ⟨3712378816542951123846923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474919211028634082564615 3712378816542951123846923)
              ·
                refine ⟨5568568224814426685770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712378816542951123846923 5568568224814426685770385)
                ·
                  refine ⟨4176426168610820014327789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5568568224814426685770385 4176426168610820014327789)
                  ·
                    refine ⟨1566159813229057505372921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4176426168610820014327789 1566159813229057505372921)
                    ·
                      refine ⟨1174619859921793129029691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566159813229057505372921 1174619859921793129029691)
                      ·
                        rfl

theorem cell23_2287564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2287564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287564 prefixEnd_2287564 := by exact prefixLift 2287564
  have htrace : WordTrace (prefixWord ++ tailWord_2287564) baseStart_2287564 baseEnd_2287564 := by
    simpa [prefixWord, tailWord_2287564, baseEnd_2287564] using wordTrace_append hprefix tailTrace_2287564
  have hstable : (prefixWord ++ tailWord_2287564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287564).length < 2 ^ (prefixWord ++ tailWord_2287564).sum := by decide
  have hdescent : baseEnd_2287564 < baseStart_2287564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287574 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2287574 : Nat := 118140960795 + 2287574 * 2 ^ 59
def prefixEnd_2287574 : Nat := 4983230072969 + 3 ^ 40 * 2287574 * 2
def baseEnd_2287574 : Nat := 391541664909446029968215

theorem tailTrace_2287574 : CollatzResearch.WordTrace tailWord_2287574 prefixEnd_2287574 391541664909446029968215 := by
  unfold tailWord_2287574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214667388407347461260361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55623118809678372920110517 5214667388407347461260361)
  ·
    refine ⟨3911000541305510595945271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214667388407347461260361 3911000541305510595945271)
    ·
      refine ⟨5866500811958265893917907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911000541305510595945271 5866500811958265893917907)
      ·
        refine ⟨8799751217937398840876861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866500811958265893917907 8799751217937398840876861)
        ·
          refine ⟨3299906706726524565328823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8799751217937398840876861 3299906706726524565328823)
          ·
            refine ⟨4949860060089786847993235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299906706726524565328823 4949860060089786847993235)
            ·
              refine ⟨7424790090134680271989853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949860060089786847993235 7424790090134680271989853)
              ·
                refine ⟨2784296283800505101996195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7424790090134680271989853 2784296283800505101996195)
                ·
                  refine ⟨4176444425700757652994293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784296283800505101996195 4176444425700757652994293)
                  ·
                    refine ⟨391541664909446029968215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4176444425700757652994293 391541664909446029968215)
                    ·
                      rfl

theorem cell23_2287574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2287574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287574 prefixEnd_2287574 := by exact prefixLift 2287574
  have htrace : WordTrace (prefixWord ++ tailWord_2287574) baseStart_2287574 baseEnd_2287574 := by
    simpa [prefixWord, tailWord_2287574, baseEnd_2287574] using wordTrace_append hprefix tailTrace_2287574
  have hstable : (prefixWord ++ tailWord_2287574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287574).length < 2 ^ (prefixWord ++ tailWord_2287574).sum := by decide
  have hdescent : baseEnd_2287574 < baseStart_2287574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287577 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_2287577 : Nat := 118140960795 + 2287577 * 2 ^ 59
def prefixEnd_2287577 : Nat := 4983230072969 + 3 ^ 40 * 2287577 * 2
def baseEnd_2287577 : Nat := 1174626535170301578167131

theorem tailTrace_2287577 : CollatzResearch.WordTrace tailWord_2287577 prefixEnd_2287577 1174626535170301578167131 := by
  unfold tailWord_2287577
  simp only [CollatzResearch.WordTrace]
  refine ⟨83434787633506690892524985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55623191755671127261683323 83434787633506690892524985)
  ·
    refine ⟨62576090725130018169393739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83434787633506690892524985 62576090725130018169393739)
    ·
      refine ⟨93864136087695027254090609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62576090725130018169393739 93864136087695027254090609)
      ·
        refine ⟨70398102065771270440567957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93864136087695027254090609 70398102065771270440567957)
        ·
          refine ⟨3299911034333028301901623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70398102065771270440567957 3299911034333028301901623)
          ·
            refine ⟨4949866551499542452852435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299911034333028301901623 4949866551499542452852435)
            ·
              refine ⟨7424799827249313679278653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949866551499542452852435 7424799827249313679278653)
              ·
                refine ⟨2784299935218492629729495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7424799827249313679278653 2784299935218492629729495)
                ·
                  refine ⟨4176449902827738944594243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784299935218492629729495 4176449902827738944594243)
                  ·
                    refine ⟨6264674854241608416891365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176449902827738944594243 6264674854241608416891365)
                    ·
                      refine ⟨1174626535170301578167131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6264674854241608416891365 1174626535170301578167131)
                      ·
                        rfl

theorem cell23_2287577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_2287577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287577 prefixEnd_2287577 := by exact prefixLift 2287577
  have htrace : WordTrace (prefixWord ++ tailWord_2287577) baseStart_2287577 baseEnd_2287577 := by
    simpa [prefixWord, tailWord_2287577, baseEnd_2287577] using wordTrace_append hprefix tailTrace_2287577
  have hstable : (prefixWord ++ tailWord_2287577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287577).length < 2 ^ (prefixWord ++ tailWord_2287577).sum := by decide
  have hdescent : baseEnd_2287577 < baseStart_2287577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287583 : List Nat := [1, 1, 2, 3, 4, 2, 10]
def baseStart_2287583 : Nat := 118140960795 + 2287583 * 2 ^ 59
def prefixEnd_2287583 : Nat := 4983230072969 + 3 ^ 40 * 2287583 * 2
def baseEnd_2287583 : Nat := 14501600198200352527063

theorem tailTrace_2287583 : CollatzResearch.WordTrace tailWord_2287583 prefixEnd_2287583 14501600198200352527063 := by
  unfold tailWord_2287583
  simp only [CollatzResearch.WordTrace]
  refine ⟨83435006471484953917243403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55623337647656635944828935 83435006471484953917243403)
  ·
    refine ⟨125152509707227430875865105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83435006471484953917243403 125152509707227430875865105)
    ·
      refine ⟨93864382280420573156898829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125152509707227430875865105 93864382280420573156898829)
      ·
        refine ⟨35199143355157714933837061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93864382280420573156898829 35199143355157714933837061)
        ·
          refine ⟨6599839379092071550094449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35199143355157714933837061 6599839379092071550094449)
          ·
            refine ⟨4949879534319053662570837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6599839379092071550094449 4949879534319053662570837)
            ·
              refine ⟨14501600198200352527063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4949879534319053662570837 14501600198200352527063)
              ·
                rfl

theorem cell23_2287583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 10].length) (baseStart_2287583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287583 prefixEnd_2287583 := by exact prefixLift 2287583
  have htrace : WordTrace (prefixWord ++ tailWord_2287583) baseStart_2287583 baseEnd_2287583 := by
    simpa [prefixWord, tailWord_2287583, baseEnd_2287583] using wordTrace_append hprefix tailTrace_2287583
  have hstable : (prefixWord ++ tailWord_2287583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287583).length < 2 ^ (prefixWord ++ tailWord_2287583).sum := by decide
  have hdescent : baseEnd_2287583 < baseStart_2287583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287587 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 2, 4]
def baseStart_2287587 : Nat := 118140960795 + 2287587 * 2 ^ 59
def prefixEnd_2287587 : Nat := 4983230072969 + 3 ^ 40 * 2287587 * 2
def baseEnd_2287587 : Nat := 391543889992282179680695

theorem tailTrace_2287587 : CollatzResearch.WordTrace tailWord_2287587 prefixEnd_2287587 391543889992282179680695 := by
  unfold tailWord_2287587
  simp only [CollatzResearch.WordTrace]
  refine ⟨83435152363470462600389015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55623434908980308400259343 83435152363470462600389015)
  ·
    refine ⟨125152728545205693900583523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83435152363470462600389015 125152728545205693900583523)
    ·
      refine ⟨187729092817808540850875285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125152728545205693900583523 187729092817808540850875285)
      ·
        refine ⟨8799801225834775352384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187729092817808540850875285 8799801225834775352384779)
        ·
          refine ⟨13199701838752163028577169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799801225834775352384779 13199701838752163028577169)
          ·
            refine ⟨9899776379064122271432877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13199701838752163028577169 9899776379064122271432877)
            ·
              refine ⟨3712416142149045851787329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9899776379064122271432877 3712416142149045851787329)
              ·
                refine ⟨2784312106611784388840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712416142149045851787329 2784312106611784388840497)
                ·
                  refine ⟨2088234079958838291630373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2784312106611784388840497 2088234079958838291630373)
                  ·
                    refine ⟨391543889992282179680695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088234079958838291630373 391543889992282179680695)
                    ·
                      rfl

theorem cell23_2287587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 4].length) (baseStart_2287587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287587 prefixEnd_2287587 := by exact prefixLift 2287587
  have htrace : WordTrace (prefixWord ++ tailWord_2287587) baseStart_2287587 baseEnd_2287587 := by
    simpa [prefixWord, tailWord_2287587, baseEnd_2287587] using wordTrace_append hprefix tailTrace_2287587
  have hstable : (prefixWord ++ tailWord_2287587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287587).length < 2 ^ (prefixWord ++ tailWord_2287587).sum := by decide
  have hdescent : baseEnd_2287587 < baseStart_2287587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287593 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_2287593 : Nat := 118140960795 + 2287593 * 2 ^ 59
def prefixEnd_2287593 : Nat := 4983230072969 + 3 ^ 40 * 2287593 * 2
def baseEnd_2287593 : Nat := 1174634750860773515567057

theorem tailTrace_2287593 : CollatzResearch.WordTrace tailWord_2287593 prefixEnd_2287593 1174634750860773515567057 := by
  unfold tailWord_2287593
  simp only [CollatzResearch.WordTrace]
  refine ⟨83435371201448725625107433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55623580800965817083404955 83435371201448725625107433)
  ·
    refine ⟨62576528401086544218830575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83435371201448725625107433 62576528401086544218830575)
    ·
      refine ⟨93864792601629816328245863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62576528401086544218830575 93864792601629816328245863)
      ·
        refine ⟨140797188902444724492368795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93864792601629816328245863 140797188902444724492368795)
        ·
          refine ⟨211195783353667086738553193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140797188902444724492368795 211195783353667086738553193)
          ·
            refine ⟨158396837515250315053914895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211195783353667086738553193 158396837515250315053914895)
            ·
              refine ⟨237595256272875472580872343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158396837515250315053914895 237595256272875472580872343)
              ·
                refine ⟨356392884409313208871308515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237595256272875472580872343 356392884409313208871308515)
                ·
                  refine ⟨534589326613969813306962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356392884409313208871308515 534589326613969813306962773)
                  ·
                    refine ⟨3132359335628729374845485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 534589326613969813306962773 3132359335628729374845485)
                    ·
                      refine ⟨1174634750860773515567057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132359335628729374845485 1174634750860773515567057)
                      ·
                        rfl

theorem cell23_2287593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_2287593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287593 prefixEnd_2287593 := by exact prefixLift 2287593
  have htrace : WordTrace (prefixWord ++ tailWord_2287593) baseStart_2287593 baseEnd_2287593 := by
    simpa [prefixWord, tailWord_2287593, baseEnd_2287593] using wordTrace_append hprefix tailTrace_2287593
  have hstable : (prefixWord ++ tailWord_2287593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287593).length < 2 ^ (prefixWord ++ tailWord_2287593).sum := by decide
  have hdescent : baseEnd_2287593 < baseStart_2287593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287594 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_2287594 : Nat := 118140960795 + 2287594 * 2 ^ 59
def prefixEnd_2287594 : Nat := 4983230072969 + 3 ^ 40 * 2287594 * 2
def baseEnd_2287594 : Nat := 1174635264341428011654553

theorem tailTrace_2287594 : CollatzResearch.WordTrace tailWord_2287594 prefixEnd_2287594 1174635264341428011654553 := by
  unfold tailWord_2287594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858851918611275698973459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55623605116296735197262557 20858851918611275698973459)
  ·
    refine ⟨31288277877916913548460189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858851918611275698973459 31288277877916913548460189)
    ·
      refine ⟨11733104204218842580672571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31288277877916913548460189 11733104204218842580672571)
      ·
        refine ⟨17599656306328263871008857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733104204218842580672571 17599656306328263871008857)
        ·
          refine ⟨13199742229746197903256643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17599656306328263871008857 13199742229746197903256643)
          ·
            refine ⟨19799613344619296854884965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13199742229746197903256643 19799613344619296854884965)
            ·
              refine ⟨3712427502116118160290931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19799613344619296854884965 3712427502116118160290931)
              ·
                refine ⟨5568641253174177240436397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712427502116118160290931 5568641253174177240436397)
                ·
                  refine ⟨2088240469940316465163649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5568641253174177240436397 2088240469940316465163649)
                  ·
                    refine ⟨1566180352455237348872737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088240469940316465163649 1566180352455237348872737)
                    ·
                      refine ⟨1174635264341428011654553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566180352455237348872737 1174635264341428011654553)
                      ·
                        rfl

theorem cell23_2287594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_2287594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287594 prefixEnd_2287594 := by exact prefixLift 2287594
  have htrace : WordTrace (prefixWord ++ tailWord_2287594) baseStart_2287594 baseEnd_2287594 := by
    simpa [prefixWord, tailWord_2287594, baseEnd_2287594] using wordTrace_append hprefix tailTrace_2287594
  have hstable : (prefixWord ++ tailWord_2287594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287594).length < 2 ^ (prefixWord ++ tailWord_2287594).sum := by decide
  have hdescent : baseEnd_2287594 < baseStart_2287594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287613 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2287613 : Nat := 118140960795 + 2287613 * 2 ^ 59
def prefixEnd_2287613 : Nat := 4983230072969 + 3 ^ 40 * 2287613 * 2
def baseEnd_2287613 : Nat := 391548340157954479105655

theorem tailTrace_2287613 : CollatzResearch.WordTrace tailWord_2287613 prefixEnd_2287613 391548340157954479105655 := by
  unfold tailWord_2287613
  simp only [CollatzResearch.WordTrace]
  refine ⟨83436100661376269040835493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55624067107584179360556995 83436100661376269040835493)
  ·
    refine ⟨15644268874008050445156655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83436100661376269040835493 15644268874008050445156655)
    ·
      refine ⟨23466403311012075667734983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15644268874008050445156655 23466403311012075667734983)
      ·
        refine ⟨35199604966518113501602475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23466403311012075667734983 35199604966518113501602475)
        ·
          refine ⟨52799407449777170252403713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35199604966518113501602475 52799407449777170252403713)
          ·
            refine ⟨39599555587332877689302785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52799407449777170252403713 39599555587332877689302785)
            ·
              refine ⟨29699666690499658266977089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39599555587332877689302785 29699666690499658266977089)
              ·
                refine ⟨22274750017874743700232817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29699666690499658266977089 22274750017874743700232817)
                ·
                  refine ⟨16706062513406057775174613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22274750017874743700232817 16706062513406057775174613)
                  ·
                    refine ⟨391548340157954479105655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16706062513406057775174613 391548340157954479105655)
                    ·
                      rfl

theorem cell23_2287613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2287613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287613 prefixEnd_2287613 := by exact prefixLift 2287613
  have htrace : WordTrace (prefixWord ++ tailWord_2287613) baseStart_2287613 baseEnd_2287613 := by
    simpa [prefixWord, tailWord_2287613, baseEnd_2287613] using wordTrace_append hprefix tailTrace_2287613
  have hstable : (prefixWord ++ tailWord_2287613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287613).length < 2 ^ (prefixWord ++ tailWord_2287613).sum := by decide
  have hdescent : baseEnd_2287613 < baseStart_2287613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287614 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2287614 : Nat := 118140960795 + 2287614 * 2 ^ 59
def prefixEnd_2287614 : Nat := 4983230072969 + 3 ^ 40 * 2287614 * 2
def baseEnd_2287614 : Nat := 1174645533954517933404461

theorem tailTrace_2287614 : CollatzResearch.WordTrace tailWord_2287614 prefixEnd_2287614 1174645533954517933404461 := by
  unfold tailWord_2287614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429517141796580776452737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55624091422915097474414597 10429517141796580776452737)
  ·
    refine ⟨7822137856347435582339553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10429517141796580776452737 7822137856347435582339553)
    ·
      refine ⟨5866603392260576686754665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7822137856347435582339553 5866603392260576686754665)
      ·
        refine ⟨4399952544195432515065999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866603392260576686754665 4399952544195432515065999)
        ·
          refine ⟨6599928816293148772598999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399952544195432515065999 6599928816293148772598999)
          ·
            refine ⟨9899893224439723158898499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599928816293148772598999 9899893224439723158898499)
            ·
              refine ⟨14849839836659584738347749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899893224439723158898499 14849839836659584738347749)
              ·
                refine ⟨2784344969373672138440203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14849839836659584738347749 2784344969373672138440203)
                ·
                  refine ⟨4176517454060508207660305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784344969373672138440203 4176517454060508207660305)
                  ·
                    refine ⟨3132388090545381155745229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176517454060508207660305 3132388090545381155745229)
                    ·
                      refine ⟨1174645533954517933404461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132388090545381155745229 1174645533954517933404461)
                      ·
                        rfl

theorem cell23_2287614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2287614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287614 prefixEnd_2287614 := by exact prefixLift 2287614
  have htrace : WordTrace (prefixWord ++ tailWord_2287614) baseStart_2287614 baseEnd_2287614 := by
    simpa [prefixWord, tailWord_2287614, baseEnd_2287614] using wordTrace_append hprefix tailTrace_2287614
  have hstable : (prefixWord ++ tailWord_2287614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287614).length < 2 ^ (prefixWord ++ tailWord_2287614).sum := by decide
  have hdescent : baseEnd_2287614 < baseStart_2287614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287633 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2287633 : Nat := 118140960795 + 2287633 * 2 ^ 59
def prefixEnd_2287633 : Nat := 4983230072969 + 3 ^ 40 * 2287633 * 2
def baseEnd_2287633 : Nat := 1174655290086953359066873

theorem tailTrace_2287633 : CollatzResearch.WordTrace tailWord_2287633 prefixEnd_2287633 1174655290086953359066873 := by
  unfold tailWord_2287633
  simp only [CollatzResearch.WordTrace]
  refine ⟨83436830121303812456563553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55624553414202541637709035 83436830121303812456563553)
  ·
    refine ⟨62577622590977859342422665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83436830121303812456563553 62577622590977859342422665)
    ·
      refine ⟨46933216943233394506816999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62577622590977859342422665 46933216943233394506816999)
      ·
        refine ⟨70399825414850091760225499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46933216943233394506816999 70399825414850091760225499)
        ·
          refine ⟨105599738122275137640338249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70399825414850091760225499 105599738122275137640338249)
          ·
            refine ⟨79199803591706353230253687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105599738122275137640338249 79199803591706353230253687)
            ·
              refine ⟨118799705387559529845380531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79199803591706353230253687 118799705387559529845380531)
              ·
                refine ⟨178199558081339294768070797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118799705387559529845380531 178199558081339294768070797)
                ·
                  refine ⟨66824834280502235538026549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178199558081339294768070797 66824834280502235538026549)
                  ·
                    refine ⟨6264828213797084581689989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66824834280502235538026549 6264828213797084581689989)
                    ·
                      refine ⟨1174655290086953359066873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6264828213797084581689989 1174655290086953359066873)
                      ·
                        rfl

theorem cell23_2287633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2287633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287633 prefixEnd_2287633 := by exact prefixLift 2287633
  have htrace : WordTrace (prefixWord ++ tailWord_2287633) baseStart_2287633 baseEnd_2287633 := by
    simpa [prefixWord, tailWord_2287633, baseEnd_2287633] using wordTrace_append hprefix tailTrace_2287633
  have hstable : (prefixWord ++ tailWord_2287633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287633).length < 2 ^ (prefixWord ++ tailWord_2287633).sum := by decide
  have hdescent : baseEnd_2287633 < baseStart_2287633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287643 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 6]
def baseStart_2287643 : Nat := 118140960795 + 2287643 * 2 ^ 59
def prefixEnd_2287643 : Nat := 4983230072969 + 3 ^ 40 * 2287643 * 2
def baseEnd_2287643 : Nat := 391553474964499439980609

theorem tailTrace_2287643 : CollatzResearch.WordTrace tailWord_2287643 prefixEnd_2287643 391553474964499439980609 := by
  unfold tailWord_2287643
  simp only [CollatzResearch.WordTrace]
  refine ⟨83437194851267584164427583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55624796567511722776285055 83437194851267584164427583)
  ·
    refine ⟨125155792276901376246641375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83437194851267584164427583 125155792276901376246641375)
    ·
      refine ⟨187733688415352064369962063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125155792276901376246641375 187733688415352064369962063)
      ·
        refine ⟨281600532623028096554943095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187733688415352064369962063 281600532623028096554943095)
        ·
          refine ⟨422400798934542144832414643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281600532623028096554943095 422400798934542144832414643)
          ·
            refine ⟨633601198401813217248621965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422400798934542144832414643 633601198401813217248621965)
            ·
              refine ⟨237600449400679956468233237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633601198401813217248621965 237600449400679956468233237)
              ·
                refine ⟨11137521065656872959448433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237600449400679956468233237 11137521065656872959448433)
                ·
                  refine ⟨8353140799242654719586325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11137521065656872959448433 8353140799242654719586325)
                  ·
                    refine ⟨391553474964499439980609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8353140799242654719586325 391553474964499439980609)
                    ·
                      rfl

theorem cell23_2287643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_2287643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287643 prefixEnd_2287643 := by exact prefixLift 2287643
  have htrace : WordTrace (prefixWord ++ tailWord_2287643) baseStart_2287643 baseEnd_2287643 := by
    simpa [prefixWord, tailWord_2287643, baseEnd_2287643] using wordTrace_append hprefix tailTrace_2287643
  have hstable : (prefixWord ++ tailWord_2287643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287643).length < 2 ^ (prefixWord ++ tailWord_2287643).sum := by decide
  have hdescent : baseEnd_2287643 < baseStart_2287643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287650 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2287650 : Nat := 118140960795 + 2287650 * 2 ^ 59
def prefixEnd_2287650 : Nat := 4983230072969 + 3 ^ 40 * 2287650 * 2
def baseEnd_2287650 : Nat := 1174664019258079792554295

theorem tailTrace_2287650 : CollatzResearch.WordTrace tailWord_2287650 prefixEnd_2287650 1174664019258079792554295 := by
  unfold tailWord_2287650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859362540560556089983101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55624966774828149573288269 20859362540560556089983101)
  ·
    refine ⟨7822260952710208533743663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20859362540560556089983101 7822260952710208533743663)
    ·
      refine ⟨11733391429065312800615495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7822260952710208533743663 11733391429065312800615495)
      ·
        refine ⟨17600087143597969200923243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733391429065312800615495 17600087143597969200923243)
        ·
          refine ⟨26400130715396953801384865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17600087143597969200923243 26400130715396953801384865)
          ·
            refine ⟨19800098036547715351038649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26400130715396953801384865 19800098036547715351038649)
            ·
              refine ⟨14850073527410786513278987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19800098036547715351038649 14850073527410786513278987)
              ·
                refine ⟨22275110291116179769918481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14850073527410786513278987 22275110291116179769918481)
                ·
                  refine ⟨16706332718337134827438861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22275110291116179769918481 16706332718337134827438861)
                  ·
                    refine ⟨6264874769376425560289573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16706332718337134827438861 6264874769376425560289573)
                    ·
                      refine ⟨1174664019258079792554295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6264874769376425560289573 1174664019258079792554295)
                      ·
                        rfl

theorem cell23_2287650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2287650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287650 prefixEnd_2287650 := by exact prefixLift 2287650
  have htrace : WordTrace (prefixWord ++ tailWord_2287650) baseStart_2287650 baseEnd_2287650 := by
    simpa [prefixWord, tailWord_2287650, baseEnd_2287650] using wordTrace_append hprefix tailTrace_2287650
  have hstable : (prefixWord ++ tailWord_2287650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287650).length < 2 ^ (prefixWord ++ tailWord_2287650).sum := by decide
  have hdescent : baseEnd_2287650 < baseStart_2287650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2287683 : Nat := 118140960795 + 2287683 * 2 ^ 59
def prefixEnd_2287683 : Nat := 4983230072969 + 3 ^ 40 * 2287683 * 2
def baseEnd_2287683 : Nat := 1174680964119678163441643

theorem tailTrace_2287683 : CollatzResearch.WordTrace tailWord_2287683 prefixEnd_2287683 1174680964119678163441643 := by
  unfold tailWord_2287683
  simp only [CollatzResearch.WordTrace]
  refine ⟨83438653771122670995883703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55625769180748447330589135 83438653771122670995883703)
  ·
    refine ⟨125157980656684006493825555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83438653771122670995883703 125157980656684006493825555)
    ·
      refine ⟨187736970985026009740738333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125157980656684006493825555 187736970985026009740738333)
      ·
        refine ⟨70401364119384753652776875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187736970985026009740738333 70401364119384753652776875)
        ·
          refine ⟨105602046179077130479165313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70401364119384753652776875 105602046179077130479165313)
          ·
            refine ⟨79201534634307847859373985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105602046179077130479165313 79201534634307847859373985)
            ·
              refine ⟨59401150975730885894530489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79201534634307847859373985 59401150975730885894530489)
              ·
                refine ⟨44550863231798164420897867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59401150975730885894530489 44550863231798164420897867)
                ·
                  refine ⟨66826294847697246631346801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44550863231798164420897867 66826294847697246631346801)
                  ·
                    refine ⟨50119721135772934973510101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66826294847697246631346801 50119721135772934973510101)
                    ·
                      refine ⟨1174680964119678163441643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50119721135772934973510101 1174680964119678163441643)
                      ·
                        rfl

theorem cell23_2287683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2287683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287683 prefixEnd_2287683 := by exact prefixLift 2287683
  have htrace : WordTrace (prefixWord ++ tailWord_2287683) baseStart_2287683 baseEnd_2287683 := by
    simpa [prefixWord, tailWord_2287683, baseEnd_2287683] using wordTrace_append hprefix tailTrace_2287683
  have hstable : (prefixWord ++ tailWord_2287683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287683).length < 2 ^ (prefixWord ++ tailWord_2287683).sum := by decide
  have hdescent : baseEnd_2287683 < baseStart_2287683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287701 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2287701 : Nat := 118140960795 + 2287701 * 2 ^ 59
def prefixEnd_2287701 : Nat := 4983230072969 + 3 ^ 40 * 2287701 * 2
def baseEnd_2287701 : Nat := 1174690206771459093016561

theorem tailTrace_2287701 : CollatzResearch.WordTrace tailWord_2287701 prefixEnd_2287701 1174690206771459093016561 := by
  unfold tailWord_2287701
  simp only [CollatzResearch.WordTrace]
  refine ⟨83439310285057460070038957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55626206856704973380025971 83439310285057460070038957)
  ·
    refine ⟨31289741356896547526264609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83439310285057460070038957 31289741356896547526264609)
    ·
      refine ⟨23467306017672410644698457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31289741356896547526264609 23467306017672410644698457)
      ·
        refine ⟨17600479513254307983523843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23467306017672410644698457 17600479513254307983523843)
        ·
          refine ⟨26400719269881461975285765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17600479513254307983523843 26400719269881461975285765)
          ·
            refine ⟨4950134863102774120366081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26400719269881461975285765 4950134863102774120366081)
            ·
              refine ⟨3712601147327080590274561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950134863102774120366081 3712601147327080590274561)
              ·
                refine ⟨2784450860495310442705921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712601147327080590274561 2784450860495310442705921)
                ·
                  refine ⟨2088338145371482832029441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2784450860495310442705921 2088338145371482832029441)
                  ·
                    refine ⟨1566253609028612124022081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088338145371482832029441 1566253609028612124022081)
                    ·
                      refine ⟨1174690206771459093016561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566253609028612124022081 1174690206771459093016561)
                      ·
                        rfl

theorem cell23_2287701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2287701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287701 prefixEnd_2287701 := by exact prefixLift 2287701
  have htrace : WordTrace (prefixWord ++ tailWord_2287701) baseStart_2287701 baseEnd_2287701 := by
    simpa [prefixWord, tailWord_2287701, baseEnd_2287701] using wordTrace_append hprefix tailTrace_2287701
  have hstable : (prefixWord ++ tailWord_2287701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287701).length < 2 ^ (prefixWord ++ tailWord_2287701).sum := by decide
  have hdescent : baseEnd_2287701 < baseStart_2287701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287714 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2287714 : Nat := 118140960795 + 2287714 * 2 ^ 59
def prefixEnd_2287714 : Nat := 4983230072969 + 3 ^ 40 * 2287714 * 2
def baseEnd_2287714 : Nat := 1174696882019967542154001

theorem tailTrace_2287714 : CollatzResearch.WordTrace tailWord_2287714 prefixEnd_2287714 1174696882019967542154001 := by
  unfold tailWord_2287714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859946108502590822565549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55626522956006908860174797 20859946108502590822565549)
  ·
    refine ⟨7822479790688471558462081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20859946108502590822565549 7822479790688471558462081)
    ·
      refine ⟨5866859843016353668846561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7822479790688471558462081 5866859843016353668846561)
      ·
        refine ⟨4400144882262265251634921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866859843016353668846561 4400144882262265251634921)
        ·
          refine ⟨3300108661696698938726191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400144882262265251634921 3300108661696698938726191)
          ·
            refine ⟨4950162992545048408089287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300108661696698938726191 4950162992545048408089287)
            ·
              refine ⟨7425244488817572612133931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950162992545048408089287 7425244488817572612133931)
              ·
                refine ⟨11137866733226358918200897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7425244488817572612133931 11137866733226358918200897)
                ·
                  refine ⟨8353400049919769188650673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11137866733226358918200897 8353400049919769188650673)
                  ·
                    refine ⟨6265050037439826891488005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8353400049919769188650673 6265050037439826891488005)
                    ·
                      refine ⟨1174696882019967542154001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6265050037439826891488005 1174696882019967542154001)
                      ·
                        rfl

theorem cell23_2287714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2287714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287714 prefixEnd_2287714 := by exact prefixLift 2287714
  have htrace : WordTrace (prefixWord ++ tailWord_2287714) baseStart_2287714 baseEnd_2287714 := by
    simpa [prefixWord, tailWord_2287714, baseEnd_2287714] using wordTrace_append hprefix tailTrace_2287714
  have hstable : (prefixWord ++ tailWord_2287714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287714).length < 2 ^ (prefixWord ++ tailWord_2287714).sum := by decide
  have hdescent : baseEnd_2287714 < baseStart_2287714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287717 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2287717 : Nat := 118140960795 + 2287717 * 2 ^ 59
def prefixEnd_2287717 : Nat := 4983230072969 + 3 ^ 40 * 2287717 * 2
def baseEnd_2287717 : Nat := 1174698422461931030416487

theorem tailTrace_2287717 : CollatzResearch.WordTrace tailWord_2287717 prefixEnd_2287717 1174698422461931030416487 := by
  unfold tailWord_2287717
  simp only [CollatzResearch.WordTrace]
  refine ⟨83439893852999494802621405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55626595901999663201747603 83439893852999494802621405)
  ·
    refine ⟨31289960194874810550983027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83439893852999494802621405 31289960194874810550983027)
    ·
      refine ⟨46934940292312215826474541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31289960194874810550983027 46934940292312215826474541)
      ·
        refine ⟨17600602609617080934927953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46934940292312215826474541 17600602609617080934927953)
        ·
          refine ⟨13200451957212810701195965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17600602609617080934927953 13200451957212810701195965)
          ·
            refine ⟨4950169483954804012948487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13200451957212810701195965 4950169483954804012948487)
            ·
              refine ⟨7425254225932206019422731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950169483954804012948487 7425254225932206019422731)
              ·
                refine ⟨11137881338898309029134097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7425254225932206019422731 11137881338898309029134097)
                ·
                  refine ⟨8353411004173731771850573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11137881338898309029134097 8353411004173731771850573)
                  ·
                    refine ⟨3132529126565149414443965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8353411004173731771850573 3132529126565149414443965)
                    ·
                      refine ⟨1174698422461931030416487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132529126565149414443965 1174698422461931030416487)
                      ·
                        rfl

theorem cell23_2287717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2287717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287717 prefixEnd_2287717 := by exact prefixLift 2287717
  have htrace : WordTrace (prefixWord ++ tailWord_2287717) baseStart_2287717 baseEnd_2287717 := by
    simpa [prefixWord, tailWord_2287717, baseEnd_2287717] using wordTrace_append hprefix tailTrace_2287717
  have hstable : (prefixWord ++ tailWord_2287717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287717).length < 2 ^ (prefixWord ++ tailWord_2287717).sum := by decide
  have hdescent : baseEnd_2287717 < baseStart_2287717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287737 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_2287737 : Nat := 118140960795 + 2287737 * 2 ^ 59
def prefixEnd_2287737 : Nat := 4983230072969 + 3 ^ 40 * 2287737 * 2
def baseEnd_2287737 : Nat := 391569564025006984055465

theorem tailTrace_2287737 : CollatzResearch.WordTrace tailWord_2287737 prefixEnd_2287737 391569564025006984055465 := by
  unfold tailWord_2287737
  simp only [CollatzResearch.WordTrace]
  refine ⟨83440623312927038218349465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55627082208618025478899643 83440623312927038218349465)
  ·
    refine ⟨62580467484695278663762099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83440623312927038218349465 62580467484695278663762099)
    ·
      refine ⟨93870701227042917995643149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62580467484695278663762099 93870701227042917995643149)
      ·
        refine ⟨35201512960141094248366181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93870701227042917995643149 35201512960141094248366181)
        ·
          refine ⟨6600283680026455171568659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35201512960141094248366181 6600283680026455171568659)
          ·
            refine ⟨9900425520039682757352989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6600283680026455171568659 9900425520039682757352989)
            ·
              refine ⟨3712659570014881034007371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9900425520039682757352989 3712659570014881034007371)
              ·
                refine ⟨5568989355022321551011057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712659570014881034007371 5568989355022321551011057)
                ·
                  refine ⟨4176742016266741163258293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5568989355022321551011057 4176742016266741163258293)
                  ·
                    refine ⟨391569564025006984055465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4176742016266741163258293 391569564025006984055465)
                    ·
                      rfl

theorem cell23_2287737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_2287737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287737 prefixEnd_2287737 := by exact prefixLift 2287737
  have htrace : WordTrace (prefixWord ++ tailWord_2287737) baseStart_2287737 baseEnd_2287737 := by
    simpa [prefixWord, tailWord_2287737, baseEnd_2287737] using wordTrace_append hprefix tailTrace_2287737
  have hstable : (prefixWord ++ tailWord_2287737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287737).length < 2 ^ (prefixWord ++ tailWord_2287737).sum := by decide
  have hdescent : baseEnd_2287737 < baseStart_2287737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287777 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2287777 : Nat := 118140960795 + 2287777 * 2 ^ 59
def prefixEnd_2287777 : Nat := 4983230072969 + 3 ^ 40 * 2287777 * 2
def baseEnd_2287777 : Nat := 1174729231301200795666211

theorem tailTrace_2287777 : CollatzResearch.WordTrace tailWord_2287777 prefixEnd_2287777 1174729231301200795666211 := by
  unfold tailWord_2287777
  simp only [CollatzResearch.WordTrace]
  refine ⟨83442082232782125049805585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55628054821854750033203723 83442082232782125049805585)
  ·
    refine ⟨62581561674586593787354189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83442082232782125049805585 62581561674586593787354189)
    ·
      refine ⟨23468085627969972670257821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62581561674586593787354189 23468085627969972670257821)
      ·
        refine ⟨8800532110488739751346683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23468085627969972670257821 8800532110488739751346683)
        ·
          refine ⟨13200798165733109627020025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800532110488739751346683 13200798165733109627020025)
          ·
            refine ⟨9900598624299832220265019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13200798165733109627020025 9900598624299832220265019)
            ·
              refine ⟨14850897936449748330397529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9900598624299832220265019 14850897936449748330397529)
              ·
                refine ⟨11138173452337311247798147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14850897936449748330397529 11138173452337311247798147)
                ·
                  refine ⟨16707260178505966871697221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11138173452337311247798147 16707260178505966871697221)
                  ·
                    refine ⟨3132611283469868788443229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16707260178505966871697221 3132611283469868788443229)
                    ·
                      refine ⟨1174729231301200795666211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132611283469868788443229 1174729231301200795666211)
                      ·
                        rfl

theorem cell23_2287777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2287777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287777 prefixEnd_2287777 := by exact prefixLift 2287777
  have htrace : WordTrace (prefixWord ++ tailWord_2287777) baseStart_2287777 baseEnd_2287777 := by
    simpa [prefixWord, tailWord_2287777, baseEnd_2287777] using wordTrace_append hprefix tailTrace_2287777
  have hstable : (prefixWord ++ tailWord_2287777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287777).length < 2 ^ (prefixWord ++ tailWord_2287777).sum := by decide
  have hdescent : baseEnd_2287777 < baseStart_2287777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287817 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 5, 2]
def baseStart_2287817 : Nat := 118140960795 + 2287817 * 2 ^ 59
def prefixEnd_2287817 : Nat := 4983230072969 + 3 ^ 40 * 2287817 * 2
def baseEnd_2287817 : Nat := 1174749770527380639166027

theorem tailTrace_2287817 : CollatzResearch.WordTrace tailWord_2287817 prefixEnd_2287817 1174749770527380639166027 := by
  unfold tailWord_2287817
  simp only [CollatzResearch.WordTrace]
  refine ⟨83443541152637211881261705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55629027435091474587507803 83443541152637211881261705)
  ·
    refine ⟨62582655864477908910946279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83443541152637211881261705 62582655864477908910946279)
    ·
      refine ⟨93873983796716863366419419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62582655864477908910946279 93873983796716863366419419)
      ·
        refine ⟨140810975695075295049629129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93873983796716863366419419 140810975695075295049629129)
        ·
          refine ⟨105608231771306471287221847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140810975695075295049629129 105608231771306471287221847)
          ·
            refine ⟨158412347656959706930832771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105608231771306471287221847 158412347656959706930832771)
            ·
              refine ⟨237618521485439560396249157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158412347656959706930832771 237618521485439560396249157)
              ·
                refine ⟨44553472778519917574296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237618521485439560396249157 44553472778519917574296717)
                ·
                  refine ⟨16707552291944969090361269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44553472778519917574296717 16707552291944969090361269)
                  ·
                    refine ⟨1566333027369840852221369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16707552291944969090361269 1566333027369840852221369)
                    ·
                      refine ⟨1174749770527380639166027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566333027369840852221369 1174749770527380639166027)
                      ·
                        rfl

theorem cell23_2287817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5, 2].length) (baseStart_2287817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287817 prefixEnd_2287817 := by exact prefixLift 2287817
  have htrace : WordTrace (prefixWord ++ tailWord_2287817) baseStart_2287817 baseEnd_2287817 := by
    simpa [prefixWord, tailWord_2287817, baseEnd_2287817] using wordTrace_append hprefix tailTrace_2287817
  have hstable : (prefixWord ++ tailWord_2287817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287817).length < 2 ^ (prefixWord ++ tailWord_2287817).sum := by decide
  have hdescent : baseEnd_2287817 < baseStart_2287817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287857 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_2287857 : Nat := 118140960795 + 2287857 * 2 ^ 59
def prefixEnd_2287857 : Nat := 4983230072969 + 3 ^ 40 * 2287857 * 2
def baseEnd_2287857 : Nat := 391590103251186827555281

theorem tailTrace_2287857 : CollatzResearch.WordTrace tailWord_2287857 prefixEnd_2287857 391590103251186827555281 := by
  unfold tailWord_2287857
  simp only [CollatzResearch.WordTrace]
  refine ⟨83445000072492298712717825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55630000048328199141811883 83445000072492298712717825)
  ·
    refine ⟨62583750054369224034538369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83445000072492298712717825 62583750054369224034538369)
    ·
      refine ⟨46937812540776918025903777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62583750054369224034538369 46937812540776918025903777)
      ·
        refine ⟨35203359405582688519427833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46937812540776918025903777 35203359405582688519427833)
        ·
          refine ⟨26402519554187016389570875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35203359405582688519427833 26402519554187016389570875)
          ·
            refine ⟨39603779331280524584356313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26402519554187016389570875 39603779331280524584356313)
            ·
              refine ⟨29702834498460393438267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39603779331280524584356313 29702834498460393438267235)
              ·
                refine ⟨44554251747690590157400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29702834498460393438267235 44554251747690590157400853)
                ·
                  refine ⟨2088480550672996413628165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44554251747690590157400853 2088480550672996413628165)
                  ·
                    refine ⟨391590103251186827555281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088480550672996413628165 391590103251186827555281)
                    ·
                      rfl

theorem cell23_2287857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_2287857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287857 prefixEnd_2287857 := by exact prefixLift 2287857
  have htrace : WordTrace (prefixWord ++ tailWord_2287857) baseStart_2287857 baseEnd_2287857 := by
    simpa [prefixWord, tailWord_2287857, baseEnd_2287857] using wordTrace_append hprefix tailTrace_2287857
  have hstable : (prefixWord ++ tailWord_2287857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287857).length < 2 ^ (prefixWord ++ tailWord_2287857).sum := by decide
  have hdescent : baseEnd_2287857 < baseStart_2287857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287898 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_2287898 : Nat := 118140960795 + 2287898 * 2 ^ 59
def prefixEnd_2287898 : Nat := 4983230072969 + 3 ^ 40 * 2287898 * 2
def baseEnd_2287898 : Nat := 1174791362460394822253155

theorem tailTrace_2287898 : CollatzResearch.WordTrace tailWord_2287898 prefixEnd_2287898 1174791362460394822253155 := by
  unfold tailWord_2287898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861623866335940678740087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55630996976895841809973565 20861623866335940678740087)
  ·
    refine ⟨31292435799503911018110131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20861623866335940678740087 31292435799503911018110131)
    ·
      refine ⟨46938653699255866527165197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31292435799503911018110131 46938653699255866527165197)
      ·
        refine ⟨17601995137220949947686949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46938653699255866527165197 17601995137220949947686949)
        ·
          refine ⟨3300374088228928115191303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17601995137220949947686949 3300374088228928115191303)
          ·
            refine ⟨4950561132343392172786955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300374088228928115191303 4950561132343392172786955)
            ·
              refine ⟨7425841698515088259180433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950561132343392172786955 7425841698515088259180433)
              ·
                refine ⟨5569381273886316194385325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7425841698515088259180433 5569381273886316194385325)
                ·
                  refine ⟨2088517977707368572894497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5569381273886316194385325 2088517977707368572894497)
                  ·
                    refine ⟨1566388483280526429670873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088517977707368572894497 1566388483280526429670873)
                    ·
                      refine ⟨1174791362460394822253155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566388483280526429670873 1174791362460394822253155)
                      ·
                        rfl

theorem cell23_2287898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_2287898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287898 prefixEnd_2287898 := by exact prefixLift 2287898
  have htrace : WordTrace (prefixWord ++ tailWord_2287898) baseStart_2287898 baseEnd_2287898 := by
    simpa [prefixWord, tailWord_2287898, baseEnd_2287898] using wordTrace_append hprefix tailTrace_2287898
  have hstable : (prefixWord ++ tailWord_2287898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287898).length < 2 ^ (prefixWord ++ tailWord_2287898).sum := by decide
  have hdescent : baseEnd_2287898 < baseStart_2287898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287904 : List Nat := [2, 1, 1, 5, 2, 2, 3, 7]
def baseStart_2287904 : Nat := 118140960795 + 2287904 * 2 ^ 59
def prefixEnd_2287904 : Nat := 4983230072969 + 3 ^ 40 * 2287904 * 2
def baseEnd_2287904 : Nat := 43510905309048955510301

theorem tailTrace_2287904 : CollatzResearch.WordTrace tailWord_2287904 prefixEnd_2287904 43510905309048955510301 := by
  unfold tailWord_2287904
  simp only [CollatzResearch.WordTrace]
  refine ⟨41723357151661012869839383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55631142868881350493119177 41723357151661012869839383)
  ·
    refine ⟨62585035727491519304759075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41723357151661012869839383 62585035727491519304759075)
    ·
      refine ⟨93877553591237278957138613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62585035727491519304759075 93877553591237278957138613)
      ·
        refine ⟨8801020649178494902231745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93877553591237278957138613 8801020649178494902231745)
        ·
          refine ⟨6600765486883871176673809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8801020649178494902231745 6600765486883871176673809)
          ·
            refine ⟨4950574115162903382505357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6600765486883871176673809 4950574115162903382505357)
            ·
              refine ⟨1856465293186088768439509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4950574115162903382505357 1856465293186088768439509)
              ·
                refine ⟨43510905309048955510301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1856465293186088768439509 43510905309048955510301)
                ·
                  rfl

theorem cell23_2287904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 7].length) (baseStart_2287904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287904 prefixEnd_2287904 := by exact prefixLift 2287904
  have htrace : WordTrace (prefixWord ++ tailWord_2287904) baseStart_2287904 baseEnd_2287904 := by
    simpa [prefixWord, tailWord_2287904, baseEnd_2287904] using wordTrace_append hprefix tailTrace_2287904
  have hstable : (prefixWord ++ tailWord_2287904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287904).length < 2 ^ (prefixWord ++ tailWord_2287904).sum := by decide
  have hdescent : baseEnd_2287904 < baseStart_2287904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287948 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2287948 : Nat := 118140960795 + 2287948 * 2 ^ 59
def prefixEnd_2287948 : Nat := 4983230072969 + 3 ^ 40 * 2287948 * 2
def baseEnd_2287948 : Nat := 1174817036493119626627925

theorem tailTrace_2287948 : CollatzResearch.WordTrace tailWord_2287948 prefixEnd_2287948 1174817036493119626627925 := by
  unfold tailWord_2287948
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724159557581310627140249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55632212743441747502853665 41724159557581310627140249)
  ·
    refine ⟨31293119668185982970355187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41724159557581310627140249 31293119668185982970355187)
    ·
      refine ⟨46939679502278974455532781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31293119668185982970355187 46939679502278974455532781)
      ·
        refine ⟨17602379813354615420824793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46939679502278974455532781 17602379813354615420824793)
        ·
          refine ⟨13201784860015961565618595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17602379813354615420824793 13201784860015961565618595)
          ·
            refine ⟨19802677290023942348427893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13201784860015961565618595 19802677290023942348427893)
            ·
              refine ⟨1856500995939744595165115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19802677290023942348427893 1856500995939744595165115)
              ·
                refine ⟨2784751493909616892747673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856500995939744595165115 2784751493909616892747673)
                ·
                  refine ⟨2088563620432212669560755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2784751493909616892747673 2088563620432212669560755)
                  ·
                    refine ⟨3132845430648319004341133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2088563620432212669560755 3132845430648319004341133)
                    ·
                      refine ⟨1174817036493119626627925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132845430648319004341133 1174817036493119626627925)
                      ·
                        rfl

theorem cell23_2287948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2287948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287948 prefixEnd_2287948 := by exact prefixLift 2287948
  have htrace : WordTrace (prefixWord ++ tailWord_2287948) baseStart_2287948 baseEnd_2287948 := by
    simpa [prefixWord, tailWord_2287948, baseEnd_2287948] using wordTrace_append hprefix tailTrace_2287948
  have hstable : (prefixWord ++ tailWord_2287948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287948).length < 2 ^ (prefixWord ++ tailWord_2287948).sum := by decide
  have hdescent : baseEnd_2287948 < baseStart_2287948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287967 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2287967 : Nat := 118140960795 + 2287967 * 2 ^ 59
def prefixEnd_2287967 : Nat := 4983230072969 + 3 ^ 40 * 2287967 * 2
def baseEnd_2287967 : Nat := 1174826792625555052290337

theorem tailTrace_2287967 : CollatzResearch.WordTrace tailWord_2287967 prefixEnd_2287967 1174826792625555052290337 := by
  unfold tailWord_2287967
  simp only [CollatzResearch.WordTrace]
  refine ⟨83449012102093787499222155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55632674734729191666148103 83449012102093787499222155)
  ·
    refine ⟨125173518153140681248833233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83449012102093787499222155 125173518153140681248833233)
    ·
      refine ⟨93880138614855510936624925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125173518153140681248833233 93880138614855510936624925)
      ·
        refine ⟨35205051980570816601234347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93880138614855510936624925 35205051980570816601234347)
        ·
          refine ⟨52807577970856224901851521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35205051980570816601234347 52807577970856224901851521)
          ·
            refine ⟨39605683478142168676388641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52807577970856224901851521 39605683478142168676388641)
            ·
              refine ⟨29704262608606626507291481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39605683478142168676388641 29704262608606626507291481)
              ·
                refine ⟨22278196956454969880468611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29704262608606626507291481 22278196956454969880468611)
                ·
                  refine ⟨33417295434682454820702917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22278196956454969880468611 33417295434682454820702917)
                  ·
                    refine ⟨6265742894002960278881797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33417295434682454820702917 6265742894002960278881797)
                    ·
                      refine ⟨1174826792625555052290337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6265742894002960278881797 1174826792625555052290337)
                      ·
                        rfl

theorem cell23_2287967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2287967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287967 prefixEnd_2287967 := by exact prefixLift 2287967
  have htrace : WordTrace (prefixWord ++ tailWord_2287967) baseStart_2287967 baseEnd_2287967 := by
    simpa [prefixWord, tailWord_2287967, baseEnd_2287967] using wordTrace_append hprefix tailTrace_2287967
  have hstable : (prefixWord ++ tailWord_2287967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287967).length < 2 ^ (prefixWord ++ tailWord_2287967).sum := by decide
  have hdescent : baseEnd_2287967 < baseStart_2287967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287971 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 6, 2, 2]
def baseStart_2287971 : Nat := 118140960795 + 2287971 * 2 ^ 59
def prefixEnd_2287971 : Nat := 4983230072969 + 3 ^ 40 * 2287971 * 2
def baseEnd_2287971 : Nat := 1174828846548173036640319

theorem tailTrace_2287971 : CollatzResearch.WordTrace tailWord_2287971 prefixEnd_2287971 1174828846548173036640319 := by
  unfold tailWord_2287971
  simp only [CollatzResearch.WordTrace]
  refine ⟨83449157994079296182367767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55632771996052864121578511 83449157994079296182367767)
  ·
    refine ⟨125173736991118944273551651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83449157994079296182367767 125173736991118944273551651)
    ·
      refine ⟨187760605486678416410327477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125173736991118944273551651 187760605486678416410327477)
      ·
        refine ⟨17602556764376101538468201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187760605486678416410327477 17602556764376101538468201)
        ·
          refine ⟨13201917573282076153851151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17602556764376101538468201 13201917573282076153851151)
          ·
            refine ⟨19802876359923114230776727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13201917573282076153851151 19802876359923114230776727)
            ·
              refine ⟨29704314539884671346165091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19802876359923114230776727 29704314539884671346165091)
              ·
                refine ⟨44556471809827007019247637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29704314539884671346165091 44556471809827007019247637)
                ·
                  refine ⟨2088584616085640954027233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44556471809827007019247637 2088584616085640954027233)
                  ·
                    refine ⟨1566438462064230715520425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088584616085640954027233 1566438462064230715520425)
                    ·
                      refine ⟨1174828846548173036640319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566438462064230715520425 1174828846548173036640319)
                      ·
                        rfl

theorem cell23_2287971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_2287971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2287971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2287971 prefixEnd_2287971 := by exact prefixLift 2287971
  have htrace : WordTrace (prefixWord ++ tailWord_2287971) baseStart_2287971 baseEnd_2287971 := by
    simpa [prefixWord, tailWord_2287971, baseEnd_2287971] using wordTrace_append hprefix tailTrace_2287971
  have hstable : (prefixWord ++ tailWord_2287971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287971).length < 2 ^ (prefixWord ++ tailWord_2287971).sum := by decide
  have hdescent : baseEnd_2287971 < baseStart_2287971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288004 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2288004 : Nat := 118140960795 + 2288004 * 2 ^ 59
def prefixEnd_2288004 : Nat := 4983230072969 + 3 ^ 40 * 2288004 * 2
def baseEnd_2288004 : Nat := 1174845791409771407527667

theorem tailTrace_2288004 : CollatzResearch.WordTrace tailWord_2288004 prefixEnd_2288004 1174845791409771407527667 := by
  unfold tailWord_2288004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41725180801479871409159533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55633574401973161878879377 41725180801479871409159533)
  ·
    refine ⟨15646942800554951778434825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41725180801479871409159533 15646942800554951778434825)
    ·
      refine ⟨11735207100416213833826119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15646942800554951778434825 11735207100416213833826119)
      ·
        refine ⟨17602810650624320750739179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735207100416213833826119 17602810650624320750739179)
        ·
          refine ⟨26404215975936481126108769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17602810650624320750739179 26404215975936481126108769)
          ·
            refine ⟨19803161981952360844581577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26404215975936481126108769 19803161981952360844581577)
            ·
              refine ⟨14852371486464270633436183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19803161981952360844581577 14852371486464270633436183)
              ·
                refine ⟨22278557229696405950154275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14852371486464270633436183 22278557229696405950154275)
                ·
                  refine ⟨33417835844544608925231413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22278557229696405950154275 33417835844544608925231413)
                  ·
                    refine ⟨3132922110426057086740445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33417835844544608925231413 3132922110426057086740445)
                    ·
                      refine ⟨1174845791409771407527667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3132922110426057086740445 1174845791409771407527667)
                      ·
                        rfl

theorem cell23_2288004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2288004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288004 prefixEnd_2288004 := by exact prefixLift 2288004
  have htrace : WordTrace (prefixWord ++ tailWord_2288004) baseStart_2288004 baseEnd_2288004 := by
    simpa [prefixWord, tailWord_2288004, baseEnd_2288004] using wordTrace_append hprefix tailTrace_2288004
  have hstable : (prefixWord ++ tailWord_2288004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288004).length < 2 ^ (prefixWord ++ tailWord_2288004).sum := by decide
  have hdescent : baseEnd_2288004 < baseStart_2288004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288017 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2288017 : Nat := 118140960795 + 2288017 * 2 ^ 59
def prefixEnd_2288017 : Nat := 4983230072969 + 3 ^ 40 * 2288017 * 2
def baseEnd_2288017 : Nat := 1174852466658279856665107

theorem tailTrace_2288017 : CollatzResearch.WordTrace tailWord_2288017 prefixEnd_2288017 1174852466658279856665107 := by
  unfold tailWord_2288017
  simp only [CollatzResearch.WordTrace]
  refine ⟨83450835751912646038542305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55633890501275097359028203 83450835751912646038542305)
  ·
    refine ⟨62588126813934484528906729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83450835751912646038542305 62588126813934484528906729)
    ·
      refine ⟨46941095110450863396680047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62588126813934484528906729 46941095110450863396680047)
      ·
        refine ⟨70411642665676295095020071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46941095110450863396680047 70411642665676295095020071)
        ·
          refine ⟨105617463998514442642530107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70411642665676295095020071 105617463998514442642530107)
          ·
            refine ⟨158426195997771663963795161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105617463998514442642530107 158426195997771663963795161)
            ·
              refine ⟨118819646998328747972846371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158426195997771663963795161 118819646998328747972846371)
              ·
                refine ⟨178229470497493121959269557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118819646998328747972846371 178229470497493121959269557)
                ·
                  refine ⟨16709012859139980183681521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178229470497493121959269557 16709012859139980183681521)
                  ·
                    refine ⟨12531759644354985137761141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16709012859139980183681521 12531759644354985137761141)
                    ·
                      refine ⟨1174852466658279856665107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12531759644354985137761141 1174852466658279856665107)
                      ·
                        rfl

theorem cell23_2288017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2288017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288017 prefixEnd_2288017 := by exact prefixLift 2288017
  have htrace : WordTrace (prefixWord ++ tailWord_2288017) baseStart_2288017 baseEnd_2288017 := by
    simpa [prefixWord, tailWord_2288017, baseEnd_2288017] using wordTrace_append hprefix tailTrace_2288017
  have hstable : (prefixWord ++ tailWord_2288017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288017).length < 2 ^ (prefixWord ++ tailWord_2288017).sum := by decide
  have hdescent : baseEnd_2288017 < baseStart_2288017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288034 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2288034 : Nat := 118140960795 + 2288034 * 2 ^ 59
def prefixEnd_2288034 : Nat := 4983230072969 + 3 ^ 40 * 2288034 * 2
def baseEnd_2288034 : Nat := 1174861195829406290152529

theorem tailTrace_2288034 : CollatzResearch.WordTrace tailWord_2288034 prefixEnd_2288034 1174861195829406290152529 := by
  unfold tailWord_2288034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862863948212764485477789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55634303861900705294607437 20862863948212764485477789)
  ·
    refine ⟨7823573980579786682054171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20862863948212764485477789 7823573980579786682054171)
    ·
      refine ⟨11735360970869680023081257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7823573980579786682054171 11735360970869680023081257)
      ·
        refine ⟨8801520728152260017310943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11735360970869680023081257 8801520728152260017310943)
        ·
          refine ⟨13202281092228390025966415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801520728152260017310943 13202281092228390025966415)
          ·
            refine ⟨19803421638342585038949623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202281092228390025966415 19803421638342585038949623)
            ·
              refine ⟨29705132457513877558424435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19803421638342585038949623 29705132457513877558424435)
              ·
                refine ⟨44557698686270816337636653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29705132457513877558424435 44557698686270816337636653)
                ·
                  refine ⟨16709137007351556126613745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44557698686270816337636653 16709137007351556126613745)
                  ·
                    refine ⟨12531852755513667094960309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16709137007351556126613745 12531852755513667094960309)
                    ·
                      refine ⟨1174861195829406290152529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12531852755513667094960309 1174861195829406290152529)
                      ·
                        rfl

theorem cell23_2288034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2288034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288034 prefixEnd_2288034 := by exact prefixLift 2288034
  have htrace : WordTrace (prefixWord ++ tailWord_2288034) baseStart_2288034 baseEnd_2288034 := by
    simpa [prefixWord, tailWord_2288034, baseEnd_2288034] using wordTrace_append hprefix tailTrace_2288034
  have hstable : (prefixWord ++ tailWord_2288034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288034).length < 2 ^ (prefixWord ++ tailWord_2288034).sum := by decide
  have hdescent : baseEnd_2288034 < baseStart_2288034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288061 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_2288061 : Nat := 118140960795 + 2288061 * 2 ^ 59
def prefixEnd_2288061 : Nat := 4983230072969 + 3 ^ 40 * 2288061 * 2
def baseEnd_2288061 : Nat := 1174875059807077684514905

theorem tailTrace_2288061 : CollatzResearch.WordTrace tailWord_2288061 prefixEnd_2288061 1174875059807077684514905 := by
  unfold tailWord_2288061
  simp only [CollatzResearch.WordTrace]
  refine ⟨83452440563753241553144037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55634960375835494368762691 83452440563753241553144037)
  ·
    refine ⟨15647332605703732791214507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83452440563753241553144037 15647332605703732791214507)
    ·
      refine ⟨23470998908555599186821761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15647332605703732791214507 23470998908555599186821761)
      ·
        refine ⟨17603249181416699390116321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23470998908555599186821761 17603249181416699390116321)
        ·
          refine ⟨13202436886062524542587241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17603249181416699390116321 13202436886062524542587241)
          ·
            refine ⟨9901827664546893406940431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13202436886062524542587241 9901827664546893406940431)
            ·
              refine ⟨14852741496820340110410647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9901827664546893406940431 14852741496820340110410647)
              ·
                refine ⟨22279112245230510165615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14852741496820340110410647 22279112245230510165615971)
                ·
                  refine ⟨33418668367845765248423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22279112245230510165615971 33418668367845765248423957)
                  ·
                    refine ⟨1566500079742770246019873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33418668367845765248423957 1566500079742770246019873)
                    ·
                      refine ⟨1174875059807077684514905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566500079742770246019873 1174875059807077684514905)
                      ·
                        rfl

theorem cell23_2288061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_2288061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288061 prefixEnd_2288061 := by exact prefixLift 2288061
  have htrace : WordTrace (prefixWord ++ tailWord_2288061) baseStart_2288061 baseEnd_2288061 := by
    simpa [prefixWord, tailWord_2288061, baseEnd_2288061] using wordTrace_append hprefix tailTrace_2288061
  have hstable : (prefixWord ++ tailWord_2288061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288061).length < 2 ^ (prefixWord ++ tailWord_2288061).sum := by decide
  have hdescent : baseEnd_2288061 < baseStart_2288061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288064 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_2288064 : Nat := 118140960795 + 2288064 * 2 ^ 59
def prefixEnd_2288064 : Nat := 4983230072969 + 3 ^ 40 * 2288064 * 2
def baseEnd_2288064 : Nat := 1174876600249041172777391

theorem tailTrace_2288064 : CollatzResearch.WordTrace tailWord_2288064 prefixEnd_2288064 1174876600249041172777391 := by
  unfold tailWord_2288064
  simp only [CollatzResearch.WordTrace]
  refine ⟨41726274991371186532751623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55635033321828248710335497 41726274991371186532751623)
  ·
    refine ⟨62589412487056779799127435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41726274991371186532751623 62589412487056779799127435)
    ·
      refine ⟨93884118730585169698691153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62589412487056779799127435 93884118730585169698691153)
      ·
        refine ⟨70413089047938877274018365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93884118730585169698691153 70413089047938877274018365)
        ·
          refine ⟨26404908392977078977756887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70413089047938877274018365 26404908392977078977756887)
          ·
            refine ⟨39607362589465618466635331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26404908392977078977756887 39607362589465618466635331)
            ·
              refine ⟨59411043884198427699952997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39607362589465618466635331 59411043884198427699952997)
              ·
                refine ⟨11139570728287205193741187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59411043884198427699952997 11139570728287205193741187)
                ·
                  refine ⟨16709356092430807790611781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11139570728287205193741187 16709356092430807790611781)
                  ·
                    refine ⟨3133004267330776460739709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16709356092430807790611781 3133004267330776460739709)
                    ·
                      refine ⟨1174876600249041172777391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133004267330776460739709 1174876600249041172777391)
                      ·
                        rfl

theorem cell23_2288064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_2288064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288064 prefixEnd_2288064 := by exact prefixLift 2288064
  have htrace : WordTrace (prefixWord ++ tailWord_2288064) baseStart_2288064 baseEnd_2288064 := by
    simpa [prefixWord, tailWord_2288064, baseEnd_2288064] using wordTrace_append hprefix tailTrace_2288064
  have hstable : (prefixWord ++ tailWord_2288064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288064).length < 2 ^ (prefixWord ++ tailWord_2288064).sum := by decide
  have hdescent : baseEnd_2288064 < baseStart_2288064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288067 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 10]
def baseStart_2288067 : Nat := 118140960795 + 2288067 * 2 ^ 59
def prefixEnd_2288067 : Nat := 4983230072969 + 3 ^ 40 * 2288067 * 2
def baseEnd_2288067 : Nat := 130542015632333851226653

theorem tailTrace_2288067 : CollatzResearch.WordTrace tailWord_2288067 prefixEnd_2288067 130542015632333851226653 := by
  unfold tailWord_2288067
  simp only [CollatzResearch.WordTrace]
  refine ⟨83452659401731504577862455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55635106267821003051908303 83452659401731504577862455)
  ·
    refine ⟨125178989102597256866793683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83452659401731504577862455 125178989102597256866793683)
    ·
      refine ⟨187768483653895885300190525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125178989102597256866793683 187768483653895885300190525)
      ·
        refine ⟨70413181370210956987571447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187768483653895885300190525 70413181370210956987571447)
        ·
          refine ⟨105619772055316435481357171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70413181370210956987571447 105619772055316435481357171)
          ·
            refine ⟨158429658082974653222035757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105619772055316435481357171 158429658082974653222035757)
            ·
              refine ⟨59411121781115494958263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158429658082974653222035757 59411121781115494958263409)
              ·
                refine ⟨44558341335836621218697557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59411121781115494958263409 44558341335836621218697557)
                ·
                  refine ⟨130542015632333851226653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44558341335836621218697557 130542015632333851226653)
                  ·
                    rfl

theorem cell23_2288067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 10].length) (baseStart_2288067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288067 prefixEnd_2288067 := by exact prefixLift 2288067
  have htrace : WordTrace (prefixWord ++ tailWord_2288067) baseStart_2288067 baseEnd_2288067 := by
    simpa [prefixWord, tailWord_2288067, baseEnd_2288067] using wordTrace_append hprefix tailTrace_2288067
  have hstable : (prefixWord ++ tailWord_2288067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288067).length < 2 ^ (prefixWord ++ tailWord_2288067).sum := by decide
  have hdescent : baseEnd_2288067 < baseStart_2288067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288071 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2288071 : Nat := 118140960795 + 2288071 * 2 ^ 59
def prefixEnd_2288071 : Nat := 4983230072969 + 3 ^ 40 * 2288071 * 2
def baseEnd_2288071 : Nat := 391626731537874215129953

theorem tailTrace_2288071 : CollatzResearch.WordTrace tailWord_2288071 prefixEnd_2288071 391626731537874215129953 := by
  unfold tailWord_2288071
  simp only [CollatzResearch.WordTrace]
  refine ⟨83452805293717013261008067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55635203529144675507338711 83452805293717013261008067)
  ·
    refine ⟨125179207940575519891512101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83452805293717013261008067 125179207940575519891512101)
    ·
      refine ⟨23471101488857909979658519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125179207940575519891512101 23471101488857909979658519)
      ·
        refine ⟨35206652233286864969487779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23471101488857909979658519 35206652233286864969487779)
        ·
          refine ⟨52809978349930297454231669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35206652233286864969487779 52809978349930297454231669)
          ·
            refine ⟨4950935470305965386334219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52809978349930297454231669 4950935470305965386334219)
            ·
              refine ⟨7426403205458948079501329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950935470305965386334219 7426403205458948079501329)
              ·
                refine ⟨5569802404094211059625997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7426403205458948079501329 5569802404094211059625997)
                ·
                  refine ⟨2088675901535329147359749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5569802404094211059625997 2088675901535329147359749)
                  ·
                    refine ⟨391626731537874215129953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088675901535329147359749 391626731537874215129953)
                    ·
                      rfl

theorem cell23_2288071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2288071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288071 prefixEnd_2288071 := by exact prefixLift 2288071
  have htrace : WordTrace (prefixWord ++ tailWord_2288071) baseStart_2288071 baseEnd_2288071 := by
    simpa [prefixWord, tailWord_2288071, baseEnd_2288071] using wordTrace_append hprefix tailTrace_2288071
  have hstable : (prefixWord ++ tailWord_2288071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288071).length < 2 ^ (prefixWord ++ tailWord_2288071).sum := by decide
  have hdescent : baseEnd_2288071 < baseStart_2288071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288101 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 8]
def baseStart_2288101 : Nat := 118140960795 + 2288101 * 2 ^ 59
def prefixEnd_2288101 : Nat := 4983230072969 + 3 ^ 40 * 2288101 * 2
def baseEnd_2288101 : Nat := 130543955448139725334969

theorem tailTrace_2288101 : CollatzResearch.WordTrace tailWord_2288101 prefixEnd_2288101 130543955448139725334969 := by
  unfold tailWord_2288101
  simp only [CollatzResearch.WordTrace]
  refine ⟨83453899483608328384600157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55635932989072218923066771 83453899483608328384600157)
  ·
    refine ⟨31295212306353123144225059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83453899483608328384600157 31295212306353123144225059)
    ·
      refine ⟨46942818459529684716337589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31295212306353123144225059 46942818459529684716337589)
      ·
        refine ⟨4400889230580907942156649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46942818459529684716337589 4400889230580907942156649)
        ·
          refine ⟨3300666922935680956617487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400889230580907942156649 3300666922935680956617487)
          ·
            refine ⟨4951000384403521434926231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300666922935680956617487 4951000384403521434926231)
            ·
              refine ⟨7426500576605282152389347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951000384403521434926231 7426500576605282152389347)
              ·
                refine ⟨11139750864907923228584021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426500576605282152389347 11139750864907923228584021)
                ·
                  refine ⟨130543955448139725334969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11139750864907923228584021 130543955448139725334969)
                  ·
                    rfl

theorem cell23_2288101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_2288101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288101 prefixEnd_2288101 := by exact prefixLift 2288101
  have htrace : WordTrace (prefixWord ++ tailWord_2288101) baseStart_2288101 baseEnd_2288101 := by
    simpa [prefixWord, tailWord_2288101, baseEnd_2288101] using wordTrace_append hprefix tailTrace_2288101
  have hstable : (prefixWord ++ tailWord_2288101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288101).length < 2 ^ (prefixWord ++ tailWord_2288101).sum := by decide
  have hdescent : baseEnd_2288101 < baseStart_2288101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288104 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2288104 : Nat := 118140960795 + 2288104 * 2 ^ 59
def prefixEnd_2288104 : Nat := 4983230072969 + 3 ^ 40 * 2288104 * 2
def baseEnd_2288104 : Nat := 1174897139475221016277207

theorem tailTrace_2288104 : CollatzResearch.WordTrace tailWord_2288104 prefixEnd_2288104 1174897139475221016277207 := by
  unfold tailWord_2288104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41727004451298729948479683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55636005935064973264639577 41727004451298729948479683)
  ·
    refine ⟨62590506676948094922719525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41727004451298729948479683 62590506676948094922719525)
    ·
      refine ⟨11735720001927767798009911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62590506676948094922719525 11735720001927767798009911)
      ·
        refine ⟨17603580002891651697014867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735720001927767798009911 17603580002891651697014867)
        ·
          refine ⟨26405370004337477545522301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603580002891651697014867 26405370004337477545522301)
          ·
            refine ⟨9902013751626554079570863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26405370004337477545522301 9902013751626554079570863)
            ·
              refine ⟨14853020627439831119356295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902013751626554079570863 14853020627439831119356295)
              ·
                refine ⟨22279530941159746679034443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14853020627439831119356295 22279530941159746679034443)
                ·
                  refine ⟨33419296411739620018551665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22279530941159746679034443 33419296411739620018551665)
                  ·
                    refine ⟨25064472308804715013913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33419296411739620018551665 25064472308804715013913749)
                    ·
                      refine ⟨1174897139475221016277207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25064472308804715013913749 1174897139475221016277207)
                      ·
                        rfl

theorem cell23_2288104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2288104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288104 prefixEnd_2288104 := by exact prefixLift 2288104
  have htrace : WordTrace (prefixWord ++ tailWord_2288104) baseStart_2288104 baseEnd_2288104 := by
    simpa [prefixWord, tailWord_2288104, baseEnd_2288104] using wordTrace_append hprefix tailTrace_2288104
  have hstable : (prefixWord ++ tailWord_2288104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288104).length < 2 ^ (prefixWord ++ tailWord_2288104).sum := by decide
  have hdescent : baseEnd_2288104 < baseStart_2288104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288118 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_2288118 : Nat := 118140960795 + 2288118 * 2 ^ 59
def prefixEnd_2288118 : Nat := 4983230072969 + 3 ^ 40 * 2288118 * 2
def baseEnd_2288118 : Nat := 130544925356042662389127

theorem tailTrace_2288118 : CollatzResearch.WordTrace tailWord_2288118 prefixEnd_2288118 130544925356042662389127 := by
  unfold tailWord_2288118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215907470284171267998063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55636346349697826858646005 5215907470284171267998063)
  ·
    refine ⟨7823861205426256901997095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5215907470284171267998063 7823861205426256901997095)
    ·
      refine ⟨11735791808139385352995643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7823861205426256901997095 11735791808139385352995643)
      ·
        refine ⟨17603687712209078029493465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735791808139385352995643 17603687712209078029493465)
        ·
          refine ⟨13202765784156808522120099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17603687712209078029493465 13202765784156808522120099)
          ·
            refine ⟨19804148676235212783180149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202765784156808522120099 19804148676235212783180149)
            ·
              refine ⟨1856638938397051198423139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19804148676235212783180149 1856638938397051198423139)
              ·
                refine ⟨2784958407595576797634709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856638938397051198423139 2784958407595576797634709)
                ·
                  refine ⟨130544925356042662389127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2784958407595576797634709 130544925356042662389127)
                  ·
                    rfl

theorem cell23_2288118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_2288118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288118 prefixEnd_2288118 := by exact prefixLift 2288118
  have htrace : WordTrace (prefixWord ++ tailWord_2288118) baseStart_2288118 baseEnd_2288118 := by
    simpa [prefixWord, tailWord_2288118, baseEnd_2288118] using wordTrace_append hprefix tailTrace_2288118
  have hstable : (prefixWord ++ tailWord_2288118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288118).length < 2 ^ (prefixWord ++ tailWord_2288118).sum := by decide
  have hdescent : baseEnd_2288118 < baseStart_2288118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288121 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 5, 2]
def baseStart_2288121 : Nat := 118140960795 + 2288121 * 2 ^ 59
def prefixEnd_2288121 : Nat := 4983230072969 + 3 ^ 40 * 2288121 * 2
def baseEnd_2288121 : Nat := 1174905868646347449764629

theorem tailTrace_2288121 : CollatzResearch.WordTrace tailWord_2288121 prefixEnd_2288121 1174905868646347449764629 := by
  unfold tailWord_2288121
  simp only [CollatzResearch.WordTrace]
  refine ⟨83454628943535871800328217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55636419295690581200218811 83454628943535871800328217)
  ·
    refine ⟨62590971707651903850246163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83454628943535871800328217 62590971707651903850246163)
    ·
      refine ⟨93886457561477855775369245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62590971707651903850246163 93886457561477855775369245)
      ·
        refine ⟨35207421585554195915763467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93886457561477855775369245 35207421585554195915763467)
        ·
          refine ⟨52811132378331293873645201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35207421585554195915763467 52811132378331293873645201)
          ·
            refine ⟨39608349283748470405233901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52811132378331293873645201 39608349283748470405233901)
            ·
              refine ⟨14853130981405676401962713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39608349283748470405233901 14853130981405676401962713)
              ·
                refine ⟨11139848236054257301472035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14853130981405676401962713 11139848236054257301472035)
                ·
                  refine ⟨16709772354081385952208053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11139848236054257301472035 16709772354081385952208053)
                  ·
                    refine ⟨1566541158195129933019505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16709772354081385952208053 1566541158195129933019505)
                    ·
                      refine ⟨1174905868646347449764629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566541158195129933019505 1174905868646347449764629)
                      ·
                        rfl

theorem cell23_2288121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_2288121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288121 prefixEnd_2288121 := by exact prefixLift 2288121
  have htrace : WordTrace (prefixWord ++ tailWord_2288121) baseStart_2288121 baseEnd_2288121 := by
    simpa [prefixWord, tailWord_2288121, baseEnd_2288121] using wordTrace_append hprefix tailTrace_2288121
  have hstable : (prefixWord ++ tailWord_2288121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288121).length < 2 ^ (prefixWord ++ tailWord_2288121).sum := by decide
  have hdescent : baseEnd_2288121 < baseStart_2288121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288131 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 1, 5]
def baseStart_2288131 : Nat := 118140960795 + 2288131 * 2 ^ 59
def prefixEnd_2288131 : Nat := 4983230072969 + 3 ^ 40 * 2288131 * 2
def baseEnd_2288131 : Nat := 391637001150964136879861

theorem tailTrace_2288131 : CollatzResearch.WordTrace tailWord_2288131 prefixEnd_2288131 391637001150964136879861 := by
  unfold tailWord_2288131
  simp only [CollatzResearch.WordTrace]
  refine ⟨83454993673499643508192247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55636662448999762338794831 83454993673499643508192247)
  ·
    refine ⟨125182490510249465262288371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83454993673499643508192247 125182490510249465262288371)
    ·
      refine ⟨187773735765374197893432557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125182490510249465262288371 187773735765374197893432557)
      ·
        refine ⟨70415150912015324210037209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187773735765374197893432557 70415150912015324210037209)
        ·
          refine ⟨52811363184011493157527907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70415150912015324210037209 52811363184011493157527907)
          ·
            refine ⟨79217044776017239736291861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52811363184011493157527907 79217044776017239736291861)
            ·
              refine ⟨3713298973875808112638681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79217044776017239736291861 3713298973875808112638681)
              ·
                refine ⟨2784974230406856084479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713298973875808112638681 2784974230406856084479011)
                ·
                  refine ⟨4177461345610284126718517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784974230406856084479011 4177461345610284126718517)
                  ·
                    refine ⟨391637001150964136879861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4177461345610284126718517 391637001150964136879861)
                    ·
                      rfl

theorem cell23_2288131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 5].length) (baseStart_2288131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288131 prefixEnd_2288131 := by exact prefixLift 2288131
  have htrace : WordTrace (prefixWord ++ tailWord_2288131) baseStart_2288131 baseEnd_2288131 := by
    simpa [prefixWord, tailWord_2288131, baseEnd_2288131] using wordTrace_append hprefix tailTrace_2288131
  have hstable : (prefixWord ++ tailWord_2288131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288131).length < 2 ^ (prefixWord ++ tailWord_2288131).sum := by decide
  have hdescent : baseEnd_2288131 < baseStart_2288131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288138 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2288138 : Nat := 118140960795 + 2288138 * 2 ^ 59
def prefixEnd_2288138 : Nat := 4983230072969 + 3 ^ 40 * 2288138 * 2
def baseEnd_2288138 : Nat := 1174914597817473883252051

theorem tailTrace_2288138 : CollatzResearch.WordTrace tailWord_2288138 prefixEnd_2288138 1174914597817473883252051 := by
  unfold tailWord_2288138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20863812246118570925924267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55636832656316189135798045 20863812246118570925924267)
  ·
    refine ⟨31295718369177856388886401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20863812246118570925924267 31295718369177856388886401)
    ·
      refine ⟨23471788776883392291664801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31295718369177856388886401 23471788776883392291664801)
      ·
        refine ⟨17603841582662544218748601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23471788776883392291664801 17603841582662544218748601)
        ·
          refine ⟨13202881186996908164061451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17603841582662544218748601 13202881186996908164061451)
          ·
            refine ⟨19804321780495362246092177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202881186996908164061451 19804321780495362246092177)
            ·
              refine ⟨14853241335371521684569133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19804321780495362246092177 14853241335371521684569133)
              ·
                refine ⟨5569965500764320631713425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14853241335371521684569133 5569965500764320631713425)
                ·
                  refine ⟨4177474125573240473785069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5569965500764320631713425 4177474125573240473785069)
                  ·
                    refine ⟨1566552797089965177669401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4177474125573240473785069 1566552797089965177669401)
                    ·
                      refine ⟨1174914597817473883252051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566552797089965177669401 1174914597817473883252051)
                      ·
                        rfl

theorem cell23_2288138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2288138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288138 prefixEnd_2288138 := by exact prefixLift 2288138
  have htrace : WordTrace (prefixWord ++ tailWord_2288138) baseStart_2288138 baseEnd_2288138 := by
    simpa [prefixWord, tailWord_2288138, baseEnd_2288138] using wordTrace_append hprefix tailTrace_2288138
  have hstable : (prefixWord ++ tailWord_2288138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288138).length < 2 ^ (prefixWord ++ tailWord_2288138).sum := by decide
  have hdescent : baseEnd_2288138 < baseStart_2288138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288161 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2288161 : Nat := 118140960795 + 2288161 * 2 ^ 59
def prefixEnd_2288161 : Nat := 4983230072969 + 3 ^ 40 * 2288161 * 2
def baseEnd_2288161 : Nat := 391642135957509097754815

theorem tailTrace_2288161 : CollatzResearch.WordTrace tailWord_2288161 prefixEnd_2288161 391642135957509097754815 := by
  unfold tailWord_2288161
  simp only [CollatzResearch.WordTrace]
  refine ⟨83456087863390958631784337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55637391908927305754522891 83456087863390958631784337)
  ·
    refine ⟨62592065897543218973838253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83456087863390958631784337 62592065897543218973838253)
    ·
      refine ⟨23472024711578707115189345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62592065897543218973838253 23472024711578707115189345)
      ·
        refine ⟨17604018533684030336392009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23472024711578707115189345 17604018533684030336392009)
        ·
          refine ⟨13203013900263022752294007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17604018533684030336392009 13203013900263022752294007)
          ·
            refine ⟨19804520850394534128441011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13203013900263022752294007 19804520850394534128441011)
            ·
              refine ⟨29706781275591801192661517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19804520850394534128441011 29706781275591801192661517)
              ·
                refine ⟨11140042978346925447248069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29706781275591801192661517 11140042978346925447248069)
                ·
                  refine ⟨2088758058440048521359013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11140042978346925447248069 2088758058440048521359013)
                  ·
                    refine ⟨391642135957509097754815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088758058440048521359013 391642135957509097754815)
                    ·
                      rfl

theorem cell23_2288161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2288161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288161 prefixEnd_2288161 := by exact prefixLift 2288161
  have htrace : WordTrace (prefixWord ++ tailWord_2288161) baseStart_2288161 baseEnd_2288161 := by
    simpa [prefixWord, tailWord_2288161, baseEnd_2288161] using wordTrace_append hprefix tailTrace_2288161
  have hstable : (prefixWord ++ tailWord_2288161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288161).length < 2 ^ (prefixWord ++ tailWord_2288161).sum := by decide
  have hdescent : baseEnd_2288161 < baseStart_2288161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288181 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2288181 : Nat := 118140960795 + 2288181 * 2 ^ 59
def prefixEnd_2288181 : Nat := 4983230072969 + 3 ^ 40 * 2288181 * 2
def baseEnd_2288181 : Nat := 1174936677485617215014353

theorem tailTrace_2288181 : CollatzResearch.WordTrace tailWord_2288181 prefixEnd_2288181 1174936677485617215014353 := by
  unfold tailWord_2288181
  simp only [CollatzResearch.WordTrace]
  refine ⟨83456817323318502047512397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55637878215545668031674931 83456817323318502047512397)
  ·
    refine ⟨31296306496244438267817149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83456817323318502047512397 31296306496244438267817149)
    ·
      refine ⟨11736114936091664350431431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31296306496244438267817149 11736114936091664350431431)
      ·
        refine ⟨17604172404137496525647147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11736114936091664350431431 17604172404137496525647147)
        ·
          refine ⟨26406258606206244788470721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17604172404137496525647147 26406258606206244788470721)
          ·
            refine ⟨19804693954654683591353041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26406258606206244788470721 19804693954654683591353041)
            ·
              refine ⟨14853520465991012693514781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19804693954654683591353041 14853520465991012693514781)
              ·
                refine ⟨5570070174746629760068043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14853520465991012693514781 5570070174746629760068043)
                ·
                  refine ⟨8355105262119944640102065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570070174746629760068043 8355105262119944640102065)
                  ·
                    refine ⟨6266328946589958480076549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8355105262119944640102065 6266328946589958480076549)
                    ·
                      refine ⟨1174936677485617215014353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6266328946589958480076549 1174936677485617215014353)
                      ·
                        rfl

theorem cell23_2288181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2288181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288181 prefixEnd_2288181 := by exact prefixLift 2288181
  have htrace : WordTrace (prefixWord ++ tailWord_2288181) baseStart_2288181 baseEnd_2288181 := by
    simpa [prefixWord, tailWord_2288181, baseEnd_2288181] using wordTrace_append hprefix tailTrace_2288181
  have hstable : (prefixWord ++ tailWord_2288181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288181).length < 2 ^ (prefixWord ++ tailWord_2288181).sum := by decide
  have hdescent : baseEnd_2288181 < baseStart_2288181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288188 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_2288188 : Nat := 118140960795 + 2288188 * 2 ^ 59
def prefixEnd_2288188 : Nat := 4983230072969 + 3 ^ 40 * 2288188 * 2
def baseEnd_2288188 : Nat := 1174940271850198687626821

theorem tailTrace_2288188 : CollatzResearch.WordTrace tailWord_2288188 prefixEnd_2288188 1174940271850198687626821 := by
  unfold tailWord_2288188
  simp only [CollatzResearch.WordTrace]
  refine ⟨41728536317146571121508609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55638048422862094828678145 41728536317146571121508609)
  ·
    refine ⟨31296402237859928341131457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41728536317146571121508609 31296402237859928341131457)
    ·
      refine ⟨23472301678394946255848593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31296402237859928341131457 23472301678394946255848593)
      ·
        refine ⟨17604226258796209691886445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23472301678394946255848593 17604226258796209691886445)
        ·
          refine ⟨6601584847048578634457417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17604226258796209691886445 6601584847048578634457417)
          ·
            refine ⟨4951188635286433975843063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6601584847048578634457417 4951188635286433975843063)
            ·
              refine ⟨7426782952929650963764595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951188635286433975843063 7426782952929650963764595)
              ·
                refine ⟨11140174429394476445646893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426782952929650963764595 11140174429394476445646893)
                ·
                  refine ⟨4177565411022928667117585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11140174429394476445646893 4177565411022928667117585)
                  ·
                    refine ⟨3133174058267196500338189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4177565411022928667117585 3133174058267196500338189)
                    ·
                      refine ⟨1174940271850198687626821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133174058267196500338189 1174940271850198687626821)
                      ·
                        rfl

theorem cell23_2288188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_2288188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288188 prefixEnd_2288188 := by exact prefixLift 2288188
  have htrace : WordTrace (prefixWord ++ tailWord_2288188) baseStart_2288188 baseEnd_2288188 := by
    simpa [prefixWord, tailWord_2288188, baseEnd_2288188] using wordTrace_append hprefix tailTrace_2288188
  have hstable : (prefixWord ++ tailWord_2288188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288188).length < 2 ^ (prefixWord ++ tailWord_2288188).sum := by decide
  have hdescent : baseEnd_2288188 < baseStart_2288188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288205 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2288205 : Nat := 118140960795 + 2288205 * 2 ^ 59
def prefixEnd_2288205 : Nat := 4983230072969 + 3 ^ 40 * 2288205 * 2
def baseEnd_2288205 : Nat := 1174949001021325121114243

theorem tailTrace_2288205 : CollatzResearch.WordTrace tailWord_2288205 prefixEnd_2288205 1174949001021325121114243 := by
  unfold tailWord_2288205
  simp only [CollatzResearch.WordTrace]
  refine ⟨83457692675231554146386069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55638461783487702764257379 83457692675231554146386069)
  ·
    refine ⟨3912079344151479100611847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83457692675231554146386069 3912079344151479100611847)
    ·
      refine ⟨5868119016227218650917771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912079344151479100611847 5868119016227218650917771)
      ·
        refine ⟨8802178524340827976376657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5868119016227218650917771 8802178524340827976376657)
        ·
          refine ⟨6601633893255620982282493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8802178524340827976376657 6601633893255620982282493)
          ·
            refine ⟨2475612709970857868355935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6601633893255620982282493 2475612709970857868355935)
            ·
              refine ⟨3713419064956286802533903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475612709970857868355935 3713419064956286802533903)
              ·
                refine ⟨5570128597434430203800855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713419064956286802533903 5570128597434430203800855)
                ·
                  refine ⟨8355192896151645305701283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570128597434430203800855 8355192896151645305701283)
                  ·
                    refine ⟨12532789344227467958551925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8355192896151645305701283 12532789344227467958551925)
                    ·
                      refine ⟨1174949001021325121114243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12532789344227467958551925 1174949001021325121114243)
                      ·
                        rfl

theorem cell23_2288205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2288205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288205 prefixEnd_2288205 := by exact prefixLift 2288205
  have htrace : WordTrace (prefixWord ++ tailWord_2288205) baseStart_2288205 baseEnd_2288205 := by
    simpa [prefixWord, tailWord_2288205, baseEnd_2288205] using wordTrace_append hprefix tailTrace_2288205
  have hstable : (prefixWord ++ tailWord_2288205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288205).length < 2 ^ (prefixWord ++ tailWord_2288205).sum := by decide
  have hdescent : baseEnd_2288205 < baseStart_2288205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288228 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_2288228 : Nat := 118140960795 + 2288228 * 2 ^ 59
def prefixEnd_2288228 : Nat := 4983230072969 + 3 ^ 40 * 2288228 * 2
def baseEnd_2288228 : Nat := 1174960811076378531126637

theorem tailTrace_2288228 : CollatzResearch.WordTrace tailWord_2288228 prefixEnd_2288228 1174960811076378531126637 := by
  unfold tailWord_2288228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41729265777074114537236669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55639021036098819382982225 41729265777074114537236669)
  ·
    refine ⟨15648474666402792951463751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41729265777074114537236669 15648474666402792951463751)
    ·
      refine ⟨23472711999604189427195627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15648474666402792951463751 23472711999604189427195627)
      ·
        refine ⟨35209067999406284140793441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23472711999604189427195627 35209067999406284140793441)
        ·
          refine ⟨26406800999554713105595081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35209067999406284140793441 26406800999554713105595081)
          ·
            refine ⟨19805100749666034829196311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26406800999554713105595081 19805100749666034829196311)
            ·
              refine ⟨29707651124499052243794467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19805100749666034829196311 29707651124499052243794467)
              ·
                refine ⟨44561476686748578365691701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29707651124499052243794467 44561476686748578365691701)
                ·
                  refine ⟨4177638439382679221783597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44561476686748578365691701 4177638439382679221783597)
                  ·
                    refine ⟨1566614414768504708168849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4177638439382679221783597 1566614414768504708168849)
                    ·
                      refine ⟨1174960811076378531126637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566614414768504708168849 1174960811076378531126637)
                      ·
                        rfl

theorem cell23_2288228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_2288228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288228 prefixEnd_2288228 := by exact prefixLift 2288228
  have htrace : WordTrace (prefixWord ++ tailWord_2288228) baseStart_2288228 baseEnd_2288228 := by
    simpa [prefixWord, tailWord_2288228, baseEnd_2288228] using wordTrace_append hprefix tailTrace_2288228
  have hstable : (prefixWord ++ tailWord_2288228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288228).length < 2 ^ (prefixWord ++ tailWord_2288228).sum := by decide
  have hdescent : baseEnd_2288228 < baseStart_2288228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288281 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 7]
def baseStart_2288281 : Nat := 118140960795 + 2288281 * 2 ^ 59
def prefixEnd_2288281 : Nat := 4983230072969 + 3 ^ 40 * 2288281 * 2
def baseEnd_2288281 : Nat := 130554225061229647084877

theorem tailTrace_2288281 : CollatzResearch.WordTrace tailWord_2288281 prefixEnd_2288281 130554225061229647084877 := by
  unfold tailWord_2288281
  simp only [CollatzResearch.WordTrace]
  refine ⟨83460464622956219126152697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55640309748637479417435131 83460464622956219126152697)
  ·
    refine ⟨62595348467217164344614523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83460464622956219126152697 62595348467217164344614523)
    ·
      refine ⟨93893022700825746516921785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62595348467217164344614523 93893022700825746516921785)
      ·
        refine ⟨70419767025619309887691339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93893022700825746516921785 70419767025619309887691339)
        ·
          refine ⟨105629650538428964831537009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70419767025619309887691339 105629650538428964831537009)
          ·
            refine ⟨79222237903821723623652757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105629650538428964831537009 79222237903821723623652757)
            ·
              refine ⟨3713542401741643294858723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79222237903821723623652757 3713542401741643294858723)
              ·
                refine ⟨5570313602612464942288085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713542401741643294858723 5570313602612464942288085)
                ·
                  refine ⟨130554225061229647084877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5570313602612464942288085 130554225061229647084877)
                  ·
                    rfl

theorem cell23_2288281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_2288281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288281 prefixEnd_2288281 := by exact prefixLift 2288281
  have htrace : WordTrace (prefixWord ++ tailWord_2288281) baseStart_2288281 baseEnd_2288281 := by
    simpa [prefixWord, tailWord_2288281, baseEnd_2288281] using wordTrace_append hprefix tailTrace_2288281
  have hstable : (prefixWord ++ tailWord_2288281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288281).length < 2 ^ (prefixWord ++ tailWord_2288281).sum := by decide
  have hdescent : baseEnd_2288281 < baseStart_2288281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288291 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2288291 : Nat := 118140960795 + 2288291 * 2 ^ 59
def prefixEnd_2288291 : Nat := 4983230072969 + 3 ^ 40 * 2288291 * 2
def baseEnd_2288291 : Nat := 1174993160357611784638847

theorem tailTrace_2288291 : CollatzResearch.WordTrace tailWord_2288291 prefixEnd_2288291 1174993160357611784638847 := by
  unfold tailWord_2288291
  simp only [CollatzResearch.WordTrace]
  refine ⟨83460829352919990834016727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55640552901946660556011151 83460829352919990834016727)
  ·
    refine ⟨125191244029379986251025091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83460829352919990834016727 125191244029379986251025091)
    ·
      refine ⟨187786866044069979376537637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125191244029379986251025091 187786866044069979376537637)
      ·
        refine ⟨35210037383263121133100807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187786866044069979376537637 35210037383263121133100807)
        ·
          refine ⟨52815056074894681699651211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35210037383263121133100807 52815056074894681699651211)
          ·
            refine ⟨79222584112342022549476817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52815056074894681699651211 79222584112342022549476817)
            ·
              refine ⟨59416938084256516912107613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79222584112342022549476817 59416938084256516912107613)
              ·
                refine ⟨22281351781596193842040355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59416938084256516912107613 22281351781596193842040355)
                ·
                  refine ⟨33422027672394290763060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22281351781596193842040355 33422027672394290763060533)
                  ·
                    refine ⟨3133315094286964759036925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33422027672394290763060533 3133315094286964759036925)
                    ·
                      refine ⟨1174993160357611784638847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133315094286964759036925 1174993160357611784638847)
                      ·
                        rfl

theorem cell23_2288291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2288291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288291 prefixEnd_2288291 := by exact prefixLift 2288291
  have htrace : WordTrace (prefixWord ++ tailWord_2288291) baseStart_2288291 baseEnd_2288291 := by
    simpa [prefixWord, tailWord_2288291, baseEnd_2288291] using wordTrace_append hprefix tailTrace_2288291
  have hstable : (prefixWord ++ tailWord_2288291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288291).length < 2 ^ (prefixWord ++ tailWord_2288291).sum := by decide
  have hdescent : baseEnd_2288291 < baseStart_2288291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288328 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2288328 : Nat := 118140960795 + 2288328 * 2 ^ 59
def prefixEnd_2288328 : Nat := 4983230072969 + 3 ^ 40 * 2288328 * 2
def baseEnd_2288328 : Nat := 391670719713942713292059

theorem tailTrace_2288328 : CollatzResearch.WordTrace tailWord_2288328 prefixEnd_2288328 391670719713942713292059 := by
  unfold tailWord_2288328
  simp only [CollatzResearch.WordTrace]
  refine ⟨41731089426892973076556819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55641452569190630768742425 41731089426892973076556819)
  ·
    refine ⟨62596634140339459614835229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41731089426892973076556819 62596634140339459614835229)
    ·
      refine ⟨23473737802627297355563211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62596634140339459614835229 23473737802627297355563211)
      ·
        refine ⟨35210606703940946033344817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23473737802627297355563211 35210606703940946033344817)
        ·
          refine ⟨26407955027955709525008613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35210606703940946033344817 26407955027955709525008613)
          ·
            refine ⟨4951491567741695535939115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26407955027955709525008613 4951491567741695535939115)
            ·
              refine ⟨7427237351612543303908673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951491567741695535939115 7427237351612543303908673)
              ·
                refine ⟨5570428013709407477931505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7427237351612543303908673 5570428013709407477931505)
                ·
                  refine ⟨4177821010282055608448629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570428013709407477931505 4177821010282055608448629)
                  ·
                    refine ⟨391670719713942713292059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4177821010282055608448629 391670719713942713292059)
                    ·
                      rfl

theorem cell23_2288328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2288328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288328 prefixEnd_2288328 := by exact prefixLift 2288328
  have htrace : WordTrace (prefixWord ++ tailWord_2288328) baseStart_2288328 baseEnd_2288328 := by
    simpa [prefixWord, tailWord_2288328, baseEnd_2288328] using wordTrace_append hprefix tailTrace_2288328
  have hstable : (prefixWord ++ tailWord_2288328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288328).length < 2 ^ (prefixWord ++ tailWord_2288328).sum := by decide
  have hdescent : baseEnd_2288328 < baseStart_2288328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288332 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 5]
def baseStart_2288332 : Nat := 118140960795 + 2288332 * 2 ^ 59
def prefixEnd_2288332 : Nat := 4983230072969 + 3 ^ 40 * 2288332 * 2
def baseEnd_2288332 : Nat := 130557134784938458247351

theorem tailTrace_2288332 : CollatzResearch.WordTrace tailWord_2288332 prefixEnd_2288332 130557134784938458247351 := by
  unfold tailWord_2288332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41731162372885727418129625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55641549830514303224172833 41731162372885727418129625)
  ·
    refine ⟨31298371779664295563597219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41731162372885727418129625 31298371779664295563597219)
    ·
      refine ⟨46947557669496443345395829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31298371779664295563597219 46947557669496443345395829)
      ·
        refine ⟨4401333531515291563630859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46947557669496443345395829 4401333531515291563630859)
        ·
          refine ⟨6602000297272937345446289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401333531515291563630859 6602000297272937345446289)
          ·
            refine ⟨4951500222954703009084717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602000297272937345446289 4951500222954703009084717)
            ·
              refine ⟨1856812583608013628406769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4951500222954703009084717 1856812583608013628406769)
              ·
                refine ⟨1392609437706010221305077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856812583608013628406769 1392609437706010221305077)
                ·
                  refine ⟨130557134784938458247351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392609437706010221305077 130557134784938458247351)
                  ·
                    rfl

theorem cell23_2288332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_2288332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288332 prefixEnd_2288332 := by exact prefixLift 2288332
  have htrace : WordTrace (prefixWord ++ tailWord_2288332) baseStart_2288332 baseEnd_2288332 := by
    simpa [prefixWord, tailWord_2288332, baseEnd_2288332] using wordTrace_append hprefix tailTrace_2288332
  have hstable : (prefixWord ++ tailWord_2288332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288332).length < 2 ^ (prefixWord ++ tailWord_2288332).sum := by decide
  have hdescent : baseEnd_2288332 < baseStart_2288332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288361 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_2288361 : Nat := 118140960795 + 2288361 * 2 ^ 59
def prefixEnd_2288361 : Nat := 4983230072969 + 3 ^ 40 * 2288361 * 2
def baseEnd_2288361 : Nat := 1175029104003426510763525

theorem tailTrace_2288361 : CollatzResearch.WordTrace tailWord_2288361 prefixEnd_2288361 1175029104003426510763525 := by
  unfold tailWord_2288361
  simp only [CollatzResearch.WordTrace]
  refine ⟨83463382462666392789064937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55642254975110928526043291 83463382462666392789064937)
  ·
    refine ⟨62597536846999794591798703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83463382462666392789064937 62597536846999794591798703)
    ·
      refine ⟨93896305270499691887698055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62597536846999794591798703 93896305270499691887698055)
      ·
        refine ⟨140844457905749537831547083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93896305270499691887698055 140844457905749537831547083)
        ·
          refine ⟨211266686858624306747320625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140844457905749537831547083 211266686858624306747320625)
          ·
            refine ⟨158450015143968230060490469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211266686858624306747320625 158450015143968230060490469)
            ·
              refine ⟨29709377839494043136341963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158450015143968230060490469 29709377839494043136341963)
              ·
                refine ⟨44564066759241064704512945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29709377839494043136341963 44564066759241064704512945)
                ·
                  refine ⟨33423050069430798528384709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44564066759241064704512945 33423050069430798528384709)
                  ·
                    refine ⟨6266821888018274724072133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33423050069430798528384709 6266821888018274724072133)
                    ·
                      refine ⟨1175029104003426510763525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6266821888018274724072133 1175029104003426510763525)
                      ·
                        rfl

theorem cell23_2288361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_2288361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288361 prefixEnd_2288361 := by exact prefixLift 2288361
  have htrace : WordTrace (prefixWord ++ tailWord_2288361) baseStart_2288361 baseEnd_2288361 := by
    simpa [prefixWord, tailWord_2288361, baseEnd_2288361] using wordTrace_append hprefix tailTrace_2288361
  have hstable : (prefixWord ++ tailWord_2288361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288361).length < 2 ^ (prefixWord ++ tailWord_2288361).sum := by decide
  have hdescent : baseEnd_2288361 < baseStart_2288361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288365 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2288365 : Nat := 118140960795 + 2288365 * 2 ^ 59
def prefixEnd_2288365 : Nat := 4983230072969 + 3 ^ 40 * 2288365 * 2
def baseEnd_2288365 : Nat := 1175031157926044495113507

theorem tailTrace_2288365 : CollatzResearch.WordTrace tailWord_2288365 prefixEnd_2288365 1175031157926044495113507 := by
  unfold tailWord_2288365
  simp only [CollatzResearch.WordTrace]
  refine ⟨83463528354651901472210549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55642352236434600981473699 83463528354651901472210549)
  ·
    refine ⟨7824705783248615763019739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83463528354651901472210549 7824705783248615763019739)
    ·
      refine ⟨11737058674872923644529609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7824705783248615763019739 11737058674872923644529609)
      ·
        refine ⟨8802794006154692733397207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11737058674872923644529609 8802794006154692733397207)
        ·
          refine ⟨13204191009232039100095811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8802794006154692733397207 13204191009232039100095811)
          ·
            refine ⟨19806286513848058650143717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13204191009232039100095811 19806286513848058650143717)
            ·
              refine ⟨3713678721346510996901947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19806286513848058650143717 3713678721346510996901947)
              ·
                refine ⟨5570518082019766495352921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713678721346510996901947 5570518082019766495352921)
                ·
                  refine ⟨4177888561514824871514691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570518082019766495352921 4177888561514824871514691)
                  ·
                    refine ⟨6266832842272237307272037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177888561514824871514691 6266832842272237307272037)
                    ·
                      refine ⟨1175031157926044495113507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6266832842272237307272037 1175031157926044495113507)
                      ·
                        rfl

theorem cell23_2288365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2288365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288365 prefixEnd_2288365 := by exact prefixLift 2288365
  have htrace : WordTrace (prefixWord ++ tailWord_2288365) baseStart_2288365 baseEnd_2288365 := by
    simpa [prefixWord, tailWord_2288365, baseEnd_2288365] using wordTrace_append hprefix tailTrace_2288365
  have hstable : (prefixWord ++ tailWord_2288365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288365).length < 2 ^ (prefixWord ++ tailWord_2288365).sum := by decide
  have hdescent : baseEnd_2288365 < baseStart_2288365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288375 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 1, 4]
def baseStart_2288375 : Nat := 118140960795 + 2288375 * 2 ^ 59
def prefixEnd_2288375 : Nat := 4983230072969 + 3 ^ 40 * 2288375 * 2
def baseEnd_2288375 : Nat := 391678764244196485329487

theorem tailTrace_2288375 : CollatzResearch.WordTrace tailWord_2288375 prefixEnd_2288375 391678764244196485329487 := by
  unfold tailWord_2288375
  simp only [CollatzResearch.WordTrace]
  refine ⟨83463893084615673180074579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55642595389743782120049719 83463893084615673180074579)
  ·
    refine ⟨125195839626923509770111869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83463893084615673180074579 125195839626923509770111869)
    ·
      refine ⟨46948439860096316163791951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125195839626923509770111869 46948439860096316163791951)
      ·
        refine ⟨70422659790144474245687927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46948439860096316163791951 70422659790144474245687927)
        ·
          refine ⟨105633989685216711368531891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70422659790144474245687927 105633989685216711368531891)
          ·
            refine ⟨158450984527825067052797837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105633989685216711368531891 158450984527825067052797837)
            ·
              refine ⟨59419119197934400144799189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158450984527825067052797837 59419119197934400144799189)
              ·
                refine ⟨1392635606201587503393731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59419119197934400144799189 1392635606201587503393731)
                ·
                  refine ⟨2088953409302381255090597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392635606201587503393731 2088953409302381255090597)
                  ·
                    refine ⟨391678764244196485329487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088953409302381255090597 391678764244196485329487)
                    ·
                      rfl

theorem cell23_2288375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_2288375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288375 prefixEnd_2288375 := by exact prefixLift 2288375
  have htrace : WordTrace (prefixWord ++ tailWord_2288375) baseStart_2288375 baseEnd_2288375 := by
    simpa [prefixWord, tailWord_2288375, baseEnd_2288375] using wordTrace_append hprefix tailTrace_2288375
  have hstable : (prefixWord ++ tailWord_2288375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288375).length < 2 ^ (prefixWord ++ tailWord_2288375).sum := by decide
  have hdescent : baseEnd_2288375 < baseStart_2288375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288392 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 1, 4]
def baseStart_2288392 : Nat := 118140960795 + 2288392 * 2 ^ 59
def prefixEnd_2288392 : Nat := 4983230072969 + 3 ^ 40 * 2288392 * 2
def baseEnd_2288392 : Nat := 391681673967905296491961

theorem tailTrace_2288392 : CollatzResearch.WordTrace tailWord_2288392 prefixEnd_2288392 391681673967905296491961 := by
  unfold tailWord_2288392
  simp only [CollatzResearch.WordTrace]
  refine ⟨41732256562777042541721715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55643008750369390055628953 41732256562777042541721715)
  ·
    refine ⟨62598384844165563812582573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41732256562777042541721715 62598384844165563812582573)
    ·
      refine ⟨23474394316562086429718465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62598384844165563812582573 23474394316562086429718465)
      ·
        refine ⟨17605795737421564822288849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23474394316562086429718465 17605795737421564822288849)
        ·
          refine ⟨13204346803066173616716637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17605795737421564822288849 13204346803066173616716637)
          ·
            refine ⟨4951630051149815106268739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13204346803066173616716637 4951630051149815106268739)
            ·
              refine ⟨7427445076724722659403109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951630051149815106268739 7427445076724722659403109)
              ·
                refine ⟨1392645951885885498638083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7427445076724722659403109 1392645951885885498638083)
                ·
                  refine ⟨2088968927828828247957125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392645951885885498638083 2088968927828828247957125)
                  ·
                    refine ⟨391681673967905296491961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088968927828828247957125 391681673967905296491961)
                    ·
                      rfl

theorem cell23_2288392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_2288392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288392 prefixEnd_2288392 := by exact prefixLift 2288392
  have htrace : WordTrace (prefixWord ++ tailWord_2288392) baseStart_2288392 baseEnd_2288392 := by
    simpa [prefixWord, tailWord_2288392, baseEnd_2288392] using wordTrace_append hprefix tailTrace_2288392
  have hstable : (prefixWord ++ tailWord_2288392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288392).length < 2 ^ (prefixWord ++ tailWord_2288392).sum := by decide
  have hdescent : baseEnd_2288392 < baseStart_2288392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288398 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2288398 : Nat := 118140960795 + 2288398 * 2 ^ 59
def prefixEnd_2288398 : Nat := 4983230072969 + 3 ^ 40 * 2288398 * 2
def baseEnd_2288398 : Nat := 1175048102787642866000855

theorem tailTrace_2288398 : CollatzResearch.WordTrace tailWord_2288398 prefixEnd_2288398 1175048102787642866000855 := by
  unfold tailWord_2288398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433091495441543513520231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55643154642354898738774565 10433091495441543513520231)
  ·
    refine ⟨15649637243162315270280347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10433091495441543513520231 15649637243162315270280347)
    ·
      refine ⟨23474455864743472905420521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15649637243162315270280347 23474455864743472905420521)
      ·
        refine ⟨17605841898557604679065391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23474455864743472905420521 17605841898557604679065391)
        ·
          refine ⟨26408762847836407018598087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17605841898557604679065391 26408762847836407018598087)
          ·
            refine ⟨39613144271754610527897131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26408762847836407018598087 39613144271754610527897131)
            ·
              refine ⟨59419716407631915791845697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39613144271754610527897131 59419716407631915791845697)
              ·
                refine ⟨44564787305723936843884273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59419716407631915791845697 44564787305723936843884273)
                ·
                  refine ⟨33423590479292952632913205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44564787305723936843884273 33423590479292952632913205)
                  ·
                    refine ⟨3133461607433714309335613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33423590479292952632913205 3133461607433714309335613)
                    ·
                      refine ⟨1175048102787642866000855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133461607433714309335613 1175048102787642866000855)
                      ·
                        rfl

theorem cell23_2288398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2288398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288398 prefixEnd_2288398 := by exact prefixLift 2288398
  have htrace : WordTrace (prefixWord ++ tailWord_2288398) baseStart_2288398 baseEnd_2288398 := by
    simpa [prefixWord, tailWord_2288398, baseEnd_2288398] using wordTrace_append hprefix tailTrace_2288398
  have hstable : (prefixWord ++ tailWord_2288398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288398).length < 2 ^ (prefixWord ++ tailWord_2288398).sum := by decide
  have hdescent : baseEnd_2288398 < baseStart_2288398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288415 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2288415 : Nat := 118140960795 + 2288415 * 2 ^ 59
def prefixEnd_2288415 : Nat := 4983230072969 + 3 ^ 40 * 2288415 * 2
def baseEnd_2288415 : Nat := 1175056831958769299488277

theorem tailTrace_2288415 : CollatzResearch.WordTrace tailWord_2288415 prefixEnd_2288415 1175056831958769299488277 := by
  unfold tailWord_2288415
  simp only [CollatzResearch.WordTrace]
  refine ⟨83465352004470760011530699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55643568002980506674353799 83465352004470760011530699)
  ·
    refine ⟨125198028006706140017296049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83465352004470760011530699 125198028006706140017296049)
    ·
      refine ⟨93898521005029605012972037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125198028006706140017296049 93898521005029605012972037)
      ·
        refine ⟨17605972688443050939932257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93898521005029605012972037 17605972688443050939932257)
        ·
          refine ⟨13204479516332288204949193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17605972688443050939932257 13204479516332288204949193)
          ·
            refine ⟨9903359637249216153711895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13204479516332288204949193 9903359637249216153711895)
            ·
              refine ⟨14855039455873824230567843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9903359637249216153711895 14855039455873824230567843)
              ·
                refine ⟨22282559183810736345851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14855039455873824230567843 22282559183810736345851765)
                ·
                  refine ⟨2088989923482256532423603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22282559183810736345851765 2088989923482256532423603)
                  ·
                    refine ⟨3133484885223384798635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2088989923482256532423603 3133484885223384798635405)
                    ·
                      refine ⟨1175056831958769299488277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133484885223384798635405 1175056831958769299488277)
                      ·
                        rfl

theorem cell23_2288415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2288415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288415 prefixEnd_2288415 := by exact prefixLift 2288415
  have htrace : WordTrace (prefixWord ++ tailWord_2288415) baseStart_2288415 baseEnd_2288415 := by
    simpa [prefixWord, tailWord_2288415, baseEnd_2288415] using wordTrace_append hprefix tailTrace_2288415
  have hstable : (prefixWord ++ tailWord_2288415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288415).length < 2 ^ (prefixWord ++ tailWord_2288415).sum := by decide
  have hdescent : baseEnd_2288415 < baseStart_2288415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288426 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2288426 : Nat := 118140960795 + 2288426 * 2 ^ 59
def prefixEnd_2288426 : Nat := 4983230072969 + 3 ^ 40 * 2288426 * 2
def baseEnd_2288426 : Nat := 391687493415322918816909

theorem tailTrace_2288426 : CollatzResearch.WordTrace tailWord_2288426 prefixEnd_2288426 391687493415322918816909 := by
  unfold tailWord_2288426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866438301857727222545283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55643835471620605926787421 20866438301857727222545283)
  ·
    refine ⟨31299657452786590833817925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20866438301857727222545283 31299657452786590833817925)
    ·
      refine ⟨5868685772397485781340861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31299657452786590833817925 5868685772397485781340861)
      ·
        refine ⟨2200757164649057168002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5868685772397485781340861 2200757164649057168002823)
        ·
          refine ⟨3301135746973585752004235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200757164649057168002823 3301135746973585752004235)
          ·
            refine ⟨4951703620460378628006353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301135746973585752004235 4951703620460378628006353)
            ·
              refine ⟨3713777715345283971004765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4951703620460378628006353 3713777715345283971004765)
              ·
                refine ⟨1392666643254481489126787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3713777715345283971004765 1392666643254481489126787)
                ·
                  refine ⟨2088999964881722233690181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392666643254481489126787 2088999964881722233690181)
                  ·
                    refine ⟨391687493415322918816909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088999964881722233690181 391687493415322918816909)
                    ·
                      rfl

theorem cell23_2288426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2288426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288426 prefixEnd_2288426 := by exact prefixLift 2288426
  have htrace : WordTrace (prefixWord ++ tailWord_2288426) baseStart_2288426 baseEnd_2288426 := by
    simpa [prefixWord, tailWord_2288426, baseEnd_2288426] using wordTrace_append hprefix tailTrace_2288426
  have hstable : (prefixWord ++ tailWord_2288426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288426).length < 2 ^ (prefixWord ++ tailWord_2288426).sum := by decide
  have hdescent : baseEnd_2288426 < baseStart_2288426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288435 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 1, 5]
def baseStart_2288435 : Nat := 118140960795 + 2288435 * 2 ^ 59
def prefixEnd_2288435 : Nat := 4983230072969 + 3 ^ 40 * 2288435 * 2
def baseEnd_2288435 : Nat := 391689033857286407079395

theorem tailTrace_2288435 : CollatzResearch.WordTrace tailWord_2288435 prefixEnd_2288435 391689033857286407079395 := by
  unfold tailWord_2288435
  simp only [CollatzResearch.WordTrace]
  refine ⟨83466081464398303427258759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55644054309598868951505839 83466081464398303427258759)
  ·
    refine ⟨125199122196597455140888139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83466081464398303427258759 125199122196597455140888139)
    ·
      refine ⟨187798683294896182711332209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125199122196597455140888139 187798683294896182711332209)
      ·
        refine ⟨140849012471172137033499157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187798683294896182711332209 140849012471172137033499157)
        ·
          refine ⟨6602297459586193923445273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140849012471172137033499157 6602297459586193923445273)
          ·
            refine ⟨4951723094689645442583955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602297459586193923445273 4951723094689645442583955)
            ·
              refine ⟨7427584642034468163875933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951723094689645442583955 7427584642034468163875933)
              ·
                refine ⟨2785344240762925561453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7427584642034468163875933 2785344240762925561453475)
                ·
                  refine ⟨4178016361144388342180213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785344240762925561453475 4178016361144388342180213)
                  ·
                    refine ⟨391689033857286407079395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4178016361144388342180213 391689033857286407079395)
                    ·
                      rfl

theorem cell23_2288435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 5].length) (baseStart_2288435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288435 prefixEnd_2288435 := by exact prefixLift 2288435
  have htrace : WordTrace (prefixWord ++ tailWord_2288435) baseStart_2288435 baseEnd_2288435 := by
    simpa [prefixWord, tailWord_2288435, baseEnd_2288435] using wordTrace_append hprefix tailTrace_2288435
  have hstable : (prefixWord ++ tailWord_2288435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288435).length < 2 ^ (prefixWord ++ tailWord_2288435).sum := by decide
  have hdescent : baseEnd_2288435 < baseStart_2288435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288458 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_2288458 : Nat := 118140960795 + 2288458 * 2 ^ 59
def prefixEnd_2288458 : Nat := 4983230072969 + 3 ^ 40 * 2288458 * 2
def baseEnd_2288458 : Nat := 1175078911626912631250579

theorem tailTrace_2288458 : CollatzResearch.WordTrace tailWord_2288458 prefixEnd_2288458 1175078911626912631250579 := by
  unfold tailWord_2288458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866730085828744588836507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55644613562209985570230685 20866730085828744588836507)
  ·
    refine ⟨31300095128743116883254761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20866730085828744588836507 31300095128743116883254761)
    ·
      refine ⟨23475071346557337662441071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31300095128743116883254761 23475071346557337662441071)
      ·
        refine ⟨35212607019836006493661607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23475071346557337662441071 35212607019836006493661607)
        ·
          refine ⟨52818910529754009740492411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35212607019836006493661607 52818910529754009740492411)
          ·
            refine ⟨79228365794631014610738617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52818910529754009740492411 79228365794631014610738617)
            ·
              refine ⟨59421274345973260958053963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79228365794631014610738617 59421274345973260958053963)
              ·
                refine ⟨89131911518959891437080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59421274345973260958053963 89131911518959891437080945)
                ·
                  refine ⟨66848933639219918577810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89131911518959891437080945 66848933639219918577810709)
                  ·
                    refine ⟨3133543764338433683334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66848933639219918577810709 3133543764338433683334877)
                    ·
                      refine ⟨1175078911626912631250579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133543764338433683334877 1175078911626912631250579)
                      ·
                        rfl

theorem cell23_2288458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_2288458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288458 prefixEnd_2288458 := by exact prefixLift 2288458
  have htrace : WordTrace (prefixWord ++ tailWord_2288458) baseStart_2288458 baseEnd_2288458 := by
    simpa [prefixWord, tailWord_2288458, baseEnd_2288458] using wordTrace_append hprefix tailTrace_2288458
  have hstable : (prefixWord ++ tailWord_2288458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288458).length < 2 ^ (prefixWord ++ tailWord_2288458).sum := by decide
  have hdescent : baseEnd_2288458 < baseStart_2288458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288557 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2288557 : Nat := 118140960795 + 2288557 * 2 ^ 59
def prefixEnd_2288557 : Nat := 4983230072969 + 3 ^ 40 * 2288557 * 2
def baseEnd_2288557 : Nat := 1175129746211707743912625

theorem tailTrace_2288557 : CollatzResearch.WordTrace tailWord_2288557 prefixEnd_2288557 1175129746211707743912625 := by
  unfold tailWord_2288557
  simp only [CollatzResearch.WordTrace]
  refine ⟨83470531169956318263199925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55647020779970878842133283 83470531169956318263199925)
  ·
    refine ⟨7825362297183404837174993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83470531169956318263199925 7825362297183404837174993)
    ·
      refine ⟨5869021722887553627881245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7825362297183404837174993 5869021722887553627881245)
      ·
        refine ⟨2200883146082832610455467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5869021722887553627881245 2200883146082832610455467)
        ·
          refine ⟨3301324719124248915683201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200883146082832610455467 3301324719124248915683201)
          ·
            refine ⟨2475993539343186686762401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3301324719124248915683201 2475993539343186686762401)
            ·
              refine ⟨1856995154507390015071801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475993539343186686762401 1856995154507390015071801)
              ·
                refine ⟨1392746365880542511303851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856995154507390015071801 1392746365880542511303851)
                ·
                  refine ⟨2089119548820813766955777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392746365880542511303851 2089119548820813766955777)
                  ·
                    refine ⟨1566839661615610325216833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089119548820813766955777 1566839661615610325216833)
                    ·
                      refine ⟨1175129746211707743912625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1566839661615610325216833 1175129746211707743912625)
                      ·
                        rfl

theorem cell23_2288557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2288557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288557 prefixEnd_2288557 := by exact prefixLift 2288557
  have htrace : WordTrace (prefixWord ++ tailWord_2288557) baseStart_2288557 baseEnd_2288557 := by
    simpa [prefixWord, tailWord_2288557, baseEnd_2288557] using wordTrace_append hprefix tailTrace_2288557
  have hstable : (prefixWord ++ tailWord_2288557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288557).length < 2 ^ (prefixWord ++ tailWord_2288557).sum := by decide
  have hdescent : baseEnd_2288557 < baseStart_2288557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288565 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2288565 : Nat := 118140960795 + 2288565 * 2 ^ 59
def prefixEnd_2288565 : Nat := 4983230072969 + 3 ^ 40 * 2288565 * 2
def baseEnd_2288565 : Nat := 1175133854056943712612587

theorem tailTrace_2288565 : CollatzResearch.WordTrace tailWord_2288565 prefixEnd_2288565 1175133854056943712612587 := by
  unfold tailWord_2288565
  simp only [CollatzResearch.WordTrace]
  refine ⟨83470822953927335629491149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55647215302618223752994099 83470822953927335629491149)
  ·
    refine ⟨31301558607722750861059181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83470822953927335629491149 31301558607722750861059181)
    ·
      refine ⟨11738084477896031572897193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31301558607722750861059181 11738084477896031572897193)
      ·
        refine ⟨8803563358422023679672895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11738084477896031572897193 8803563358422023679672895)
        ·
          refine ⟨13205345037633035519509343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8803563358422023679672895 13205345037633035519509343)
          ·
            refine ⟨19808017556449553279264015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13205345037633035519509343 19808017556449553279264015)
            ·
              refine ⟨29712026334674329918896023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19808017556449553279264015 29712026334674329918896023)
              ·
                refine ⟨44568039502011494878344035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29712026334674329918896023 44568039502011494878344035)
                ·
                  refine ⟨66852059253017242317516053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44568039502011494878344035 66852059253017242317516053)
                  ·
                    refine ⟨3133690277485183233633565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66852059253017242317516053 3133690277485183233633565)
                    ·
                      refine ⟨1175133854056943712612587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133690277485183233633565 1175133854056943712612587)
                      ·
                        rfl

theorem cell23_2288565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2288565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288565 prefixEnd_2288565 := by exact prefixLift 2288565
  have htrace : WordTrace (prefixWord ++ tailWord_2288565) baseStart_2288565 baseEnd_2288565 := by
    simpa [prefixWord, tailWord_2288565, baseEnd_2288565] using wordTrace_append hprefix tailTrace_2288565
  have hstable : (prefixWord ++ tailWord_2288565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288565).length < 2 ^ (prefixWord ++ tailWord_2288565).sum := by decide
  have hdescent : baseEnd_2288565 < baseStart_2288565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288602 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_2288602 : Nat := 118140960795 + 2288602 * 2 ^ 59
def prefixEnd_2288602 : Nat := 4983230072969 + 3 ^ 40 * 2288602 * 2
def baseEnd_2288602 : Nat := 130572539204573340872213

theorem tailTrace_2288602 : CollatzResearch.WordTrace tailWord_2288602 prefixEnd_2288602 130572539204573340872213 := by
  unfold tailWord_2288602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20868043113698322737147015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55648114969862193965725373 20868043113698322737147015)
  ·
    refine ⟨31302064670547484105720523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20868043113698322737147015 31302064670547484105720523)
    ·
      refine ⟨46953097005821226158580785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31302064670547484105720523 46953097005821226158580785)
      ·
        refine ⟨35214822754365919618935589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46953097005821226158580785 35214822754365919618935589)
        ·
          refine ⟨6602779266443609928550423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35214822754365919618935589 6602779266443609928550423)
          ·
            refine ⟨9904168899665414892825635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6602779266443609928550423 9904168899665414892825635)
            ·
              refine ⟨14856253349498122339238453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9904168899665414892825635 14856253349498122339238453)
              ·
                refine ⟨1392773751515448969303605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14856253349498122339238453 1392773751515448969303605)
                ·
                  refine ⟨130572539204573340872213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392773751515448969303605 130572539204573340872213)
                  ·
                    rfl

theorem cell23_2288602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_2288602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288602 prefixEnd_2288602 := by exact prefixLift 2288602
  have htrace : WordTrace (prefixWord ++ tailWord_2288602) baseStart_2288602 baseEnd_2288602 := by
    simpa [prefixWord, tailWord_2288602, baseEnd_2288602] using wordTrace_append hprefix tailTrace_2288602
  have hstable : (prefixWord ++ tailWord_2288602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288602).length < 2 ^ (prefixWord ++ tailWord_2288602).sum := by decide
  have hdescent : baseEnd_2288602 < baseStart_2288602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288669 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2288669 : Nat := 118140960795 + 2288669 * 2 ^ 59
def prefixEnd_2288669 : Nat := 4983230072969 + 3 ^ 40 * 2288669 * 2
def baseEnd_2288669 : Nat := 1175187256045011305712109

theorem tailTrace_2288669 : CollatzResearch.WordTrace tailWord_2288669 prefixEnd_2288669 1175187256045011305712109 := by
  unfold tailWord_2288669
  simp only [CollatzResearch.WordTrace]
  refine ⟨83474616145550561391277061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55649744097033707594184707 83474616145550561391277061)
  ·
    refine ⟨15651490527290730260864449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83474616145550561391277061 15651490527290730260864449)
    ·
      refine ⟨11738617895468047695648337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15651490527290730260864449 11738617895468047695648337)
      ·
        refine ⟨8803963421601035771736253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11738617895468047695648337 8803963421601035771736253)
        ·
          refine ⟨3301486283100388414401095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8803963421601035771736253 3301486283100388414401095)
          ·
            refine ⟨4952229424650582621601643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301486283100388414401095 4952229424650582621601643)
            ·
              refine ⟨7428344136975873932402465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952229424650582621601643 7428344136975873932402465)
              ·
                refine ⟨5571258102731905449301849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7428344136975873932402465 5571258102731905449301849)
                ·
                  refine ⟨4178443577048929086976387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5571258102731905449301849 4178443577048929086976387)
                  ·
                    refine ⟨6267665365573393630464581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178443577048929086976387 6267665365573393630464581)
                    ·
                      refine ⟨1175187256045011305712109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6267665365573393630464581 1175187256045011305712109)
                      ·
                        rfl

theorem cell23_2288669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2288669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288669 prefixEnd_2288669 := by exact prefixLift 2288669
  have htrace : WordTrace (prefixWord ++ tailWord_2288669) baseStart_2288669 baseEnd_2288669 := by
    simpa [prefixWord, tailWord_2288669, baseEnd_2288669] using wordTrace_append hprefix tailTrace_2288669
  have hstable : (prefixWord ++ tailWord_2288669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288669).length < 2 ^ (prefixWord ++ tailWord_2288669).sum := by decide
  have hdescent : baseEnd_2288669 < baseStart_2288669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288675 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 8]
def baseStart_2288675 : Nat := 118140960795 + 2288675 * 2 ^ 59
def prefixEnd_2288675 : Nat := 4983230072969 + 3 ^ 40 * 2288675 * 2
def baseEnd_2288675 : Nat := 130576704103215364693009

theorem tailTrace_2288675 : CollatzResearch.WordTrace tailWord_2288675 prefixEnd_2288675 130576704103215364693009 := by
  unfold tailWord_2288675
  simp only [CollatzResearch.WordTrace]
  refine ⟨83474834983528824415995479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55649889989019216277330319 83474834983528824415995479)
  ·
    refine ⟨125212252475293236623993219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83474834983528824415995479 125212252475293236623993219)
    ·
      refine ⟨187818378712939854935989829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125212252475293236623993219 187818378712939854935989829)
      ·
        refine ⟨35215946008676222800498093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187818378712939854935989829 35215946008676222800498093)
        ·
          refine ⟨13205979753253583550186785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35215946008676222800498093 13205979753253583550186785)
          ·
            refine ⟨9904484814940187662640089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13205979753253583550186785 9904484814940187662640089)
            ·
              refine ⟨7428363611205140746980067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9904484814940187662640089 7428363611205140746980067)
              ·
                refine ⟨11142545416807711120470101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428363611205140746980067 11142545416807711120470101)
                ·
                  refine ⟨130576704103215364693009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11142545416807711120470101 130576704103215364693009)
                  ·
                    rfl

theorem cell23_2288675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 8].length) (baseStart_2288675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288675 prefixEnd_2288675 := by exact prefixLift 2288675
  have htrace : WordTrace (prefixWord ++ tailWord_2288675) baseStart_2288675 baseEnd_2288675 := by
    simpa [prefixWord, tailWord_2288675, baseEnd_2288675] using wordTrace_append hprefix tailTrace_2288675
  have hstable : (prefixWord ++ tailWord_2288675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288675).length < 2 ^ (prefixWord ++ tailWord_2288675).sum := by decide
  have hdescent : baseEnd_2288675 < baseStart_2288675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288735 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 6]
def baseStart_2288735 : Nat := 118140960795 + 2288735 * 2 ^ 59
def prefixEnd_2288735 : Nat := 4983230072969 + 3 ^ 40 * 2288735 * 2
def baseEnd_2288735 : Nat := 391740381922736015828935

theorem tailTrace_2288735 : CollatzResearch.WordTrace tailWord_2288735 prefixEnd_2288735 391740381922736015828935 := by
  unfold tailWord_2288735
  simp only [CollatzResearch.WordTrace]
  refine ⟨83477023363311454663179659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55651348908874303108786439 83477023363311454663179659)
  ·
    refine ⟨125215535044967181994769489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83477023363311454663179659 125215535044967181994769489)
    ·
      refine ⟨93911651283725386496077117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125215535044967181994769489 93911651283725386496077117)
      ·
        refine ⟨35216869231397019936028919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93911651283725386496077117 35216869231397019936028919)
        ·
          refine ⟨52825303847095529904043379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35216869231397019936028919 52825303847095529904043379)
          ·
            refine ⟨79237955770643294856065069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52825303847095529904043379 79237955770643294856065069)
            ·
              refine ⟨29714233413991235571024401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79237955770643294856065069 29714233413991235571024401)
              ·
                refine ⟨22285675060493426678268301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29714233413991235571024401 22285675060493426678268301)
                ·
                  refine ⟨8357128147685035004350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22285675060493426678268301 8357128147685035004350613)
                  ·
                    refine ⟨391740381922736015828935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8357128147685035004350613 391740381922736015828935)
                    ·
                      rfl

theorem cell23_2288735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_2288735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288735 prefixEnd_2288735 := by exact prefixLift 2288735
  have htrace : WordTrace (prefixWord ++ tailWord_2288735) baseStart_2288735 baseEnd_2288735 := by
    simpa [prefixWord, tailWord_2288735, baseEnd_2288735] using wordTrace_append hprefix tailTrace_2288735
  have hstable : (prefixWord ++ tailWord_2288735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288735).length < 2 ^ (prefixWord ++ tailWord_2288735).sum := by decide
  have hdescent : baseEnd_2288735 < baseStart_2288735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288736 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 1, 1, 3]
def baseStart_2288736 : Nat := 118140960795 + 2288736 * 2 ^ 59
def prefixEnd_2288736 : Nat := 4983230072969 + 3 ^ 40 * 2288736 * 2
def baseEnd_2288736 : Nat := 1175221659248862543574301

theorem tailTrace_2288736 : CollatzResearch.WordTrace tailWord_2288736 prefixEnd_2288736 1175221659248862543574301 := by
  unfold tailWord_2288736
  simp only [CollatzResearch.WordTrace]
  refine ⟨41738529918153915916983031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55651373224205221222644041 41738529918153915916983031)
  ·
    refine ⟨62607794877230873875474547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41738529918153915916983031 62607794877230873875474547)
    ·
      refine ⟨93911692315846310813211821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62607794877230873875474547 93911692315846310813211821)
      ·
        refine ⟨35216884618442366554954433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93911692315846310813211821 35216884618442366554954433)
        ·
          refine ⟨26412663463831774916215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35216884618442366554954433 26412663463831774916215825)
          ·
            refine ⟨19809497597873831187161869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26412663463831774916215825 19809497597873831187161869)
            ·
              refine ⟨7428561599202686695185701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19809497597873831187161869 7428561599202686695185701)
              ·
                refine ⟨1392855299850503755347319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7428561599202686695185701 1392855299850503755347319)
                ·
                  refine ⟨2089282949775755633020979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392855299850503755347319 2089282949775755633020979)
                  ·
                    refine ⟨3133924424663633449531469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2089282949775755633020979 3133924424663633449531469)
                    ·
                      refine ⟨1175221659248862543574301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3133924424663633449531469 1175221659248862543574301)
                      ·
                        rfl

theorem cell23_2288736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_2288736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288736 prefixEnd_2288736 := by exact prefixLift 2288736
  have htrace : WordTrace (prefixWord ++ tailWord_2288736) baseStart_2288736 baseEnd_2288736 := by
    simpa [prefixWord, tailWord_2288736, baseEnd_2288736] using wordTrace_append hprefix tailTrace_2288736
  have hstable : (prefixWord ++ tailWord_2288736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288736).length < 2 ^ (prefixWord ++ tailWord_2288736).sum := by decide
  have hdescent : baseEnd_2288736 < baseStart_2288736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288752 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_2288752 : Nat := 118140960795 + 2288752 * 2 ^ 59
def prefixEnd_2288752 : Nat := 4983230072969 + 3 ^ 40 * 2288752 * 2
def baseEnd_2288752 : Nat := 391743291646444826991409

theorem tailTrace_2288752 : CollatzResearch.WordTrace tailWord_2288752 prefixEnd_2288752 391743291646444826991409 := by
  unfold tailWord_2288752
  simp only [CollatzResearch.WordTrace]
  refine ⟨41738821702124933283274255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55651762269499911044365673 41738821702124933283274255)
  ·
    refine ⟨62608232553187399924911383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41738821702124933283274255 62608232553187399924911383)
    ·
      refine ⟨93912348829781099887367075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62608232553187399924911383 93912348829781099887367075)
      ·
        refine ⟨140868523244671649831050613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93912348829781099887367075 140868523244671649831050613)
        ·
          refine ⟨13206424054187967171660995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140868523244671649831050613 13206424054187967171660995)
          ·
            refine ⟨19809636081281950757491493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13206424054187967171660995 19809636081281950757491493)
            ·
              refine ⟨3714306765240365767029655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19809636081281950757491493 3714306765240365767029655)
              ·
                refine ⟨5571460147860548650544483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3714306765240365767029655 5571460147860548650544483)
                ·
                  refine ⟨8357190221790822975816725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5571460147860548650544483 8357190221790822975816725)
                  ·
                    refine ⟨391743291646444826991409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8357190221790822975816725 391743291646444826991409)
                    ·
                      rfl

theorem cell23_2288752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_2288752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288752 prefixEnd_2288752 := by exact prefixLift 2288752
  have htrace : WordTrace (prefixWord ++ tailWord_2288752) baseStart_2288752 baseEnd_2288752 := by
    simpa [prefixWord, tailWord_2288752, baseEnd_2288752] using wordTrace_append hprefix tailTrace_2288752
  have hstable : (prefixWord ++ tailWord_2288752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288752).length < 2 ^ (prefixWord ++ tailWord_2288752).sum := by decide
  have hdescent : baseEnd_2288752 < baseStart_2288752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288773 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_2288773 : Nat := 118140960795 + 2288773 * 2 ^ 59
def prefixEnd_2288773 : Nat := 4983230072969 + 3 ^ 40 * 2288773 * 2
def baseEnd_2288773 : Nat := 391746886011026299603877

theorem tailTrace_2288773 : CollatzResearch.WordTrace tailWord_2288773 prefixEnd_2288773 391746886011026299603877 := by
  unfold tailWord_2288773
  simp only [CollatzResearch.WordTrace]
  refine ⟨83478409337173787153062973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55652272891449191435375315 83478409337173787153062973)
  ·
    refine ⟨31304403501440170182398615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83478409337173787153062973 31304403501440170182398615)
    ·
      refine ⟨46956605252160255273597923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31304403501440170182398615 46956605252160255273597923)
      ·
        refine ⟨70434907878240382910396885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46956605252160255273597923 70434907878240382910396885)
        ·
          refine ⟨1650818153396258974462427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70434907878240382910396885 1650818153396258974462427)
          ·
            refine ⟨2476227230094388461693641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650818153396258974462427 2476227230094388461693641)
            ·
              refine ⟨1857170422570791346270231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476227230094388461693641 1857170422570791346270231)
              ·
                refine ⟨2785755633856187019405347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857170422570791346270231 2785755633856187019405347)
                ·
                  refine ⟨4178633450784280529108021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785755633856187019405347 4178633450784280529108021)
                  ·
                    refine ⟨391746886011026299603877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4178633450784280529108021 391746886011026299603877)
                    ·
                      rfl

theorem cell23_2288773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_2288773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288773 prefixEnd_2288773 := by exact prefixLift 2288773
  have htrace : WordTrace (prefixWord ++ tailWord_2288773) baseStart_2288773 baseEnd_2288773 := by
    simpa [prefixWord, tailWord_2288773, baseEnd_2288773] using wordTrace_append hprefix tailTrace_2288773
  have hstable : (prefixWord ++ tailWord_2288773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288773).length < 2 ^ (prefixWord ++ tailWord_2288773).sum := by decide
  have hdescent : baseEnd_2288773 < baseStart_2288773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288776 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2288776 : Nat := 118140960795 + 2288776 * 2 ^ 59
def prefixEnd_2288776 : Nat := 4983230072969 + 3 ^ 40 * 2288776 * 2
def baseEnd_2288776 : Nat := 1175242198475042387074117

theorem tailTrace_2288776 : CollatzResearch.WordTrace tailWord_2288776 prefixEnd_2288776 1175242198475042387074117 := by
  unfold tailWord_2288776
  simp only [CollatzResearch.WordTrace]
  refine ⟨41739259378081459332711091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55652345837441945776948121 41739259378081459332711091)
  ·
    refine ⟨62608889067122188999066637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41739259378081459332711091 62608889067122188999066637)
    ·
      refine ⟨23478333400170820874649989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62608889067122188999066637 23478333400170820874649989)
      ·
        refine ⟨4402187512532028913996873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23478333400170820874649989 4402187512532028913996873)
        ·
          refine ⟨3301640634399021685497655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402187512532028913996873 3301640634399021685497655)
          ·
            refine ⟨4952460951598532528246483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301640634399021685497655 4952460951598532528246483)
            ·
              refine ⟨7428691427397798792369725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952460951598532528246483 7428691427397798792369725)
              ·
                refine ⟨2785759285274174547138647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7428691427397798792369725 2785759285274174547138647)
                ·
                  refine ⟨4178638927911261820707971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785759285274174547138647 4178638927911261820707971)
                  ·
                    refine ⟨6267958391866892731061957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178638927911261820707971 6267958391866892731061957)
                    ·
                      refine ⟨1175242198475042387074117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6267958391866892731061957 1175242198475042387074117)
                      ·
                        rfl

theorem cell23_2288776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2288776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288776 prefixEnd_2288776 := by exact prefixLift 2288776
  have htrace : WordTrace (prefixWord ++ tailWord_2288776) baseStart_2288776 baseEnd_2288776 := by
    simpa [prefixWord, tailWord_2288776, baseEnd_2288776] using wordTrace_append hprefix tailTrace_2288776
  have hstable : (prefixWord ++ tailWord_2288776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288776).length < 2 ^ (prefixWord ++ tailWord_2288776).sum := by decide
  have hdescent : baseEnd_2288776 < baseStart_2288776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288782 : List Nat := [4, 1, 1, 3, 2, 2, 10]
def baseStart_2288782 : Nat := 118140960795 + 2288782 * 2 ^ 59
def prefixEnd_2288782 : Nat := 4983230072969 + 3 ^ 40 * 2288782 * 2
def baseEnd_2288782 : Nat := 14509200979740362513569

theorem tailTrace_2288782 : CollatzResearch.WordTrace tailWord_2288782 prefixEnd_2288782 14509200979740362513569 := by
  unfold tailWord_2288782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434842199267647711267575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55652491729427454460093733 10434842199267647711267575)
  ·
    refine ⟨15652263298901471566901363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434842199267647711267575 15652263298901471566901363)
    ·
      refine ⟨23478394948352207350352045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15652263298901471566901363 23478394948352207350352045)
      ·
        refine ⟨8804398105632077756382017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23478394948352207350352045 8804398105632077756382017)
        ·
          refine ⟨6603298579224058317286513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8804398105632077756382017 6603298579224058317286513)
          ·
            refine ⟨4952473934418043737964885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603298579224058317286513 4952473934418043737964885)
            ·
              refine ⟨14509200979740362513569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4952473934418043737964885 14509200979740362513569)
              ·
                rfl

theorem cell23_2288782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 10].length) (baseStart_2288782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288782 prefixEnd_2288782 := by exact prefixLift 2288782
  have htrace : WordTrace (prefixWord ++ tailWord_2288782) baseStart_2288782 baseEnd_2288782 := by
    simpa [prefixWord, tailWord_2288782, baseEnd_2288782] using wordTrace_append hprefix tailTrace_2288782
  have hstable : (prefixWord ++ tailWord_2288782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288782).length < 2 ^ (prefixWord ++ tailWord_2288782).sum := by decide
  have hdescent : baseEnd_2288782 < baseStart_2288782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288786 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2288786 : Nat := 118140960795 + 2288786 * 2 ^ 59
def prefixEnd_2288786 : Nat := 4983230072969 + 3 ^ 40 * 2288786 * 2
def baseEnd_2288786 : Nat := 391749111093862449316357

theorem tailTrace_2288786 : CollatzResearch.WordTrace tailWord_2288786 prefixEnd_2288786 391749111093862449316357 := by
  unfold tailWord_2288786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20869720871531672593321553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55652588990751126915524141 20869720871531672593321553)
  ·
    refine ⟨15652290653648754444991165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20869720871531672593321553 15652290653648754444991165)
    ·
      refine ⟨5869608995118282916871687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15652290653648754444991165 5869608995118282916871687)
      ·
        refine ⟨8804413492677424375307531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869608995118282916871687 8804413492677424375307531)
        ·
          refine ⟨13206620239016136562961297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8804413492677424375307531 13206620239016136562961297)
          ·
            refine ⟨9904965179262102422220973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13206620239016136562961297 9904965179262102422220973)
            ·
              refine ⟨3714361942223288408332865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9904965179262102422220973 3714361942223288408332865)
              ·
                refine ⟨2785771456667466306249649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714361942223288408332865 2785771456667466306249649)
                ·
                  refine ⟨2089328592500599729687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2785771456667466306249649 2089328592500599729687237)
                  ·
                    refine ⟨391749111093862449316357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089328592500599729687237 391749111093862449316357)
                    ·
                      rfl

theorem cell23_2288786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2288786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288786 prefixEnd_2288786 := by exact prefixLift 2288786
  have htrace : WordTrace (prefixWord ++ tailWord_2288786) baseStart_2288786 baseEnd_2288786 := by
    simpa [prefixWord, tailWord_2288786, baseEnd_2288786] using wordTrace_append hprefix tailTrace_2288786
  have hstable : (prefixWord ++ tailWord_2288786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288786).length < 2 ^ (prefixWord ++ tailWord_2288786).sum := by decide
  have hdescent : baseEnd_2288786 < baseStart_2288786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288813 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2288813 : Nat := 118140960795 + 2288813 * 2 ^ 59
def prefixEnd_2288813 : Nat := 4983230072969 + 3 ^ 40 * 2288813 * 2
def baseEnd_2288813 : Nat := 1175261197259258742311447

theorem tailTrace_2288813 : CollatzResearch.WordTrace tailWord_2288813 prefixEnd_2288813 1175261197259258742311447 := by
  unfold tailWord_2288813
  simp only [CollatzResearch.WordTrace]
  refine ⟨83479868257028873984519093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55653245504685915989679395 83479868257028873984519093)
  ·
    refine ⟨7826237649096456936048665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83479868257028873984519093 7826237649096456936048665)
    ·
      refine ⟨5869678236822342702036499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7826237649096456936048665 5869678236822342702036499)
      ·
        refine ⟨8804517355233514053054749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869678236822342702036499 8804517355233514053054749)
        ·
          refine ⟨3301694008212567769895531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8804517355233514053054749 3301694008212567769895531)
          ·
            refine ⟨4952541012318851654843297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301694008212567769895531 4952541012318851654843297)
            ·
              refine ⟨3714405759239138741132473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952541012318851654843297 3714405759239138741132473)
              ·
                refine ⟨2785804319429354055849355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714405759239138741132473 2785804319429354055849355)
                ·
                  refine ⟨4178706479144031083774033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785804319429354055849355 4178706479144031083774033)
                  ·
                    refine ⟨3134029859358023312830525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4178706479144031083774033 3134029859358023312830525)
                    ·
                      refine ⟨1175261197259258742311447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3134029859358023312830525 1175261197259258742311447)
                      ·
                        rfl

theorem cell23_2288813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2288813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288813 prefixEnd_2288813 := by exact prefixLift 2288813
  have htrace : WordTrace (prefixWord ++ tailWord_2288813) baseStart_2288813 baseEnd_2288813 := by
    simpa [prefixWord, tailWord_2288813, baseEnd_2288813] using wordTrace_append hprefix tailTrace_2288813
  have hstable : (prefixWord ++ tailWord_2288813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288813).length < 2 ^ (prefixWord ++ tailWord_2288813).sum := by decide
  have hdescent : baseEnd_2288813 < baseStart_2288813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288819 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 3, 3, 2]
def baseStart_2288819 : Nat := 118140960795 + 2288819 * 2 ^ 59
def prefixEnd_2288819 : Nat := 4983230072969 + 3 ^ 40 * 2288819 * 2
def baseEnd_2288819 : Nat := 1175264278143185718836419

theorem tailTrace_2288819 : CollatzResearch.WordTrace tailWord_2288819 prefixEnd_2288819 1175264278143185718836419 := by
  unfold tailWord_2288819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83480087095007137009237511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55653391396671424672825007 83480087095007137009237511)
  ·
    refine ⟨125220130642510705513856267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83480087095007137009237511 125220130642510705513856267)
    ·
      refine ⟨187830195963766058270784401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125220130642510705513856267 187830195963766058270784401)
      ·
        refine ⟨140872646972824543703088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187830195963766058270784401 140872646972824543703088301)
        ·
          refine ⟨52827242614809203888658113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140872646972824543703088301 52827242614809203888658113)
          ·
            refine ⟨39620431961106902916493585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52827242614809203888658113 39620431961106902916493585)
            ·
              refine ⟨29715323970830177187370189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39620431961106902916493585 29715323970830177187370189)
              ·
                refine ⟨11143246489061316445263821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29715323970830177187370189 11143246489061316445263821)
                ·
                  refine ⟨4178717433397993666973933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11143246489061316445263821 4178717433397993666973933)
                  ·
                    refine ⟨1567019037524247625115225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4178717433397993666973933 1567019037524247625115225)
                    ·
                      refine ⟨1175264278143185718836419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567019037524247625115225 1175264278143185718836419)
                      ·
                        rfl

theorem cell23_2288819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3, 2].length) (baseStart_2288819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288819 prefixEnd_2288819 := by exact prefixLift 2288819
  have htrace : WordTrace (prefixWord ++ tailWord_2288819) baseStart_2288819 baseEnd_2288819 := by
    simpa [prefixWord, tailWord_2288819, baseEnd_2288819] using wordTrace_append hprefix tailTrace_2288819
  have hstable : (prefixWord ++ tailWord_2288819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288819).length < 2 ^ (prefixWord ++ tailWord_2288819).sum := by decide
  have hdescent : baseEnd_2288819 < baseStart_2288819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288872 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 9]
def baseStart_2288872 : Nat := 118140960795 + 2288872 * 2 ^ 59
def prefixEnd_2288872 : Nat := 4983230072969 + 3 ^ 40 * 2288872 * 2
def baseEnd_2288872 : Nat := 130587943624208223497075

theorem tailTrace_2288872 : CollatzResearch.WordTrace tailWord_2288872 prefixEnd_2288872 130587943624208223497075 := by
  unfold tailWord_2288872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41741010081907563530458435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55654680109210084707277913 41741010081907563530458435)
  ·
    refine ⟨62611515122861345295687653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41741010081907563530458435 62611515122861345295687653)
    ·
      refine ⟨11739659085536502242941435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62611515122861345295687653 11739659085536502242941435)
      ·
        refine ⟨17609488628304753364412153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11739659085536502242941435 17609488628304753364412153)
        ·
          refine ⟨13207116471228565023309115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17609488628304753364412153 13207116471228565023309115)
          ·
            refine ⟨19810674706842847534963673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13207116471228565023309115 19810674706842847534963673)
            ·
              refine ⟨14858006030132135651222755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19810674706842847534963673 14858006030132135651222755)
              ·
                refine ⟨22287009045198203476834133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14858006030132135651222755 22287009045198203476834133)
                ·
                  refine ⟨130587943624208223497075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22287009045198203476834133 130587943624208223497075)
                  ·
                    rfl

theorem cell23_2288872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_2288872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288872 prefixEnd_2288872 := by exact prefixLift 2288872
  have htrace : WordTrace (prefixWord ++ tailWord_2288872) baseStart_2288872 baseEnd_2288872 := by
    simpa [prefixWord, tailWord_2288872, baseEnd_2288872] using wordTrace_append hprefix tailTrace_2288872
  have hstable : (prefixWord ++ tailWord_2288872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288872).length < 2 ^ (prefixWord ++ tailWord_2288872).sum := by decide
  have hdescent : baseEnd_2288872 < baseStart_2288872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288889 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 5]
def baseStart_2288889 : Nat := 118140960795 + 2288889 * 2 ^ 59
def prefixEnd_2288889 : Nat := 4983230072969 + 3 ^ 40 * 2288889 * 2
def baseEnd_2288889 : Nat := 130588913532111160551233

theorem tailTrace_2288889 : CollatzResearch.WordTrace tailWord_2288889 prefixEnd_2288889 130588913532111160551233 := by
  unfold tailWord_2288889
  simp only [CollatzResearch.WordTrace]
  refine ⟨83482640204753538964285721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55655093469835692642857147 83482640204753538964285721)
  ·
    refine ⟨62611980153565154223214291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83482640204753538964285721 62611980153565154223214291)
    ·
      refine ⟨93917970230347731334821437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62611980153565154223214291 93917970230347731334821437)
      ·
        refine ⟨35219238836380399250558039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93917970230347731334821437 35219238836380399250558039)
        ·
          refine ⟨52828858254570598875837059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35219238836380399250558039 52828858254570598875837059)
          ·
            refine ⟨79243287381855898313755589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52828858254570598875837059 79243287381855898313755589)
            ·
              refine ⟨14858116384097980933829173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79243287381855898313755589 14858116384097980933829173)
              ·
                refine ⟨1392948411009185712546485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14858116384097980933829173 1392948411009185712546485)
                ·
                  refine ⟨130588913532111160551233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392948411009185712546485 130588913532111160551233)
                  ·
                    rfl

theorem cell23_2288889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 5].length) (baseStart_2288889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288889 prefixEnd_2288889 := by exact prefixLift 2288889
  have htrace : WordTrace (prefixWord ++ tailWord_2288889) baseStart_2288889 baseEnd_2288889 := by
    simpa [prefixWord, tailWord_2288889, baseEnd_2288889] using wordTrace_append hprefix tailTrace_2288889
  have hstable : (prefixWord ++ tailWord_2288889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288889).length < 2 ^ (prefixWord ++ tailWord_2288889).sum := by decide
  have hdescent : baseEnd_2288889 < baseStart_2288889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288900 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_2288900 : Nat := 118140960795 + 2288900 * 2 ^ 59
def prefixEnd_2288900 : Nat := 4983230072969 + 3 ^ 40 * 2288900 * 2
def baseEnd_2288900 : Nat := 1175305870076199901923547

theorem tailTrace_2288900 : CollatzResearch.WordTrace tailWord_2288900 prefixEnd_2288900 1175305870076199901923547 := by
  unfold tailWord_2288900
  simp only [CollatzResearch.WordTrace]
  refine ⟨41741520703856843921468077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55655360938475791895290769 41741520703856843921468077)
  ·
    refine ⟨15653070263946316470550529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41741520703856843921468077 15653070263946316470550529)
    ·
      refine ⟨11739802697959737352912897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15653070263946316470550529 11739802697959737352912897)
      ·
        refine ⟨8804852023469803014684673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11739802697959737352912897 8804852023469803014684673)
        ·
          refine ⟨6603639017602352261013505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8804852023469803014684673 6603639017602352261013505)
          ·
            refine ⟨4952729263201764195760129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603639017602352261013505 4952729263201764195760129)
            ·
              refine ⟨3714546947401323146820097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952729263201764195760129 3714546947401323146820097)
              ·
                refine ⟨2785910210550992360115073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714546947401323146820097 2785910210550992360115073)
                ·
                  refine ⟨2089432657913244270086305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2785910210550992360115073 2089432657913244270086305)
                  ·
                    refine ⟨1567074493434933202564729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089432657913244270086305 1567074493434933202564729)
                    ·
                      refine ⟨1175305870076199901923547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567074493434933202564729 1175305870076199901923547)
                      ·
                        rfl

theorem cell23_2288900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_2288900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288900 prefixEnd_2288900 := by exact prefixLift 2288900
  have htrace : WordTrace (prefixWord ++ tailWord_2288900) baseStart_2288900 baseEnd_2288900 := by
    simpa [prefixWord, tailWord_2288900, baseEnd_2288900] using wordTrace_append hprefix tailTrace_2288900
  have hstable : (prefixWord ++ tailWord_2288900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288900).length < 2 ^ (prefixWord ++ tailWord_2288900).sum := by decide
  have hdescent : baseEnd_2288900 < baseStart_2288900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288936 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2288936 : Nat := 118140960795 + 2288936 * 2 ^ 59
def prefixEnd_2288936 : Nat := 4983230072969 + 3 ^ 40 * 2288936 * 2
def baseEnd_2288936 : Nat := 391774785126587253691127

theorem tailTrace_2288936 : CollatzResearch.WordTrace tailWord_2288936 prefixEnd_2288936 391774785126587253691127 := by
  unfold tailWord_2288936
  simp only [CollatzResearch.WordTrace]
  refine ⟨41742177217791632995623331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55656236290388843994164441 41742177217791632995623331)
  ·
    refine ⟨62613265826687449493434997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41742177217791632995623331 62613265826687449493434997)
    ·
      refine ⟨5869993671251948390009531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62613265826687449493434997 5869993671251948390009531)
      ·
        refine ⟨8804990506877922585014297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869993671251948390009531 8804990506877922585014297)
        ·
          refine ⟨6603742880158441938760723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8804990506877922585014297 6603742880158441938760723)
          ·
            refine ⟨9905614320237662908141085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6603742880158441938760723 9905614320237662908141085)
            ·
              refine ⟨3714605370089123590552907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9905614320237662908141085 3714605370089123590552907)
              ·
                refine ⟨5571908055133685385829361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3714605370089123590552907 5571908055133685385829361)
                ·
                  refine ⟨4178931041350264039372021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5571908055133685385829361 4178931041350264039372021)
                  ·
                    refine ⟨391774785126587253691127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4178931041350264039372021 391774785126587253691127)
                    ·
                      rfl

theorem cell23_2288936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2288936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288936 prefixEnd_2288936 := by exact prefixLift 2288936
  have htrace : WordTrace (prefixWord ++ tailWord_2288936) baseStart_2288936 baseEnd_2288936 := by
    simpa [prefixWord, tailWord_2288936, baseEnd_2288936] using wordTrace_append hprefix tailTrace_2288936
  have hstable : (prefixWord ++ tailWord_2288936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288936).length < 2 ^ (prefixWord ++ tailWord_2288936).sum := by decide
  have hdescent : baseEnd_2288936 < baseStart_2288936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288956 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_2288956 : Nat := 118140960795 + 2288956 * 2 ^ 59
def prefixEnd_2288956 : Nat := 4983230072969 + 3 ^ 40 * 2288956 * 2
def baseEnd_2288956 : Nat := 1175334624992851682823289

theorem tailTrace_2288956 : CollatzResearch.WordTrace tailWord_2288956 prefixEnd_2288956 1175334624992851682823289 := by
  unfold tailWord_2288956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41742541947755404703487361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55656722597007206271316481 41742541947755404703487361)
  ·
    refine ⟨31306906460816553527615521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41742541947755404703487361 31306906460816553527615521)
    ·
      refine ⟨23480179845612415145711641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31306906460816553527615521 23480179845612415145711641)
      ·
        refine ⟨17610134884209311359283731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23480179845612415145711641 17610134884209311359283731)
        ·
          refine ⟨26415202326313967038925597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17610134884209311359283731 26415202326313967038925597)
          ·
            refine ⟨9905700872367737639597099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26415202326313967038925597 9905700872367737639597099)
            ·
              refine ⟨14858551308551606459395649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9905700872367737639597099 14858551308551606459395649)
              ·
                refine ⟨11143913481413704844546737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14858551308551606459395649 11143913481413704844546737)
                ·
                  refine ⟨8357935111060278633410053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11143913481413704844546737 8357935111060278633410053)
                  ·
                    refine ⟨1567112833323802243764385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8357935111060278633410053 1567112833323802243764385)
                    ·
                      refine ⟨1175334624992851682823289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567112833323802243764385 1175334624992851682823289)
                      ·
                        rfl

theorem cell23_2288956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_2288956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2288956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2288956 prefixEnd_2288956 := by exact prefixLift 2288956
  have htrace : WordTrace (prefixWord ++ tailWord_2288956) baseStart_2288956 baseEnd_2288956 := by
    simpa [prefixWord, tailWord_2288956, baseEnd_2288956] using wordTrace_append hprefix tailTrace_2288956
  have hstable : (prefixWord ++ tailWord_2288956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288956).length < 2 ^ (prefixWord ++ tailWord_2288956).sum := by decide
  have hdescent : baseEnd_2288956 < baseStart_2288956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289073 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_2289073 : Nat := 118140960795 + 2289073 * 2 ^ 59
def prefixEnd_2289073 : Nat := 4983230072969 + 3 ^ 40 * 2289073 * 2
def baseEnd_2289073 : Nat := 391798234076475908353417

theorem tailTrace_2289073 : CollatzResearch.WordTrace tailWord_2289073 prefixEnd_2289073 391798234076475908353417 := by
  unfold tailWord_2289073
  simp only [CollatzResearch.WordTrace]
  refine ⟨83489351236086938388983873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55659567490724625592655915 83489351236086938388983873)
  ·
    refine ⟨62617013427065203791737905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83489351236086938388983873 62617013427065203791737905)
    ·
      refine ⟨46962760070298902843803429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62617013427065203791737905 46962760070298902843803429)
      ·
        refine ⟨8805517513181044283213143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46962760070298902843803429 8805517513181044283213143)
        ·
          refine ⟨13208276269771566424819715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8805517513181044283213143 13208276269771566424819715)
          ·
            refine ⟨19812414404657349637229573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13208276269771566424819715 19812414404657349637229573)
            ·
              refine ⟨3714827700873253056980545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19812414404657349637229573 3714827700873253056980545)
              ·
                refine ⟨2786120775654939792735409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714827700873253056980545 2786120775654939792735409)
                ·
                  refine ⟨2089590581741204844551557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786120775654939792735409 2089590581741204844551557)
                  ·
                    refine ⟨391798234076475908353417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089590581741204844551557 391798234076475908353417)
                    ·
                      rfl

theorem cell23_2289073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_2289073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289073 prefixEnd_2289073 := by exact prefixLift 2289073
  have htrace : WordTrace (prefixWord ++ tailWord_2289073) baseStart_2289073 baseEnd_2289073 := by
    simpa [prefixWord, tailWord_2289073, baseEnd_2289073] using wordTrace_append hprefix tailTrace_2289073
  have hstable : (prefixWord ++ tailWord_2289073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289073).length < 2 ^ (prefixWord ++ tailWord_2289073).sum := by decide
  have hdescent : baseEnd_2289073 < baseStart_2289073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289117 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_2289117 : Nat := 118140960795 + 2289117 * 2 ^ 59
def prefixEnd_2289117 : Nat := 4983230072969 + 3 ^ 40 * 2289117 * 2
def baseEnd_2289117 : Nat := 1175417295378225552910049

theorem tailTrace_2289117 : CollatzResearch.WordTrace tailWord_2289117 prefixEnd_2289117 1175417295378225552910049 := by
  unfold tailWord_2289117
  simp only [CollatzResearch.WordTrace]
  refine ⟨83490956047927533903585605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55660637365285022602390403 83490956047927533903585605)
  ·
    refine ⟨15654554258986412606922301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83490956047927533903585605 15654554258986412606922301)
    ·
      refine ⟨5870457847119904727595863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15654554258986412606922301 5870457847119904727595863)
      ·
        refine ⟨8805686770679857091393795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5870457847119904727595863 8805686770679857091393795)
        ·
          refine ⟨13208530156019785637090693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8805686770679857091393795 13208530156019785637090693)
          ·
            refine ⟨2476599404253709806954505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13208530156019785637090693 2476599404253709806954505)
            ·
              refine ⟨1857449553190282355215879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476599404253709806954505 1857449553190282355215879)
              ·
                refine ⟨2786174329785423532823819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857449553190282355215879 2786174329785423532823819)
                ·
                  refine ⟨4179261494678135299235729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786174329785423532823819 4179261494678135299235729)
                  ·
                    refine ⟨3134446121008601474426797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4179261494678135299235729 3134446121008601474426797)
                    ·
                      refine ⟨1175417295378225552910049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3134446121008601474426797 1175417295378225552910049)
                      ·
                        rfl

theorem cell23_2289117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_2289117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289117 prefixEnd_2289117 := by exact prefixLift 2289117
  have htrace : WordTrace (prefixWord ++ tailWord_2289117) baseStart_2289117 baseEnd_2289117 := by
    simpa [prefixWord, tailWord_2289117, baseEnd_2289117] using wordTrace_append hprefix tailTrace_2289117
  have hstable : (prefixWord ++ tailWord_2289117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289117).length < 2 ^ (prefixWord ++ tailWord_2289117).sum := by decide
  have hdescent : baseEnd_2289117 < baseStart_2289117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289130 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2289130 : Nat := 118140960795 + 2289130 * 2 ^ 59
def prefixEnd_2289130 : Nat := 4983230072969 + 3 ^ 40 * 2289130 * 2
def baseEnd_2289130 : Nat := 1175423970626734002047489

theorem tailTrace_2289130 : CollatzResearch.WordTrace tailWord_2289130 prefixEnd_2289130 1175423970626734002047489 := by
  unfold tailWord_2289130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20872857549220109280952211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55660953464586958082539229 20872857549220109280952211)
  ·
    refine ⟨31309286323830163921428317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20872857549220109280952211 31309286323830163921428317)
    ·
      refine ⟨11740982371436311470535619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31309286323830163921428317 11740982371436311470535619)
      ·
        refine ⟨17611473557154467205803429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740982371436311470535619 17611473557154467205803429)
        ·
          refine ⟨3302151291966462601088143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17611473557154467205803429 3302151291966462601088143)
          ·
            refine ⟨4953226937949693901632215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302151291966462601088143 4953226937949693901632215)
            ·
              refine ⟨7429840406924540852448323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953226937949693901632215 7429840406924540852448323)
              ·
                refine ⟨11144760610386811278672485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429840406924540852448323 11144760610386811278672485)
                ·
                  refine ⟨2089642614447527114751091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11144760610386811278672485 2089642614447527114751091)
                  ·
                    refine ⟨3134463921671290672126637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2089642614447527114751091 3134463921671290672126637)
                    ·
                      refine ⟨1175423970626734002047489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3134463921671290672126637 1175423970626734002047489)
                      ·
                        rfl

theorem cell23_2289130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2289130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289130 prefixEnd_2289130 := by exact prefixLift 2289130
  have htrace : WordTrace (prefixWord ++ tailWord_2289130) baseStart_2289130 baseEnd_2289130 := by
    simpa [prefixWord, tailWord_2289130, baseEnd_2289130] using wordTrace_append hprefix tailTrace_2289130
  have hstable : (prefixWord ++ tailWord_2289130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289130).length < 2 ^ (prefixWord ++ tailWord_2289130).sum := by decide
  have hdescent : baseEnd_2289130 < baseStart_2289130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289139 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_2289139 : Nat := 118140960795 + 2289139 * 2 ^ 59
def prefixEnd_2289139 : Nat := 4983230072969 + 3 ^ 40 * 2289139 * 2
def baseEnd_2289139 : Nat := 1175428591952624466834947

theorem tailTrace_2289139 : CollatzResearch.WordTrace tailWord_2289139 prefixEnd_2289139 1175428591952624466834947 := by
  unfold tailWord_2289139
  simp only [CollatzResearch.WordTrace]
  refine ⟨83491758453847831660886471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55661172302565221107257647 83491758453847831660886471)
  ·
    refine ⟨125237637680771747491329707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83491758453847831660886471 125237637680771747491329707)
    ·
      refine ⟨187856456521157621236994561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125237637680771747491329707 187856456521157621236994561)
      ·
        refine ⟨140892342390868215927745921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187856456521157621236994561 140892342390868215927745921)
        ·
          refine ⟨105669256793151161945809441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140892342390868215927745921 105669256793151161945809441)
          ·
            refine ⟨79251942594863371459357081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105669256793151161945809441 79251942594863371459357081)
            ·
              refine ⟨59438956946147528594517811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79251942594863371459357081 59438956946147528594517811)
              ·
                refine ⟨89158435419221292891776717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59438956946147528594517811 89158435419221292891776717)
                ·
                  refine ⟨33434413282207984834416269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89158435419221292891776717 33434413282207984834416269)
                  ·
                    refine ⟨12537904980827994312906101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33434413282207984834416269 12537904980827994312906101)
                    ·
                      refine ⟨1175428591952624466834947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12537904980827994312906101 1175428591952624466834947)
                      ·
                        rfl

theorem cell23_2289139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_2289139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289139 prefixEnd_2289139 := by exact prefixLift 2289139
  have htrace : WordTrace (prefixWord ++ tailWord_2289139) baseStart_2289139 baseEnd_2289139 := by
    simpa [prefixWord, tailWord_2289139, baseEnd_2289139] using wordTrace_append hprefix tailTrace_2289139
  have hstable : (prefixWord ++ tailWord_2289139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289139).length < 2 ^ (prefixWord ++ tailWord_2289139).sum := by decide
  have hdescent : baseEnd_2289139 < baseStart_2289139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289165 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2289165 : Nat := 118140960795 + 2289165 * 2 ^ 59
def prefixEnd_2289165 : Nat := 4983230072969 + 3 ^ 40 * 2289165 * 2
def baseEnd_2289165 : Nat := 1175441942449641365109829

theorem tailTrace_2289165 : CollatzResearch.WordTrace tailWord_2289165 prefixEnd_2289165 1175441942449641365109829 := by
  unfold tailWord_2289165
  simp only [CollatzResearch.WordTrace]
  refine ⟨83492706751753638101332949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55661804501169092067555299 83492706751753638101332949)
  ·
    refine ⟨1956860314494225892999991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 83492706751753638101332949 1956860314494225892999991)
    ·
      refine ⟨2935290471741338839499987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956860314494225892999991 2935290471741338839499987)
      ·
        refine ⟨4402935707612008259249981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935290471741338839499987 4402935707612008259249981)
        ·
          refine ⟨1651100890354503097218743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4402935707612008259249981 1651100890354503097218743)
          ·
            refine ⟨2476651335531754645828115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651100890354503097218743 2476651335531754645828115)
            ·
              refine ⟨3714977003297631968742173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476651335531754645828115 3714977003297631968742173)
              ·
                refine ⟨1393116376236611988278315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714977003297631968742173 1393116376236611988278315)
                ·
                  refine ⟨2089674564354917982417473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393116376236611988278315 2089674564354917982417473)
                  ·
                    refine ⟨1567255923266188486813105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089674564354917982417473 1567255923266188486813105)
                    ·
                      refine ⟨1175441942449641365109829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567255923266188486813105 1175441942449641365109829)
                      ·
                        rfl

theorem cell23_2289165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2289165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289165 prefixEnd_2289165 := by exact prefixLift 2289165
  have htrace : WordTrace (prefixWord ++ tailWord_2289165) baseStart_2289165 baseEnd_2289165 := by
    simpa [prefixWord, tailWord_2289165, baseEnd_2289165] using wordTrace_append hprefix tailTrace_2289165
  have hstable : (prefixWord ++ tailWord_2289165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289165).length < 2 ^ (prefixWord ++ tailWord_2289165).sum := by decide
  have hdescent : baseEnd_2289165 < baseStart_2289165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289179 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_2289179 : Nat := 118140960795 + 2289179 * 2 ^ 59
def prefixEnd_2289179 : Nat := 4983230072969 + 3 ^ 40 * 2289179 * 2
def baseEnd_2289179 : Nat := 1175449131178804310334763

theorem tailTrace_2289179 : CollatzResearch.WordTrace tailWord_2289179 prefixEnd_2289179 1175449131178804310334763 := by
  unfold tailWord_2289179
  simp only [CollatzResearch.WordTrace]
  refine ⟨83493217373702918492342591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55662144915801945661561727 83493217373702918492342591)
  ·
    refine ⟨125239826060554377738513887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83493217373702918492342591 125239826060554377738513887)
    ·
      refine ⟨187859739090831566607770831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125239826060554377738513887 187859739090831566607770831)
      ·
        refine ⟨281789608636247349911656247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187859739090831566607770831 281789608636247349911656247)
        ·
          refine ⟨422684412954371024867484371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281789608636247349911656247 422684412954371024867484371)
          ·
            refine ⟨634026619431556537301226557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422684412954371024867484371 634026619431556537301226557)
            ·
              refine ⟨237759982286833701487959959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634026619431556537301226557 237759982286833701487959959)
              ·
                refine ⟨356639973430250552231939939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237759982286833701487959959 356639973430250552231939939)
                ·
                  refine ⟨534959960145375828347909909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356639973430250552231939939 534959960145375828347909909)
                  ·
                    refine ⟨25076248131814491953808277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 534959960145375828347909909 25076248131814491953808277)
                    ·
                      refine ⟨1175449131178804310334763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25076248131814491953808277 1175449131178804310334763)
                      ·
                        rfl

theorem cell23_2289179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_2289179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289179 prefixEnd_2289179 := by exact prefixLift 2289179
  have htrace : WordTrace (prefixWord ++ tailWord_2289179) baseStart_2289179 baseEnd_2289179 := by
    simpa [prefixWord, tailWord_2289179, baseEnd_2289179] using wordTrace_append hprefix tailTrace_2289179
  have hstable : (prefixWord ++ tailWord_2289179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289179).length < 2 ^ (prefixWord ++ tailWord_2289179).sum := by decide
  have hdescent : baseEnd_2289179 < baseStart_2289179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289238 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2289238 : Nat := 118140960795 + 2289238 * 2 ^ 59
def prefixEnd_2289238 : Nat := 4983230072969 + 3 ^ 40 * 2289238 * 2
def baseEnd_2289238 : Nat := 1175479426537419579496993

theorem tailTrace_2289238 : CollatzResearch.WordTrace tailWord_2289238 prefixEnd_2289238 1175479426537419579496993 := by
  unfold tailWord_2289238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218460580030573223046273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55663579520326114379160245 5218460580030573223046273)
  ·
    refine ⟨3913845435022929917284705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5218460580030573223046273 3913845435022929917284705)
    ·
      refine ⟨2935384076267197437963529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3913845435022929917284705 2935384076267197437963529)
      ·
        refine ⟨2201538057200398078472647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935384076267197437963529 2201538057200398078472647)
        ·
          refine ⟨3302307085800597117708971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201538057200398078472647 3302307085800597117708971)
          ·
            refine ⟨4953460628700895676563457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302307085800597117708971 4953460628700895676563457)
            ·
              refine ⟨3715095471525671757422593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953460628700895676563457 3715095471525671757422593)
              ·
                refine ⟨2786321603644253818066945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3715095471525671757422593 2786321603644253818066945)
                ·
                  refine ⟨2089741202733190363550209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786321603644253818066945 2089741202733190363550209)
                  ·
                    refine ⟨1567305902049892772662657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089741202733190363550209 1567305902049892772662657)
                    ·
                      refine ⟨1175479426537419579496993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567305902049892772662657 1175479426537419579496993)
                      ·
                        rfl

theorem cell23_2289238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2289238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289238 prefixEnd_2289238 := by exact prefixLift 2289238
  have htrace : WordTrace (prefixWord ++ tailWord_2289238) baseStart_2289238 baseEnd_2289238 := by
    simpa [prefixWord, tailWord_2289238, baseEnd_2289238] using wordTrace_append hprefix tailTrace_2289238
  have hstable : (prefixWord ++ tailWord_2289238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289238).length < 2 ^ (prefixWord ++ tailWord_2289238).sum := by decide
  have hdescent : baseEnd_2289238 < baseStart_2289238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289270 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2289270 : Nat := 118140960795 + 2289270 * 2 ^ 59
def prefixEnd_2289270 : Nat := 4983230072969 + 3 ^ 40 * 2289270 * 2
def baseEnd_2289270 : Nat := 391831952639454484765615

theorem tailTrace_2289270 : CollatzResearch.WordTrace tailWord_2289270 prefixEnd_2289270 391831952639454484765615 := by
  unfold tailWord_2289270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218533526023327564619079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55664357610915494022603509 5218533526023327564619079)
  ·
    refine ⟨7827800289034991346928619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218533526023327564619079 7827800289034991346928619)
    ·
      refine ⟨11741700433552487020392929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827800289034991346928619 11741700433552487020392929)
      ·
        refine ⟨8806275325164365265294697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11741700433552487020392929 8806275325164365265294697)
        ·
          refine ⟨6604706493873273948971023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8806275325164365265294697 6604706493873273948971023)
          ·
            refine ⟨9907059740809910923456535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604706493873273948971023 9907059740809910923456535)
            ·
              refine ⟨14860589611214866385184803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9907059740809910923456535 14860589611214866385184803)
              ·
                refine ⟨22290884416822299577777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14860589611214866385184803 22290884416822299577777205)
                ·
                  refine ⟨2089770414077090585416613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22290884416822299577777205 2089770414077090585416613)
                  ·
                    refine ⟨391831952639454484765615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089770414077090585416613 391831952639454484765615)
                    ·
                      rfl

theorem cell23_2289270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2289270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289270 prefixEnd_2289270 := by exact prefixLift 2289270
  have htrace : WordTrace (prefixWord ++ tailWord_2289270) baseStart_2289270 baseEnd_2289270 := by
    simpa [prefixWord, tailWord_2289270, baseEnd_2289270] using wordTrace_append hprefix tailTrace_2289270
  have hstable : (prefixWord ++ tailWord_2289270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289270).length < 2 ^ (prefixWord ++ tailWord_2289270).sum := by decide
  have hdescent : baseEnd_2289270 < baseStart_2289270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289287 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 1, 4]
def baseStart_2289287 : Nat := 118140960795 + 2289287 * 2 ^ 59
def prefixEnd_2289287 : Nat := 4983230072969 + 3 ^ 40 * 2289287 * 2
def baseEnd_2289287 : Nat := 391834862363163295928089

theorem tailTrace_2289287 : CollatzResearch.WordTrace tailWord_2289287 prefixEnd_2289287 391834862363163295928089 := by
  unfold tailWord_2289287
  simp only [CollatzResearch.WordTrace]
  refine ⟨83497156457311652937274115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55664770971541101958182743 83497156457311652937274115)
  ·
    refine ⟨125245734685967479405911173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83497156457311652937274115 125245734685967479405911173)
    ·
      refine ⟨23483575253618902388608345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125245734685967479405911173 23483575253618902388608345)
      ·
        refine ⟨17612681440214176791456259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23483575253618902388608345 17612681440214176791456259)
        ·
          refine ⟨26419022160321265187184389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17612681440214176791456259 26419022160321265187184389)
          ·
            refine ⟨4953566655060237222597073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26419022160321265187184389 4953566655060237222597073)
            ·
              refine ⟨3715174991295177916947805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953566655060237222597073 3715174991295177916947805)
              ·
                refine ⟨1393190621735691718855427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3715174991295177916947805 1393190621735691718855427)
                ·
                  refine ⟨2089785932603537578283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393190621735691718855427 2089785932603537578283141)
                  ·
                    refine ⟨391834862363163295928089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089785932603537578283141 391834862363163295928089)
                    ·
                      rfl

theorem cell23_2289287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_2289287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289287 prefixEnd_2289287 := by exact prefixLift 2289287
  have htrace : WordTrace (prefixWord ++ tailWord_2289287) baseStart_2289287 baseEnd_2289287 := by
    simpa [prefixWord, tailWord_2289287, baseEnd_2289287] using wordTrace_append hprefix tailTrace_2289287
  have hstable : (prefixWord ++ tailWord_2289287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289287).length < 2 ^ (prefixWord ++ tailWord_2289287).sum := by decide
  have hdescent : baseEnd_2289287 < baseStart_2289287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289300 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 8]
def baseStart_2289300 : Nat := 118140960795 + 2289300 * 2 ^ 59
def prefixEnd_2289300 : Nat := 4983230072969 + 3 ^ 40 * 2289300 * 2
def baseEnd_2289300 : Nat := 130612362481999815213523

theorem tailTrace_2289300 : CollatzResearch.WordTrace tailWord_2289300 prefixEnd_2289300 130612362481999815213523 := by
  unfold tailWord_2289300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41748815303132278078748677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55665087070843037438331569 41748815303132278078748677)
  ·
    refine ⟨7827902869337302139765377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41748815303132278078748677 7827902869337302139765377)
    ·
      refine ⟨5870927152002976604824033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7827902869337302139765377 5870927152002976604824033)
      ·
        refine ⟨4403195364002232453618025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5870927152002976604824033 4403195364002232453618025)
        ·
          refine ⟨3302396523001674340213519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4403195364002232453618025 3302396523001674340213519)
          ·
            refine ⟨4953594784502511510320279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302396523001674340213519 4953594784502511510320279)
            ·
              refine ⟨7430392176753767265480419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953594784502511510320279 7430392176753767265480419)
              ·
                refine ⟨11145588265130650898220629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7430392176753767265480419 11145588265130650898220629)
                ·
                  refine ⟨130612362481999815213523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11145588265130650898220629 130612362481999815213523)
                  ·
                    rfl

theorem cell23_2289300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_2289300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289300 prefixEnd_2289300 := by exact prefixLift 2289300
  have htrace : WordTrace (prefixWord ++ tailWord_2289300) baseStart_2289300 baseEnd_2289300 := by
    simpa [prefixWord, tailWord_2289300, baseEnd_2289300] using wordTrace_append hprefix tailTrace_2289300
  have hstable : (prefixWord ++ tailWord_2289300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289300).length < 2 ^ (prefixWord ++ tailWord_2289300).sum := by decide
  have hdescent : baseEnd_2289300 < baseStart_2289300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289343 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 6, 4]
def baseStart_2289343 : Nat := 118140960795 + 2289343 * 2 ^ 59
def prefixEnd_2289343 : Nat := 4983230072969 + 3 ^ 40 * 2289343 * 2
def baseEnd_2289343 : Nat := 391844447335380556228003

theorem tailTrace_2289343 : CollatzResearch.WordTrace tailWord_2289343 prefixEnd_2289343 391844447335380556228003 := by
  unfold tailWord_2289343
  simp only [CollatzResearch.WordTrace]
  refine ⟨83499198945108774501312683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55666132630072516334208455 83499198945108774501312683)
  ·
    refine ⟨125248798417663161751969025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83499198945108774501312683 125248798417663161751969025)
    ·
      refine ⟨93936598813247371313976769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125248798417663161751969025 93936598813247371313976769)
      ·
        refine ⟨70452449109935528485482577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93936598813247371313976769 70452449109935528485482577)
        ·
          refine ⟨52839336832451646364111933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70452449109935528485482577 52839336832451646364111933)
          ·
            refine ⟨19814751312169367386541975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52839336832451646364111933 19814751312169367386541975)
            ·
              refine ⟨29722126968254051079812963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19814751312169367386541975 29722126968254051079812963)
              ·
                refine ⟨44583190452381076619719445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29722126968254051079812963 44583190452381076619719445)
                ·
                  refine ⟨2089837052455362966549349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44583190452381076619719445 2089837052455362966549349)
                  ·
                    refine ⟨391844447335380556228003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089837052455362966549349 391844447335380556228003)
                    ·
                      rfl

theorem cell23_2289343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_2289343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289343 prefixEnd_2289343 := by exact prefixLift 2289343
  have htrace : WordTrace (prefixWord ++ tailWord_2289343) baseStart_2289343 baseEnd_2289343 := by
    simpa [prefixWord, tailWord_2289343, baseEnd_2289343] using wordTrace_append hprefix tailTrace_2289343
  have hstable : (prefixWord ++ tailWord_2289343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289343).length < 2 ^ (prefixWord ++ tailWord_2289343).sum := by decide
  have hdescent : baseEnd_2289343 < baseStart_2289343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289377 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2289377 : Nat := 118140960795 + 2289377 * 2 ^ 59
def prefixEnd_2289377 : Nat := 4983230072969 + 3 ^ 40 * 2289377 * 2
def baseEnd_2289377 : Nat := 391850266782798178552951

theorem tailTrace_2289377 : CollatzResearch.WordTrace tailWord_2289377 prefixEnd_2289377 391850266782798178552951 := by
  unfold tailWord_2289377
  simp only [CollatzResearch.WordTrace]
  refine ⟨83500439026985598308050385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55666959351323732205366923 83500439026985598308050385)
  ·
    refine ⟨62625329270239198731037789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83500439026985598308050385 62625329270239198731037789)
    ·
      refine ⟨23484498476339699524139171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62625329270239198731037789 23484498476339699524139171)
      ·
        refine ⟨35226747714509549286208757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23484498476339699524139171 35226747714509549286208757)
        ·
          refine ⟨3302507598235270245582071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35226747714509549286208757 3302507598235270245582071)
          ·
            refine ⟨4953761397352905368373107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302507598235270245582071 4953761397352905368373107)
            ·
              refine ⟨7430642096029358052559661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953761397352905368373107 7430642096029358052559661)
              ·
                refine ⟨2786490786011009269709873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7430642096029358052559661 2786490786011009269709873)
                ·
                  refine ⟨2089868089508256952282405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786490786011009269709873 2089868089508256952282405)
                  ·
                    refine ⟨391850266782798178552951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089868089508256952282405 391850266782798178552951)
                    ·
                      rfl

theorem cell23_2289377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2289377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289377 prefixEnd_2289377 := by exact prefixLift 2289377
  have htrace : WordTrace (prefixWord ++ tailWord_2289377) baseStart_2289377 baseEnd_2289377 := by
    simpa [prefixWord, tailWord_2289377, baseEnd_2289377] using wordTrace_append hprefix tailTrace_2289377
  have hstable : (prefixWord ++ tailWord_2289377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289377).length < 2 ^ (prefixWord ++ tailWord_2289377).sum := by decide
  have hdescent : baseEnd_2289377 < baseStart_2289377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289400 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2289400 : Nat := 118140960795 + 2289400 * 2 ^ 59
def prefixEnd_2289400 : Nat := 4983230072969 + 3 ^ 40 * 2289400 * 2
def baseEnd_2289400 : Nat := 1175562610403447945671247

theorem tailTrace_2289400 : CollatzResearch.WordTrace tailWord_2289400 prefixEnd_2289400 1175562610403447945671247 := by
  unfold tailWord_2289400
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750638952951136618068827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55667518603934848824091769 41750638952951136618068827)
  ·
    refine ⟨62625958429426704927103241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41750638952951136618068827 62625958429426704927103241)
    ·
      refine ⟨46969468822070028695327431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62625958429426704927103241 46969468822070028695327431)
      ·
        refine ⟨70454203233105043042991147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46969468822070028695327431 70454203233105043042991147)
        ·
          refine ⟨105681304849657564564486721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70454203233105043042991147 105681304849657564564486721)
          ·
            refine ⟨79260978637243173423365041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105681304849657564564486721 79260978637243173423365041)
            ·
              refine ⟨59445733977932380067523781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79260978637243173423365041 59445733977932380067523781)
              ·
                refine ⟨11146075120862321262660709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59445733977932380067523781 11146075120862321262660709)
                ·
                  refine ⟨2089889085161685236748883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11146075120862321262660709 2089889085161685236748883)
                  ·
                    refine ⟨3134833627742527855123325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2089889085161685236748883 3134833627742527855123325)
                    ·
                      refine ⟨1175562610403447945671247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3134833627742527855123325 1175562610403447945671247)
                      ·
                        rfl

theorem cell23_2289400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2289400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289400 prefixEnd_2289400 := by exact prefixLift 2289400
  have htrace : WordTrace (prefixWord ++ tailWord_2289400) baseStart_2289400 baseEnd_2289400 := by
    simpa [prefixWord, tailWord_2289400, baseEnd_2289400] using wordTrace_append hprefix tailTrace_2289400
  have hstable : (prefixWord ++ tailWord_2289400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289400).length < 2 ^ (prefixWord ++ tailWord_2289400).sum := by decide
  have hdescent : baseEnd_2289400 < baseStart_2289400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289418 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2289418 : Nat := 118140960795 + 2289418 * 2 ^ 59
def prefixEnd_2289418 : Nat := 4983230072969 + 3 ^ 40 * 2289418 * 2
def baseEnd_2289418 : Nat := 1175571853055228875246165

theorem tailTrace_2289418 : CollatzResearch.WordTrace tailWord_2289418 prefixEnd_2289418 1175571853055228875246165 := by
  unfold tailWord_2289418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20875483604959265577573227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55667956279891374873528605 20875483604959265577573227)
  ·
    refine ⟨31313225407438898366359841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20875483604959265577573227 31313225407438898366359841)
    ·
      refine ⟨23484919055579173774769881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31313225407438898366359841 23484919055579173774769881)
      ·
        refine ⟨17613689291684380331077411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23484919055579173774769881 17613689291684380331077411)
        ·
          refine ⟨26420533937526570496616117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613689291684380331077411 26420533937526570496616117)
          ·
            refine ⟨2476925056643115984057761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26420533937526570496616117 2476925056643115984057761)
            ·
              refine ⟨1857693792482336988043321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476925056643115984057761 1857693792482336988043321)
              ·
                refine ⟨1393270344361752741032491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857693792482336988043321 1393270344361752741032491)
                ·
                  refine ⟨2089905516542629111548737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393270344361752741032491 2089905516542629111548737)
                  ·
                    refine ⟨1567429137406971833661553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089905516542629111548737 1567429137406971833661553)
                    ·
                      refine ⟨1175571853055228875246165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567429137406971833661553 1175571853055228875246165)
                      ·
                        rfl

theorem cell23_2289418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2289418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289418 prefixEnd_2289418 := by exact prefixLift 2289418
  have htrace : WordTrace (prefixWord ++ tailWord_2289418) baseStart_2289418 baseEnd_2289418 := by
    simpa [prefixWord, tailWord_2289418, baseEnd_2289418] using wordTrace_append hprefix tailTrace_2289418
  have hstable : (prefixWord ++ tailWord_2289418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289418).length < 2 ^ (prefixWord ++ tailWord_2289418).sum := by decide
  have hdescent : baseEnd_2289418 < baseStart_2289418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289443 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2289443 : Nat := 118140960795 + 2289443 * 2 ^ 59
def prefixEnd_2289443 : Nat := 4983230072969 + 3 ^ 40 * 2289443 * 2
def baseEnd_2289443 : Nat := 1175584690071591277433549

theorem tailTrace_2289443 : CollatzResearch.WordTrace tailWord_2289443 prefixEnd_2289443 1175584690071591277433549 := by
  unfold tailWord_2289443
  simp only [CollatzResearch.WordTrace]
  refine ⟨83502846244746491579952983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55668564163164327719968655 83502846244746491579952983)
  ·
    refine ⟨125254269367119737369929475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83502846244746491579952983 125254269367119737369929475)
    ·
      refine ⟨187881404050679606054894213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125254269367119737369929475 187881404050679606054894213)
      ·
        refine ⟨35227763259502426135292665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187881404050679606054894213 35227763259502426135292665)
        ·
          refine ⟨26420822444626819601469499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35227763259502426135292665 26420822444626819601469499)
          ·
            refine ⟨39631233666940229402204249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26420822444626819601469499 39631233666940229402204249)
            ·
              refine ⟨29723425250205172051653187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39631233666940229402204249 29723425250205172051653187)
              ·
                refine ⟨44585137875307758077479781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29723425250205172051653187 44585137875307758077479781)
                ·
                  refine ⟨8359713351620204639527459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44585137875307758077479781 8359713351620204639527459)
                  ·
                    refine ⟨12539570027430306959291189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8359713351620204639527459 12539570027430306959291189)
                    ·
                      refine ⟨1175584690071591277433549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12539570027430306959291189 1175584690071591277433549)
                      ·
                        rfl

theorem cell23_2289443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2289443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289443 prefixEnd_2289443 := by exact prefixLift 2289443
  have htrace : WordTrace (prefixWord ++ tailWord_2289443) baseStart_2289443 baseEnd_2289443 := by
    simpa [prefixWord, tailWord_2289443, baseEnd_2289443] using wordTrace_append hprefix tailTrace_2289443
  have hstable : (prefixWord ++ tailWord_2289443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289443).length < 2 ^ (prefixWord ++ tailWord_2289443).sum := by decide
  have hdescent : baseEnd_2289443 < baseStart_2289443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289457 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_2289457 : Nat := 118140960795 + 2289457 * 2 ^ 59
def prefixEnd_2289457 : Nat := 4983230072969 + 3 ^ 40 * 2289457 * 2
def baseEnd_2289457 : Nat := 1175591878800754222658485

theorem tailTrace_2289457 : CollatzResearch.WordTrace tailWord_2289457 prefixEnd_2289457 1175591878800754222658485 := by
  unfold tailWord_2289457
  simp only [CollatzResearch.WordTrace]
  refine ⟨83503356866695771970962625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55668904577797181313975083 83503356866695771970962625)
  ·
    refine ⟨62627517650021828978221969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83503356866695771970962625 62627517650021828978221969)
    ·
      refine ⟨46970638237516371733666477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62627517650021828978221969 46970638237516371733666477)
      ·
        refine ⟨17613989339068639400124929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46970638237516371733666477 17613989339068639400124929)
        ·
          refine ⟨13210492004301479550093697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17613989339068639400124929 13210492004301479550093697)
          ·
            refine ⟨9907869003226109662570273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13210492004301479550093697 9907869003226109662570273)
            ·
              refine ⟨7430901752419582246927705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9907869003226109662570273 7430901752419582246927705)
              ·
                refine ⟨5573176314314686685195779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7430901752419582246927705 5573176314314686685195779)
                ·
                  refine ⟨8359764471472030027793669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573176314314686685195779 8359764471472030027793669)
                  ·
                    refine ⟨1567455838401005630211313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8359764471472030027793669 1567455838401005630211313)
                    ·
                      refine ⟨1175591878800754222658485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567455838401005630211313 1175591878800754222658485)
                      ·
                        rfl

theorem cell23_2289457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_2289457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289457 prefixEnd_2289457 := by exact prefixLift 2289457
  have htrace : WordTrace (prefixWord ++ tailWord_2289457) baseStart_2289457 baseEnd_2289457 := by
    simpa [prefixWord, tailWord_2289457, baseEnd_2289457] using wordTrace_append hprefix tailTrace_2289457
  have hstable : (prefixWord ++ tailWord_2289457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289457).length < 2 ^ (prefixWord ++ tailWord_2289457).sum := by decide
  have hdescent : baseEnd_2289457 < baseStart_2289457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289480 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 7]
def baseStart_2289480 : Nat := 118140960795 + 2289480 * 2 ^ 59
def prefixEnd_2289480 : Nat := 4983230072969 + 3 ^ 40 * 2289480 * 2
def baseEnd_2289480 : Nat := 130622632095089736963431

theorem tailTrace_2289480 : CollatzResearch.WordTrace tailWord_2289480 prefixEnd_2289480 130622632095089736963431 := by
  unfold tailWord_2289480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41752097872806223449524947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55669463830408297932699929 41752097872806223449524947)
  ·
    refine ⟨62628146809209335174287421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41752097872806223449524947 62628146809209335174287421)
    ·
      refine ⟨23485555053453500690357783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62628146809209335174287421 23485555053453500690357783)
      ·
        refine ⟨35228332580180251035536675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23485555053453500690357783 35228332580180251035536675)
        ·
          refine ⟨52842498870270376553305013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35228332580180251035536675 52842498870270376553305013)
          ·
            refine ⟨4953984269087847801872345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52842498870270376553305013 4953984269087847801872345)
            ·
              refine ⟨3715488201815885851404259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953984269087847801872345 3715488201815885851404259)
              ·
                refine ⟨5573232302723828777106389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715488201815885851404259 5573232302723828777106389)
                ·
                  refine ⟨130622632095089736963431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5573232302723828777106389 130622632095089736963431)
                  ·
                    rfl

theorem cell23_2289480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_2289480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289480 prefixEnd_2289480 := by exact prefixLift 2289480
  have htrace : WordTrace (prefixWord ++ tailWord_2289480) baseStart_2289480 baseEnd_2289480 := by
    simpa [prefixWord, tailWord_2289480, baseEnd_2289480] using wordTrace_append hprefix tailTrace_2289480
  have hstable : (prefixWord ++ tailWord_2289480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289480).length < 2 ^ (prefixWord ++ tailWord_2289480).sum := by decide
  have hdescent : baseEnd_2289480 < baseStart_2289480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289530 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_2289530 : Nat := 118140960795 + 2289530 * 2 ^ 59
def prefixEnd_2289530 : Nat := 4983230072969 + 3 ^ 40 * 2289530 * 2
def baseEnd_2289530 : Nat := 1175629362888532437045649

theorem tailTrace_2289530 : CollatzResearch.WordTrace tailWord_2289530 prefixEnd_2289530 1175629362888532437045649 := by
  unfold tailWord_2289530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20876504848857826359592511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55670679596954203625580029 20876504848857826359592511)
  ·
    refine ⟨31314757273286739539388767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20876504848857826359592511 31314757273286739539388767)
    ·
      refine ⟨46972135909930109309083151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31314757273286739539388767 46972135909930109309083151)
      ·
        refine ⟨70458203864895163963624727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46972135909930109309083151 70458203864895163963624727)
        ·
          refine ⟨105687305797342745945437091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70458203864895163963624727 105687305797342745945437091)
          ·
            refine ⟨158530958696014118918155637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105687305797342745945437091 158530958696014118918155637)
            ·
              refine ⟨14862277377751323648577091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158530958696014118918155637 14862277377751323648577091)
              ·
                refine ⟨22293416066626985472865637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14862277377751323648577091 22293416066626985472865637)
                ·
                  refine ⟨4180015512492559776162307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22293416066626985472865637 4180015512492559776162307)
                  ·
                    refine ⟨6270023268738839664243461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180015512492559776162307 6270023268738839664243461)
                    ·
                      refine ⟨1175629362888532437045649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6270023268738839664243461 1175629362888532437045649)
                      ·
                        rfl

theorem cell23_2289530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_2289530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289530 prefixEnd_2289530 := by exact prefixLift 2289530
  have htrace : WordTrace (prefixWord ++ tailWord_2289530) baseStart_2289530 baseEnd_2289530 := by
    simpa [prefixWord, tailWord_2289530, baseEnd_2289530] using wordTrace_append hprefix tailTrace_2289530
  have hstable : (prefixWord ++ tailWord_2289530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289530).length < 2 ^ (prefixWord ++ tailWord_2289530).sum := by decide
  have hdescent : baseEnd_2289530 < baseStart_2289530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289564 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2289564 : Nat := 118140960795 + 2289564 * 2 ^ 59
def prefixEnd_2289564 : Nat := 4983230072969 + 3 ^ 40 * 2289564 * 2
def baseEnd_2289564 : Nat := 1175646821230785304020493

theorem tailTrace_2289564 : CollatzResearch.WordTrace tailWord_2289564 prefixEnd_2289564 1175646821230785304020493 := by
  unfold tailWord_2289564
  simp only [CollatzResearch.WordTrace]
  refine ⟨41753629738654064622553873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55671506318205419496738497 41753629738654064622553873)
  ·
    refine ⟨31315222303990548466915405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41753629738654064622553873 31315222303990548466915405)
    ·
      refine ⟨11743208363996455675093277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31315222303990548466915405 11743208363996455675093277)
      ·
        refine ⟨4403703136498670878159979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11743208363996455675093277 4403703136498670878159979)
        ·
          refine ⟨6605554704748006317239969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403703136498670878159979 6605554704748006317239969)
          ·
            refine ⟨4954166028561004737929977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6605554704748006317239969 4954166028561004737929977)
            ·
              refine ⟨3715624521420753553447483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4954166028561004737929977 3715624521420753553447483)
              ·
                refine ⟨5573436782131130330171225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715624521420753553447483 5573436782131130330171225)
                ·
                  refine ⟨4180077586598347747628419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5573436782131130330171225 4180077586598347747628419)
                  ·
                    refine ⟨6270116379897521621442629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180077586598347747628419 6270116379897521621442629)
                    ·
                      refine ⟨1175646821230785304020493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6270116379897521621442629 1175646821230785304020493)
                      ·
                        rfl

theorem cell23_2289564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2289564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289564 prefixEnd_2289564 := by exact prefixLift 2289564
  have htrace : WordTrace (prefixWord ++ tailWord_2289564) baseStart_2289564 baseEnd_2289564 := by
    simpa [prefixWord, tailWord_2289564, baseEnd_2289564] using wordTrace_append hprefix tailTrace_2289564
  have hstable : (prefixWord ++ tailWord_2289564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289564).length < 2 ^ (prefixWord ++ tailWord_2289564).sum := by decide
  have hdescent : baseEnd_2289564 < baseStart_2289564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289582 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_2289582 : Nat := 118140960795 + 2289582 * 2 ^ 59
def prefixEnd_2289582 : Nat := 4983230072969 + 3 ^ 40 * 2289582 * 2
def baseEnd_2289582 : Nat := 130628451542507359288379

theorem tailTrace_2289582 : CollatzResearch.WordTrace tailWord_2289582 prefixEnd_2289582 130628451542507359288379 := by
  unfold tailWord_2289582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438489498905364789907875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55671943994161945546175333 10438489498905364789907875)
  ·
    refine ⟨15657734248358047184861813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10438489498905364789907875 15657734248358047184861813)
    ·
      refine ⟨1467912585783566923580795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15657734248358047184861813 1467912585783566923580795)
      ·
        refine ⟨2201868878675350385371193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467912585783566923580795 2201868878675350385371193)
        ·
          refine ⟨1651401659006512789028395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2201868878675350385371193 1651401659006512789028395)
          ·
            refine ⟨2477102488509769183542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651401659006512789028395 2477102488509769183542593)
            ·
              refine ⟨1857826866382326887656945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477102488509769183542593 1857826866382326887656945)
              ·
                refine ⟨1393370149786745165742709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857826866382326887656945 1393370149786745165742709)
                ·
                  refine ⟨130628451542507359288379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393370149786745165742709 130628451542507359288379)
                  ·
                    rfl

theorem cell23_2289582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_2289582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289582 prefixEnd_2289582 := by exact prefixLift 2289582
  have htrace : WordTrace (prefixWord ++ tailWord_2289582) baseStart_2289582 baseEnd_2289582 := by
    simpa [prefixWord, tailWord_2289582, baseEnd_2289582] using wordTrace_append hprefix tailTrace_2289582
  have hstable : (prefixWord ++ tailWord_2289582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289582).length < 2 ^ (prefixWord ++ tailWord_2289582).sum := by decide
  have hdescent : baseEnd_2289582 < baseStart_2289582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289600 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_2289600 : Nat := 118140960795 + 2289600 * 2 ^ 59
def prefixEnd_2289600 : Nat := 4983230072969 + 3 ^ 40 * 2289600 * 2
def baseEnd_2289600 : Nat := 391888435511449054390109

theorem tailTrace_2289600 : CollatzResearch.WordTrace tailWord_2289600 prefixEnd_2289600 391888435511449054390109 := by
  unfold tailWord_2289600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41754286252588853696709127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55672381670118471595612169 41754286252588853696709127)
  ·
    refine ⟨62631429378883280545063691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41754286252588853696709127 62631429378883280545063691)
    ·
      refine ⟨93947144068324920817595537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62631429378883280545063691 93947144068324920817595537)
      ·
        refine ⟨70460358051243690613196653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93947144068324920817595537 70460358051243690613196653)
        ·
          refine ⟨26422634269216383979948745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70460358051243690613196653 26422634269216383979948745)
          ·
            refine ⟨19816975701912287984961559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26422634269216383979948745 19816975701912287984961559)
            ·
              refine ⟨29725463552868431977442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19816975701912287984961559 29725463552868431977442339)
              ·
                refine ⟨44588195329302647966163509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29725463552868431977442339 44588195329302647966163509)
                ·
                  refine ⟨4180143312122123246827829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44588195329302647966163509 4180143312122123246827829)
                  ·
                    refine ⟨391888435511449054390109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4180143312122123246827829 391888435511449054390109)
                    ·
                      rfl

theorem cell23_2289600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_2289600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289600 prefixEnd_2289600 := by exact prefixLift 2289600
  have htrace : WordTrace (prefixWord ++ tailWord_2289600) baseStart_2289600 baseEnd_2289600 := by
    simpa [prefixWord, tailWord_2289600, baseEnd_2289600] using wordTrace_append hprefix tailTrace_2289600
  have hstable : (prefixWord ++ tailWord_2289600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289600).length < 2 ^ (prefixWord ++ tailWord_2289600).sum := by decide
  have hdescent : baseEnd_2289600 < baseStart_2289600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289607 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_2289607 : Nat := 118140960795 + 2289607 * 2 ^ 59
def prefixEnd_2289607 : Nat := 4983230072969 + 3 ^ 40 * 2289607 * 2
def baseEnd_2289607 : Nat := 1175668900898928635782795

theorem tailTrace_2289607 : CollatzResearch.WordTrace tailWord_2289607 prefixEnd_2289607 1175668900898928635782795 := by
  unfold tailWord_2289607
  simp only [CollatzResearch.WordTrace]
  refine ⟨83508827816152347588923075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55672551877434898392615383 83508827816152347588923075)
  ·
    refine ⟨125263241724228521383384613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83508827816152347588923075 125263241724228521383384613)
    ·
      refine ⟨23486857823292847759384615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125263241724228521383384613 23486857823292847759384615)
      ·
        refine ⟨35230286734939271639076923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23486857823292847759384615 35230286734939271639076923)
        ·
          refine ⟨52845430102408907458615385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35230286734939271639076923 52845430102408907458615385)
          ·
            refine ⟨39634072576806680593961539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52845430102408907458615385 39634072576806680593961539)
            ·
              refine ⟨59451108865210020890942309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39634072576806680593961539 59451108865210020890942309)
              ·
                refine ⟨11147082912226878917051683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59451108865210020890942309 11147082912226878917051683)
                ·
                  refine ⟨16720624368340318375577525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11147082912226878917051683 16720624368340318375577525)
                  ·
                    refine ⟨1567558534531904847710393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16720624368340318375577525 1567558534531904847710393)
                    ·
                      refine ⟨1175668900898928635782795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567558534531904847710393 1175668900898928635782795)
                      ·
                        rfl

theorem cell23_2289607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_2289607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289607 prefixEnd_2289607 := by exact prefixLift 2289607
  have htrace : WordTrace (prefixWord ++ tailWord_2289607) baseStart_2289607 baseEnd_2289607 := by
    simpa [prefixWord, tailWord_2289607, baseEnd_2289607] using wordTrace_append hprefix tailTrace_2289607
  have hstable : (prefixWord ++ tailWord_2289607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289607).length < 2 ^ (prefixWord ++ tailWord_2289607).sum := by decide
  have hdescent : baseEnd_2289607 < baseStart_2289607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289614 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_2289614 : Nat := 118140960795 + 2289614 * 2 ^ 59
def prefixEnd_2289614 : Nat := 4983230072969 + 3 ^ 40 * 2289614 * 2
def baseEnd_2289614 : Nat := 1175672495263510108395263

theorem tailTrace_2289614 : CollatzResearch.WordTrace tailWord_2289614 prefixEnd_2289614 1175672495263510108395263 := by
  unfold tailWord_2289614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438635390890873473053487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55672722084751325189618597 10438635390890873473053487)
  ·
    refine ⟨15657953086336310209580231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10438635390890873473053487 15657953086336310209580231)
    ·
      refine ⟨23486929629504465314370347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15657953086336310209580231 23486929629504465314370347)
      ·
        refine ⟨35230394444256697971555521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23486929629504465314370347 35230394444256697971555521)
        ·
          refine ⟨26422795833192523478666641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35230394444256697971555521 26422795833192523478666641)
          ·
            refine ⟨19817096874894392608999981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26422795833192523478666641 19817096874894392608999981)
            ·
              refine ⟨7431411328085397228374993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19817096874894392608999981 7431411328085397228374993)
              ·
                refine ⟨5573558496064047921281245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431411328085397228374993 5573558496064047921281245)
                ·
                  refine ⟨2090084436024017970480467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5573558496064047921281245 2090084436024017970480467)
                  ·
                    refine ⟨3135126654036026955720701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090084436024017970480467 3135126654036026955720701)
                    ·
                      refine ⟨1175672495263510108395263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135126654036026955720701 1175672495263510108395263)
                      ·
                        rfl

theorem cell23_2289614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_2289614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289614 prefixEnd_2289614 := by exact prefixLift 2289614
  have htrace : WordTrace (prefixWord ++ tailWord_2289614) baseStart_2289614 baseEnd_2289614 := by
    simpa [prefixWord, tailWord_2289614, baseEnd_2289614] using wordTrace_append hprefix tailTrace_2289614
  have hstable : (prefixWord ++ tailWord_2289614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289614).length < 2 ^ (prefixWord ++ tailWord_2289614).sum := by decide
  have hdescent : baseEnd_2289614 < baseStart_2289614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289618 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2289618 : Nat := 118140960795 + 2289618 * 2 ^ 59
def prefixEnd_2289618 : Nat := 4983230072969 + 3 ^ 40 * 2289618 * 2
def baseEnd_2289618 : Nat := 1175674549186128092745245

theorem tailTrace_2289618 : CollatzResearch.WordTrace tailWord_2289618 prefixEnd_2289618 1175674549186128092745245 := by
  unfold tailWord_2289618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877307254778124116893377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55672819346074997645049005 20877307254778124116893377)
  ·
    refine ⟨15657980441083593087670033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20877307254778124116893377 15657980441083593087670033)
    ·
      refine ⟨11743485330812694815752525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657980441083593087670033 11743485330812694815752525)
      ·
        refine ⟨4403806999054760555907197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11743485330812694815752525 4403806999054760555907197)
        ·
          refine ⟨1651427624645535208465199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403806999054760555907197 1651427624645535208465199)
          ·
            refine ⟨2477141436968302812697799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651427624645535208465199 2477141436968302812697799)
            ·
              refine ⟨3715712155452454219046699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477141436968302812697799 3715712155452454219046699)
              ·
                refine ⟨5573568233178681328570049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715712155452454219046699 5573568233178681328570049)
                ·
                  refine ⟨4180176174884010996427537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5573568233178681328570049 4180176174884010996427537)
                  ·
                    refine ⟨3135132131163008247320653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180176174884010996427537 3135132131163008247320653)
                    ·
                      refine ⟨1175674549186128092745245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135132131163008247320653 1175674549186128092745245)
                      ·
                        rfl

theorem cell23_2289618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2289618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289618 prefixEnd_2289618 := by exact prefixLift 2289618
  have htrace : WordTrace (prefixWord ++ tailWord_2289618) baseStart_2289618 baseEnd_2289618 := by
    simpa [prefixWord, tailWord_2289618, baseEnd_2289618] using wordTrace_append hprefix tailTrace_2289618
  have hstable : (prefixWord ++ tailWord_2289618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289618).length < 2 ^ (prefixWord ++ tailWord_2289618).sum := by decide
  have hdescent : baseEnd_2289618 < baseStart_2289618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289631 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 3]
def baseStart_2289631 : Nat := 118140960795 + 2289631 * 2 ^ 59
def prefixEnd_2289631 : Nat := 4983230072969 + 3 ^ 40 * 2289631 * 2
def baseEnd_2289631 : Nat := 1175681224434636541882685

theorem tailTrace_2289631 : CollatzResearch.WordTrace tailWord_2289631 prefixEnd_2289631 1175681224434636541882685 := by
  unfold tailWord_2289631
  simp only [CollatzResearch.WordTrace]
  refine ⟨83509703168065399687796747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55673135445376933125197831 83509703168065399687796747)
  ·
    refine ⟨125264554752098099531695121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83509703168065399687796747 125264554752098099531695121)
    ·
      refine ⟨93948416064073574648771341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125264554752098099531695121 93948416064073574648771341)
      ·
        refine ⟨35230656024027590493289253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93948416064073574648771341 35230656024027590493289253)
        ·
          refine ⟨6605748004505173217491735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35230656024027590493289253 6605748004505173217491735)
          ·
            refine ⟨9908622006757759826237603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6605748004505173217491735 9908622006757759826237603)
            ·
              refine ⟨14862933010136639739356405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9908622006757759826237603 14862933010136639739356405)
              ·
                refine ⟨1393399969700309975564663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14862933010136639739356405 1393399969700309975564663)
                ·
                  refine ⟨2090099954550464963346995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393399969700309975564663 2090099954550464963346995)
                  ·
                    refine ⟨3135149931825697445020493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090099954550464963346995 3135149931825697445020493)
                    ·
                      refine ⟨1175681224434636541882685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135149931825697445020493 1175681224434636541882685)
                      ·
                        rfl

theorem cell23_2289631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_2289631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289631 prefixEnd_2289631 := by exact prefixLift 2289631
  have htrace : WordTrace (prefixWord ++ tailWord_2289631) baseStart_2289631 baseEnd_2289631 := by
    simpa [prefixWord, tailWord_2289631, baseEnd_2289631] using wordTrace_append hprefix tailTrace_2289631
  have hstable : (prefixWord ++ tailWord_2289631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289631).length < 2 ^ (prefixWord ++ tailWord_2289631).sum := by decide
  have hdescent : baseEnd_2289631 < baseStart_2289631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289647 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 4, 4]
def baseStart_2289647 : Nat := 118140960795 + 2289647 * 2 ^ 59
def prefixEnd_2289647 : Nat := 4983230072969 + 3 ^ 40 * 2289647 * 2
def baseEnd_2289647 : Nat := 391896480041702826427537

theorem tailTrace_2289647 : CollatzResearch.WordTrace tailWord_2289647 prefixEnd_2289647 391896480041702826427537 := by
  unfold tailWord_2289647
  simp only [CollatzResearch.WordTrace]
  refine ⟨83510286736007434420379195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55673524490671622946919463 83510286736007434420379195)
  ·
    refine ⟨125265430104011151630568793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83510286736007434420379195 125265430104011151630568793)
    ·
      refine ⟨93949072578008363722926595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125265430104011151630568793 93949072578008363722926595)
      ·
        refine ⟨140923608867012545584389893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93949072578008363722926595 140923608867012545584389893)
        ·
          refine ⟨26423176662564852297073105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140923608867012545584389893 26423176662564852297073105)
          ·
            refine ⟨19817382496923639222804829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26423176662564852297073105 19817382496923639222804829)
            ·
              refine ⟨7431518436346364708551811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19817382496923639222804829 7431518436346364708551811)
              ·
                refine ⟨11147277654519547062827717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431518436346364708551811 11147277654519547062827717)
                ·
                  refine ⟨2090114560222415074280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11147277654519547062827717 2090114560222415074280197)
                  ·
                    refine ⟨391896480041702826427537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2090114560222415074280197 391896480041702826427537)
                    ·
                      rfl

theorem cell23_2289647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_2289647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289647 prefixEnd_2289647 := by exact prefixLift 2289647
  have htrace : WordTrace (prefixWord ++ tailWord_2289647) baseStart_2289647 baseEnd_2289647 := by
    simpa [prefixWord, tailWord_2289647, baseEnd_2289647] using wordTrace_append hprefix tailTrace_2289647
  have hstable : (prefixWord ++ tailWord_2289647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289647).length < 2 ^ (prefixWord ++ tailWord_2289647).sum := by decide
  have hdescent : baseEnd_2289647 < baseStart_2289647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289657 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2289657 : Nat := 118140960795 + 2289657 * 2 ^ 59
def prefixEnd_2289657 : Nat := 4983230072969 + 3 ^ 40 * 2289657 * 2
def baseEnd_2289657 : Nat := 1175694574931653440157565

theorem tailTrace_2289657 : CollatzResearch.WordTrace tailWord_2289657 prefixEnd_2289657 1175694574931653440157565 := by
  unfold tailWord_2289657
  simp only [CollatzResearch.WordTrace]
  refine ⟨83510651465971206128243225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55673767643980804085495483 83510651465971206128243225)
  ·
    refine ⟨62632988599478404596182419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83510651465971206128243225 62632988599478404596182419)
    ·
      refine ⟨93949482899217606894273629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62632988599478404596182419 93949482899217606894273629)
      ·
        refine ⟨35231056087206602585352611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93949482899217606894273629 35231056087206602585352611)
        ·
          refine ⟨52846584130809903878028917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35231056087206602585352611 52846584130809903878028917)
          ·
            refine ⟨4954367262263428488565211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52846584130809903878028917 4954367262263428488565211)
            ·
              refine ⟨7431550893395142732847817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954367262263428488565211 7431550893395142732847817)
              ·
                refine ⟨5573663170046357049635863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431550893395142732847817 5573663170046357049635863)
                ·
                  refine ⟨8360494755069535574453795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573663170046357049635863 8360494755069535574453795)
                  ·
                    refine ⟨12540742132604303361680693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8360494755069535574453795 12540742132604303361680693)
                    ·
                      refine ⟨1175694574931653440157565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12540742132604303361680693 1175694574931653440157565)
                      ·
                        rfl

theorem cell23_2289657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2289657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289657 prefixEnd_2289657 := by exact prefixLift 2289657
  have htrace : WordTrace (prefixWord ++ tailWord_2289657) baseStart_2289657 baseEnd_2289657 := by
    simpa [prefixWord, tailWord_2289657, baseEnd_2289657] using wordTrace_append hprefix tailTrace_2289657
  have hstable : (prefixWord ++ tailWord_2289657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289657).length < 2 ^ (prefixWord ++ tailWord_2289657).sum := by decide
  have hdescent : baseEnd_2289657 < baseStart_2289657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289660 : List Nat := [2, 2, 2, 1, 2, 2, 2, 10]
def baseStart_2289660 : Nat := 118140960795 + 2289660 * 2 ^ 59
def prefixEnd_2289660 : Nat := 4983230072969 + 3 ^ 40 * 2289660 * 2
def baseEnd_2289660 : Nat := 43544300569393219571113

theorem tailTrace_2289660 : CollatzResearch.WordTrace tailWord_2289660 prefixEnd_2289660 43544300569393219571113 := by
  unfold tailWord_2289660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41755380442480168820301217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55673840589973558427068289 41755380442480168820301217)
  ·
    refine ⟨31316535331860126615225913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41755380442480168820301217 31316535331860126615225913)
    ·
      refine ⟨23487401498895094961419435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31316535331860126615225913 23487401498895094961419435)
      ·
        refine ⟨35231102248342642442129153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23487401498895094961419435 35231102248342642442129153)
        ·
          refine ⟨26423326686256981831596865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35231102248342642442129153 26423326686256981831596865)
          ·
            refine ⟨19817495014692736373697649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26423326686256981831596865 19817495014692736373697649)
            ·
              refine ⟨14863121261019552280273237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19817495014692736373697649 14863121261019552280273237)
              ·
                refine ⟨43544300569393219571113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14863121261019552280273237 43544300569393219571113)
                ·
                  rfl

theorem cell23_2289660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 10].length) (baseStart_2289660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289660 prefixEnd_2289660 := by exact prefixLift 2289660
  have htrace : WordTrace (prefixWord ++ tailWord_2289660) baseStart_2289660 baseEnd_2289660 := by
    simpa [prefixWord, tailWord_2289660, baseEnd_2289660] using wordTrace_append hprefix tailTrace_2289660
  have hstable : (prefixWord ++ tailWord_2289660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289660).length < 2 ^ (prefixWord ++ tailWord_2289660).sum := by decide
  have hdescent : baseEnd_2289660 < baseStart_2289660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289671 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2289671 : Nat := 118140960795 + 2289671 * 2 ^ 59
def prefixEnd_2289671 : Nat := 4983230072969 + 3 ^ 40 * 2289671 * 2
def baseEnd_2289671 : Nat := 1175701763660816385382501

theorem tailTrace_2289671 : CollatzResearch.WordTrace tailWord_2289671 prefixEnd_2289671 1175701763660816385382501 := by
  unfold tailWord_2289671
  simp only [CollatzResearch.WordTrace]
  refine ⟨83511162087920486519252867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55674108058613657679501911 83511162087920486519252867)
  ·
    refine ⟨125266743131880729778879301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83511162087920486519252867 125266743131880729778879301)
    ·
      refine ⟨23487514337227636833539869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125266743131880729778879301 23487514337227636833539869)
      ·
        refine ⟨8807817876460363812577451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23487514337227636833539869 8807817876460363812577451)
        ·
          refine ⟨13211726814690545718866177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8807817876460363812577451 13211726814690545718866177)
          ·
            refine ⟨9908795111017909289149633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13211726814690545718866177 9908795111017909289149633)
            ·
              refine ⟨7431596333263431966862225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9908795111017909289149633 7431596333263431966862225)
              ·
                refine ⟨5573697249947573975146669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431596333263431966862225 5573697249947573975146669)
                ·
                  refine ⟨2090136468730340240680001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5573697249947573975146669 2090136468730340240680001)
                  ·
                    refine ⟨1567602351547755180510001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2090136468730340240680001 1567602351547755180510001)
                    ·
                      refine ⟨1175701763660816385382501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567602351547755180510001 1175701763660816385382501)
                      ·
                        rfl

theorem cell23_2289671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2289671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289671 prefixEnd_2289671 := by exact prefixLift 2289671
  have htrace : WordTrace (prefixWord ++ tailWord_2289671) baseStart_2289671 baseEnd_2289671 := by
    simpa [prefixWord, tailWord_2289671, baseEnd_2289671] using wordTrace_append hprefix tailTrace_2289671
  have hstable : (prefixWord ++ tailWord_2289671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289671).length < 2 ^ (prefixWord ++ tailWord_2289671).sum := by decide
  have hdescent : baseEnd_2289671 < baseStart_2289671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289767 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 7]
def baseStart_2289767 : Nat := 118140960795 + 2289767 * 2 ^ 59
def prefixEnd_2289767 : Nat := 4983230072969 + 3 ^ 40 * 2289767 * 2
def baseEnd_2289767 : Nat := 130639006422627556642451

theorem tailTrace_2289767 : CollatzResearch.WordTrace tailWord_2289767 prefixEnd_2289767 130639006422627556642451 := by
  unfold tailWord_2289767
  simp only [CollatzResearch.WordTrace]
  refine ⟨83514663495572694914747555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55676442330381796609831703 83514663495572694914747555)
  ·
    refine ⟨125271995243359042372121333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83514663495572694914747555 125271995243359042372121333)
    ·
      refine ⟨11744249554064910222386375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125271995243359042372121333 11744249554064910222386375)
      ·
        refine ⟨17616374331097365333579563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11744249554064910222386375 17616374331097365333579563)
        ·
          refine ⟨26424561496646048000369345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17616374331097365333579563 26424561496646048000369345)
          ·
            refine ⟨19818421122484536000277009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26424561496646048000369345 19818421122484536000277009)
            ·
              refine ⟨14863815841863402000207757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19818421122484536000277009 14863815841863402000207757)
              ·
                refine ⟨5573930940698775750077909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14863815841863402000207757 5573930940698775750077909)
                ·
                  refine ⟨130639006422627556642451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5573930940698775750077909 130639006422627556642451)
                  ·
                    rfl

theorem cell23_2289767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 7].length) (baseStart_2289767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289767 prefixEnd_2289767 := by exact prefixLift 2289767
  have htrace : WordTrace (prefixWord ++ tailWord_2289767) baseStart_2289767 baseEnd_2289767 := by
    simpa [prefixWord, tailWord_2289767, baseEnd_2289767] using wordTrace_append hprefix tailTrace_2289767
  have hstable : (prefixWord ++ tailWord_2289767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289767).length < 2 ^ (prefixWord ++ tailWord_2289767).sum := by decide
  have hdescent : baseEnd_2289767 < baseStart_2289767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289774 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2289774 : Nat := 118140960795 + 2289774 * 2 ^ 59
def prefixEnd_2289774 : Nat := 4983230072969 + 3 ^ 40 * 2289774 * 2
def baseEnd_2289774 : Nat := 1175754652168229482394527

theorem tailTrace_2289774 : CollatzResearch.WordTrace tailWord_2289774 prefixEnd_2289774 1175754652168229482394527 := by
  unfold tailWord_2289774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439364850818416888781547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55676612537698223406834917 10439364850818416888781547)
  ·
    refine ⟨15659047276227625333172321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10439364850818416888781547 15659047276227625333172321)
    ·
      refine ⟨11744285457170718999879241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15659047276227625333172321 11744285457170718999879241)
      ·
        refine ⟨8808214092878039249909431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11744285457170718999879241 8808214092878039249909431)
        ·
          refine ⟨13212321139317058874864147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808214092878039249909431 13212321139317058874864147)
          ·
            refine ⟨19818481708975588312296221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13212321139317058874864147 19818481708975588312296221)
            ·
              refine ⟨7431930640865845617111083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19818481708975588312296221 7431930640865845617111083)
              ·
                refine ⟨11147895961298768425666625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431930640865845617111083 11147895961298768425666625)
                ·
                  refine ⟨8360921970974076319249969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11147895961298768425666625 8360921970974076319249969)
                  ·
                    refine ⟨6270691478230557239437477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8360921970974076319249969 6270691478230557239437477)
                    ·
                      refine ⟨1175754652168229482394527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6270691478230557239437477 1175754652168229482394527)
                      ·
                        rfl

theorem cell23_2289774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2289774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289774 prefixEnd_2289774 := by exact prefixLift 2289774
  have htrace : WordTrace (prefixWord ++ tailWord_2289774) baseStart_2289774 baseEnd_2289774 := by
    simpa [prefixWord, tailWord_2289774, baseEnd_2289774] using wordTrace_append hprefix tailTrace_2289774
  have hstable : (prefixWord ++ tailWord_2289774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289774).length < 2 ^ (prefixWord ++ tailWord_2289774).sum := by decide
  have hdescent : baseEnd_2289774 < baseStart_2289774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289778 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2289778 : Nat := 118140960795 + 2289778 * 2 ^ 59
def prefixEnd_2289778 : Nat := 4983230072969 + 3 ^ 40 * 2289778 * 2
def baseEnd_2289778 : Nat := 1175756706090847466744509

theorem tailTrace_2289778 : CollatzResearch.WordTrace tailWord_2289778 prefixEnd_2289778 1175756706090847466744509 := by
  unfold tailWord_2289778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20878766174633210948349497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55676709799021895862265325 20878766174633210948349497)
  ·
    refine ⟨15659074630974908211262123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20878766174633210948349497 15659074630974908211262123)
    ·
      refine ⟨23488611946462362316893185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15659074630974908211262123 23488611946462362316893185)
      ·
        refine ⟨17616458959846771737669889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23488611946462362316893185 17616458959846771737669889)
        ·
          refine ⟨13212344219885078803252417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17616458959846771737669889 13212344219885078803252417)
          ·
            refine ⟨9909258164913809102439313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13212344219885078803252417 9909258164913809102439313)
            ·
              refine ⟨7431943623685356826829485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9909258164913809102439313 7431943623685356826829485)
              ·
                refine ⟨2786978858882008810061057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7431943623685356826829485 2786978858882008810061057)
                ·
                  refine ⟨2090234144161506607545793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786978858882008810061057 2090234144161506607545793)
                  ·
                    refine ⟨1567675608121129955659345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2090234144161506607545793 1567675608121129955659345)
                    ·
                      refine ⟨1175756706090847466744509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567675608121129955659345 1175756706090847466744509)
                      ·
                        rfl

theorem cell23_2289778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2289778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289778 prefixEnd_2289778 := by exact prefixLift 2289778
  have htrace : WordTrace (prefixWord ++ tailWord_2289778) baseStart_2289778 baseEnd_2289778 := by
    simpa [prefixWord, tailWord_2289778, baseEnd_2289778] using wordTrace_append hprefix tailTrace_2289778
  have hstable : (prefixWord ++ tailWord_2289778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289778).length < 2 ^ (prefixWord ++ tailWord_2289778).sum := by decide
  have hdescent : baseEnd_2289778 < baseStart_2289778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289868 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2289868 : Nat := 118140960795 + 2289868 * 2 ^ 59
def prefixEnd_2289868 : Nat := 4983230072969 + 3 ^ 40 * 2289868 * 2
def baseEnd_2289868 : Nat := 1175802919349752114619095

theorem tailTrace_2289868 : CollatzResearch.WordTrace tailWord_2289868 prefixEnd_2289868 1175802919349752114619095 := by
  unfold tailWord_2289868
  simp only [CollatzResearch.WordTrace]
  refine ⟨41759173634103394582087129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55678898178804526109449505 41759173634103394582087129)
  ·
    refine ⟨31319380225577545936565347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41759173634103394582087129 31319380225577545936565347)
    ·
      refine ⟨46979070338366318904848021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31319380225577545936565347 46979070338366318904848021)
      ·
        refine ⟨2202143922110921198664751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46979070338366318904848021 2202143922110921198664751)
        ·
          refine ⟨3303215883166381797997127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202143922110921198664751 3303215883166381797997127)
          ·
            refine ⟨4954823824749572696995691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303215883166381797997127 4954823824749572696995691)
            ·
              refine ⟨7432235737124359045493537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954823824749572696995691 7432235737124359045493537)
              ·
                refine ⟨5574176802843269284120153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7432235737124359045493537 5574176802843269284120153)
                ·
                  refine ⟨4180632602132451963090115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574176802843269284120153 4180632602132451963090115)
                  ·
                    refine ⟨6270948903198677944635173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180632602132451963090115 6270948903198677944635173)
                    ·
                      refine ⟨1175802919349752114619095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6270948903198677944635173 1175802919349752114619095)
                      ·
                        rfl

theorem cell23_2289868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2289868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289868 prefixEnd_2289868 := by exact prefixLift 2289868
  have htrace : WordTrace (prefixWord ++ tailWord_2289868) baseStart_2289868 baseEnd_2289868 := by
    simpa [prefixWord, tailWord_2289868, baseEnd_2289868] using wordTrace_append hprefix tailTrace_2289868
  have hstable : (prefixWord ++ tailWord_2289868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289868).length < 2 ^ (prefixWord ++ tailWord_2289868).sum := by decide
  have hdescent : baseEnd_2289868 < baseStart_2289868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289874 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_2289874 : Nat := 118140960795 + 2289874 * 2 ^ 59
def prefixEnd_2289874 : Nat := 4983230072969 + 3 ^ 40 * 2289874 * 2
def baseEnd_2289874 : Nat := 130645111137075454571563

theorem tailTrace_2289874 : CollatzResearch.WordTrace tailWord_2289874 prefixEnd_2289874 130645111137075454571563 := by
  unfold tailWord_2289874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20879641526546263047223169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55679044070790034792595117 20879641526546263047223169)
  ·
    refine ⟨15659731144909697285417377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20879641526546263047223169 15659731144909697285417377)
    ·
      refine ⟨11744798358682272964063033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15659731144909697285417377 11744798358682272964063033)
      ·
        refine ⟨8808598769011704723047275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11744798358682272964063033 8808598769011704723047275)
        ·
          refine ⟨13212898153517557084570913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808598769011704723047275 13212898153517557084570913)
          ·
            refine ⟨9909673615138167813428185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13212898153517557084570913 9909673615138167813428185)
            ·
              refine ⟨7432255211353625860071139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9909673615138167813428185 7432255211353625860071139)
              ·
                refine ⟨11148382817030438790106709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7432255211353625860071139 11148382817030438790106709)
                ·
                  refine ⟨130645111137075454571563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11148382817030438790106709 130645111137075454571563)
                  ·
                    rfl

theorem cell23_2289874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_2289874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289874 prefixEnd_2289874 := by exact prefixLift 2289874
  have htrace : WordTrace (prefixWord ++ tailWord_2289874) baseStart_2289874 baseEnd_2289874 := by
    simpa [prefixWord, tailWord_2289874, baseEnd_2289874] using wordTrace_append hprefix tailTrace_2289874
  have hstable : (prefixWord ++ tailWord_2289874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289874).length < 2 ^ (prefixWord ++ tailWord_2289874).sum := by decide
  have hdescent : baseEnd_2289874 < baseStart_2289874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289887 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 9]
def baseStart_2289887 : Nat := 118140960795 + 2289887 * 2 ^ 59
def prefixEnd_2289887 : Nat := 4983230072969 + 3 ^ 40 * 2289887 * 2
def baseEnd_2289887 : Nat := 391937558494062513427169

theorem tailTrace_2289887 : CollatzResearch.WordTrace tailWord_2289887 prefixEnd_2289887 391937558494062513427169 := by
  unfold tailWord_2289887
  simp only [CollatzResearch.WordTrace]
  refine ⟨83519040255137955409115915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55679360170091970272743943 83519040255137955409115915)
  ·
    refine ⟨125278560382706933113673873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83519040255137955409115915 125278560382706933113673873)
    ·
      refine ⟨93958920287030199835255405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125278560382706933113673873 93958920287030199835255405)
      ·
        refine ⟨35234595107636324938220777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93958920287030199835255405 35234595107636324938220777)
        ·
          refine ⟨26425946330727243703665583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35234595107636324938220777 26425946330727243703665583)
          ·
            refine ⟨39638919496090865555498375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26425946330727243703665583 39638919496090865555498375)
            ·
              refine ⟨59458379244136298333247563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39638919496090865555498375 59458379244136298333247563)
              ·
                refine ⟨89187568866204447499871345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59458379244136298333247563 89187568866204447499871345)
                ·
                  refine ⟨66890676649653335624903509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89187568866204447499871345 66890676649653335624903509)
                  ·
                    refine ⟨391937558494062513427169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66890676649653335624903509 391937558494062513427169)
                    ·
                      rfl

theorem cell23_2289887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_2289887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289887 prefixEnd_2289887 := by exact prefixLift 2289887
  have htrace : WordTrace (prefixWord ++ tailWord_2289887) baseStart_2289887 baseEnd_2289887 := by
    simpa [prefixWord, tailWord_2289887, baseEnd_2289887] using wordTrace_append hprefix tailTrace_2289887
  have hstable : (prefixWord ++ tailWord_2289887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289887).length < 2 ^ (prefixWord ++ tailWord_2289887).sum := by decide
  have hdescent : baseEnd_2289887 < baseStart_2289887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289897 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_2289897 : Nat := 118140960795 + 2289897 * 2 ^ 59
def prefixEnd_2289897 : Nat := 4983230072969 + 3 ^ 40 * 2289897 * 2
def baseEnd_2289897 : Nat := 1175817810288732501156461

theorem tailTrace_2289897 : CollatzResearch.WordTrace tailWord_2289897 prefixEnd_2289897 1175817810288732501156461 := by
  unfold tailWord_2289897
  simp only [CollatzResearch.WordTrace]
  refine ⟨83519404985101727116979945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55679603323401151411319963 83519404985101727116979945)
  ·
    refine ⟨62639553738826295337734959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83519404985101727116979945 62639553738826295337734959)
    ·
      refine ⟨93959330608239443006602439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62639553738826295337734959 93959330608239443006602439)
      ·
        refine ⟨140938995912359164509903659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93959330608239443006602439 140938995912359164509903659)
        ·
          refine ⟨211408493868538746764855489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140938995912359164509903659 211408493868538746764855489)
          ·
            refine ⟨158556370401404060073641617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211408493868538746764855489 158556370401404060073641617)
            ·
              refine ⟨118917277801053045055231213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158556370401404060073641617 118917277801053045055231213)
              ·
                refine ⟨44593979175394891895711705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118917277801053045055231213 44593979175394891895711705)
                ·
                  refine ⟨33445484381546168921783779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44593979175394891895711705 33445484381546168921783779)
                  ·
                    refine ⟨50168226572319253382675669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33445484381546168921783779 50168226572319253382675669)
                    ·
                      refine ⟨1175817810288732501156461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50168226572319253382675669 1175817810288732501156461)
                      ·
                        rfl

theorem cell23_2289897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_2289897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289897 prefixEnd_2289897 := by exact prefixLift 2289897
  have htrace : WordTrace (prefixWord ++ tailWord_2289897) baseStart_2289897 baseEnd_2289897 := by
    simpa [prefixWord, tailWord_2289897, baseEnd_2289897] using wordTrace_append hprefix tailTrace_2289897
  have hstable : (prefixWord ++ tailWord_2289897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289897).length < 2 ^ (prefixWord ++ tailWord_2289897).sum := by decide
  have hdescent : baseEnd_2289897 < baseStart_2289897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289928 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_2289928 : Nat := 118140960795 + 2289928 * 2 ^ 59
def prefixEnd_2289928 : Nat := 4983230072969 + 3 ^ 40 * 2289928 * 2
def baseEnd_2289928 : Nat := 1175833728189021879868819

theorem tailTrace_2289928 : CollatzResearch.WordTrace tailWord_2289928 prefixEnd_2289928 1175833728189021879868819 := by
  unfold tailWord_2289928
  simp only [CollatzResearch.WordTrace]
  refine ⟨41760267823994709705679219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55680357098659612940905625 41760267823994709705679219)
  ·
    refine ⟨62640401735992064558518829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41760267823994709705679219 62640401735992064558518829)
    ·
      refine ⟨23490150650997024209444561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62640401735992064558518829 23490150650997024209444561)
      ·
        refine ⟨17617612988247768157083421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23490150650997024209444561 17617612988247768157083421)
        ·
          refine ⟨6606604870592913058906283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17617612988247768157083421 6606604870592913058906283)
          ·
            refine ⟨9909907305889369588359425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6606604870592913058906283 9909907305889369588359425)
            ·
              refine ⟨7432430479417027191269569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9909907305889369588359425 7432430479417027191269569)
              ·
                refine ⟨5574322859562770393452177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7432430479417027191269569 5574322859562770393452177)
                ·
                  refine ⟨4180742144672077795089133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574322859562770393452177 4180742144672077795089133)
                  ·
                    refine ⟨1567778304252029173158425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4180742144672077795089133 1567778304252029173158425)
                    ·
                      refine ⟨1175833728189021879868819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567778304252029173158425 1175833728189021879868819)
                      ·
                        rfl

theorem cell23_2289928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_2289928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289928 prefixEnd_2289928 := by exact prefixLift 2289928
  have htrace : WordTrace (prefixWord ++ tailWord_2289928) baseStart_2289928 baseEnd_2289928 := by
    simpa [prefixWord, tailWord_2289928, baseEnd_2289928] using wordTrace_append hprefix tailTrace_2289928
  have hstable : (prefixWord ++ tailWord_2289928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289928).length < 2 ^ (prefixWord ++ tailWord_2289928).sum := by decide
  have hdescent : baseEnd_2289928 < baseStart_2289928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289934 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2289934 : Nat := 118140960795 + 2289934 * 2 ^ 59
def prefixEnd_2289934 : Nat := 4983230072969 + 3 ^ 40 * 2289934 * 2
def baseEnd_2289934 : Nat := 391945603024316285464597

theorem tailTrace_2289934 : CollatzResearch.WordTrace tailWord_2289934 prefixEnd_2289934 391945603024316285464597 := by
  unfold tailWord_2289934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440094310745960304509607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55680502990645121624051237 10440094310745960304509607)
  ·
    refine ⟨15660141466118940456764411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10440094310745960304509607 15660141466118940456764411)
    ·
      refine ⟨23490212199178410685146617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15660141466118940456764411 23490212199178410685146617)
      ·
        refine ⟨17617659149383808013859963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23490212199178410685146617 17617659149383808013859963)
        ·
          refine ⟨26426488724075712020789945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17617659149383808013859963 26426488724075712020789945)
          ·
            refine ⟨19819866543056784015592459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26426488724075712020789945 19819866543056784015592459)
            ·
              refine ⟨29729799814585176023388689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19819866543056784015592459 29729799814585176023388689)
              ·
                refine ⟨22297349860938882017541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29729799814585176023388689 22297349860938882017541517)
                ·
                  refine ⟨8361506197852080756578069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22297349860938882017541517 8361506197852080756578069)
                  ·
                    refine ⟨391945603024316285464597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8361506197852080756578069 391945603024316285464597)
                    ·
                      rfl

theorem cell23_2289934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2289934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289934 prefixEnd_2289934 := by exact prefixLift 2289934
  have htrace : WordTrace (prefixWord ++ tailWord_2289934) baseStart_2289934 baseEnd_2289934 := by
    simpa [prefixWord, tailWord_2289934, baseEnd_2289934] using wordTrace_append hprefix tailTrace_2289934
  have hstable : (prefixWord ++ tailWord_2289934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289934).length < 2 ^ (prefixWord ++ tailWord_2289934).sum := by decide
  have hdescent : baseEnd_2289934 < baseStart_2289934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289944 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2289944 : Nat := 118140960795 + 2289944 * 2 ^ 59
def prefixEnd_2289944 : Nat := 4983230072969 + 3 ^ 40 * 2289944 * 2
def baseEnd_2289944 : Nat := 1175841943879493817268745

theorem tailTrace_2289944 : CollatzResearch.WordTrace tailWord_2289944 prefixEnd_2289944 1175841943879493817268745 := by
  unfold tailWord_2289944
  simp only [CollatzResearch.WordTrace]
  refine ⟨41760559607965727071970443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55680746143954302762627257 41760559607965727071970443)
  ·
    refine ⟨62640839411948590607955665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41760559607965727071970443 62640839411948590607955665)
    ·
      refine ⟨46980629558961442955966749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62640839411948590607955665 46980629558961442955966749)
      ·
        refine ⟨17617736084610541108487531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46980629558961442955966749 17617736084610541108487531)
        ·
          refine ⟨26426604126915811662731297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17617736084610541108487531 26426604126915811662731297)
          ·
            refine ⟨19819953095186858747048473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26426604126915811662731297 19819953095186858747048473)
            ·
              refine ⟨14864964821390144060286355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19819953095186858747048473 14864964821390144060286355)
              ·
                refine ⟨22297447232085216090429533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14864964821390144060286355 22297447232085216090429533)
                ·
                  refine ⟨8361542712031956033911075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22297447232085216090429533 8361542712031956033911075)
                  ·
                    refine ⟨12542314068047934050866613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8361542712031956033911075 12542314068047934050866613)
                    ·
                      refine ⟨1175841943879493817268745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12542314068047934050866613 1175841943879493817268745)
                      ·
                        rfl

theorem cell23_2289944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2289944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289944 prefixEnd_2289944 := by exact prefixLift 2289944
  have htrace : WordTrace (prefixWord ++ tailWord_2289944) baseStart_2289944 baseEnd_2289944 := by
    simpa [prefixWord, tailWord_2289944, baseEnd_2289944] using wordTrace_append hprefix tailTrace_2289944
  have hstable : (prefixWord ++ tailWord_2289944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289944).length < 2 ^ (prefixWord ++ tailWord_2289944).sum := by decide
  have hdescent : baseEnd_2289944 < baseStart_2289944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289951 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 6]
def baseStart_2289951 : Nat := 118140960795 + 2289951 * 2 ^ 59
def prefixEnd_2289951 : Nat := 4983230072969 + 3 ^ 40 * 2289951 * 2
def baseEnd_2289951 : Nat := 391948512748025096627071

theorem tailTrace_2289951 : CollatzResearch.WordTrace tailWord_2289951 prefixEnd_2289951 391948512748025096627071 := by
  unfold tailWord_2289951
  simp only [CollatzResearch.WordTrace]
  refine ⟨83521374526906094339445707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55680916351270729559630471 83521374526906094339445707)
  ·
    refine ⟨125282061790359141509168561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83521374526906094339445707 125282061790359141509168561)
    ·
      refine ⟨93961546342769356131876421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125282061790359141509168561 93961546342769356131876421)
      ·
        refine ⟨17617789939269254274726829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93961546342769356131876421 17617789939269254274726829)
        ·
          refine ⟨6606671227225970353022561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17617789939269254274726829 6606671227225970353022561)
          ·
            refine ⟨4955003420419477764766921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6606671227225970353022561 4955003420419477764766921)
            ·
              refine ⟨3716252565314608323575191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955003420419477764766921 3716252565314608323575191)
              ·
                refine ⟨5574378847971912485362787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716252565314608323575191 5574378847971912485362787)
                ·
                  refine ⟨8361568271957868728044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574378847971912485362787 8361568271957868728044181)
                  ·
                    refine ⟨391948512748025096627071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8361568271957868728044181 391948512748025096627071)
                    ·
                      rfl

theorem cell23_2289951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_2289951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289951 prefixEnd_2289951 := by exact prefixLift 2289951
  have htrace : WordTrace (prefixWord ++ tailWord_2289951) baseStart_2289951 baseEnd_2289951 := by
    simpa [prefixWord, tailWord_2289951, baseEnd_2289951] using wordTrace_append hprefix tailTrace_2289951
  have hstable : (prefixWord ++ tailWord_2289951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289951).length < 2 ^ (prefixWord ++ tailWord_2289951).sum := by decide
  have hdescent : baseEnd_2289951 < baseStart_2289951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289962 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2289962 : Nat := 118140960795 + 2289962 * 2 ^ 59
def prefixEnd_2289962 : Nat := 4983230072969 + 3 ^ 40 * 2289962 * 2
def baseEnd_2289962 : Nat := 1175851186531274746843663

theorem tailTrace_2289962 : CollatzResearch.WordTrace tailWord_2289962 prefixEnd_2289962 1175851186531274746843663 := by
  unfold tailWord_2289962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880443932466560804524035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55681183819910828812064093 20880443932466560804524035)
  ·
    refine ⟨31320665898699841206786053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20880443932466560804524035 31320665898699841206786053)
    ·
      refine ⟨5872624856006220226272385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31320665898699841206786053 5872624856006220226272385)
      ·
        refine ⟨4404468642004665169704289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5872624856006220226272385 4404468642004665169704289)
        ·
          refine ⟨3303351481503498877278217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404468642004665169704289 3303351481503498877278217)
          ·
            refine ⟨2477513611127624157958663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303351481503498877278217 2477513611127624157958663)
            ·
              refine ⟨3716270416691436236937995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477513611127624157958663 3716270416691436236937995)
              ·
                refine ⟨5574405625037154355406993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716270416691436236937995 5574405625037154355406993)
                ·
                  refine ⟨4180804218777865766555245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574405625037154355406993 4180804218777865766555245)
                  ·
                    refine ⟨1567801582041699662458217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4180804218777865766555245 1567801582041699662458217)
                    ·
                      refine ⟨1175851186531274746843663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567801582041699662458217 1175851186531274746843663)
                      ·
                        rfl

theorem cell23_2289962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2289962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289962 prefixEnd_2289962 := by exact prefixLift 2289962
  have htrace : WordTrace (prefixWord ++ tailWord_2289962) baseStart_2289962 baseEnd_2289962 := by
    simpa [prefixWord, tailWord_2289962, baseEnd_2289962] using wordTrace_append hprefix tailTrace_2289962
  have hstable : (prefixWord ++ tailWord_2289962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289962).length < 2 ^ (prefixWord ++ tailWord_2289962).sum := by decide
  have hdescent : baseEnd_2289962 < baseStart_2289962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289978 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_2289978 : Nat := 118140960795 + 2289978 * 2 ^ 59
def prefixEnd_2289978 : Nat := 4983230072969 + 3 ^ 40 * 2289978 * 2
def baseEnd_2289978 : Nat := 1175859402221746684243589

theorem tailTrace_2289978 : CollatzResearch.WordTrace tailWord_2289978 prefixEnd_2289978 1175859402221746684243589 := by
  unfold tailWord_2289978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880589824452069487669647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55681572865205518633785725 20880589824452069487669647)
  ·
    refine ⟨31320884736678104231504471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20880589824452069487669647 31320884736678104231504471)
    ·
      refine ⟨46981327105017156347256707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31320884736678104231504471 46981327105017156347256707)
      ·
        refine ⟨70471990657525734520885061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46981327105017156347256707 70471990657525734520885061)
        ·
          refine ⟨13213498248286075222665949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70471990657525734520885061 13213498248286075222665949)
          ·
            refine ⟨4955061843107278208499731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13213498248286075222665949 4955061843107278208499731)
            ·
              refine ⟨7432592764660917312749597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955061843107278208499731 7432592764660917312749597)
              ·
                refine ⟨2787222286747843992281099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7432592764660917312749597 2787222286747843992281099)
                ·
                  refine ⟨4180833430121765988421649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787222286747843992281099 4180833430121765988421649)
                  ·
                    refine ⟨3135625072591324491316237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180833430121765988421649 3135625072591324491316237)
                    ·
                      refine ⟨1175859402221746684243589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135625072591324491316237 1175859402221746684243589)
                      ·
                        rfl

theorem cell23_2289978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_2289978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2289978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2289978 prefixEnd_2289978 := by exact prefixLift 2289978
  have htrace : WordTrace (prefixWord ++ tailWord_2289978) baseStart_2289978 baseEnd_2289978 := by
    simpa [prefixWord, tailWord_2289978, baseEnd_2289978] using wordTrace_append hprefix tailTrace_2289978
  have hstable : (prefixWord ++ tailWord_2289978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289978).length < 2 ^ (prefixWord ++ tailWord_2289978).sum := by decide
  have hdescent : baseEnd_2289978 < baseStart_2289978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290005 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2290005 : Nat := 118140960795 + 2290005 * 2 ^ 59
def prefixEnd_2290005 : Nat := 4983230072969 + 3 ^ 40 * 2290005 * 2
def baseEnd_2290005 : Nat := 1175873266199418078605965

theorem tailTrace_2290005 : CollatzResearch.WordTrace tailWord_2290005 prefixEnd_2290005 1175873266199418078605965 := by
  unfold tailWord_2290005
  simp only [CollatzResearch.WordTrace]
  refine ⟨83523344068710461561911469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55682229379140307707940979 83523344068710461561911469)
  ·
    refine ⟨31321254025766423085716801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83523344068710461561911469 31321254025766423085716801)
    ·
      refine ⟨23490940519324817314287601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31321254025766423085716801 23490940519324817314287601)
      ·
        refine ⟨17618205389493612985715701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23490940519324817314287601 17618205389493612985715701)
        ·
          refine ⟨1651706755265026217410847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17618205389493612985715701 1651706755265026217410847)
          ·
            refine ⟨2477560132897539326116271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651706755265026217410847 2477560132897539326116271)
            ·
              refine ⟨3716340199346308989174407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477560132897539326116271 3716340199346308989174407)
              ·
                refine ⟨5574510299019463483761611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716340199346308989174407 5574510299019463483761611)
                ·
                  refine ⟨8361765448529195225642417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574510299019463483761611 8361765448529195225642417)
                  ·
                    refine ⟨6271324086396896419231813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8361765448529195225642417 6271324086396896419231813)
                    ·
                      refine ⟨1175873266199418078605965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6271324086396896419231813 1175873266199418078605965)
                      ·
                        rfl

theorem cell23_2290005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2290005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290005 prefixEnd_2290005 := by exact prefixLift 2290005
  have htrace : WordTrace (prefixWord ++ tailWord_2290005) baseStart_2290005 baseEnd_2290005 := by
    simpa [prefixWord, tailWord_2290005, baseEnd_2290005] using wordTrace_append hprefix tailTrace_2290005
  have hstable : (prefixWord ++ tailWord_2290005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290005).length < 2 ^ (prefixWord ++ tailWord_2290005).sum := by decide
  have hdescent : baseEnd_2290005 < baseStart_2290005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290012 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2290012 : Nat := 118140960795 + 2290012 * 2 ^ 59
def prefixEnd_2290012 : Nat := 4983230072969 + 3 ^ 40 * 2290012 * 2
def baseEnd_2290012 : Nat := 1175876860563999551218433

theorem tailTrace_2290012 : CollatzResearch.WordTrace tailWord_2290012 prefixEnd_2290012 1175876860563999551218433 := by
  unfold tailWord_2290012
  simp only [CollatzResearch.WordTrace]
  refine ⟨41761799689842550878708145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55682399586456734504944193 41761799689842550878708145)
  ·
    refine ⟨31321349767381913159031109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41761799689842550878708145 31321349767381913159031109)
    ·
      refine ⟨5872753081384108717318333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31321349767381913159031109 5872753081384108717318333)
      ·
        refine ⟨2202282405519040768994375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5872753081384108717318333 2202282405519040768994375)
        ·
          refine ⟨3303423608278561153491563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202282405519040768994375 3303423608278561153491563)
          ·
            refine ⟨4955135412417841730237345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303423608278561153491563 4955135412417841730237345)
            ·
              refine ⟨3716351559313381297678009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955135412417841730237345 3716351559313381297678009)
              ·
                refine ⟨2787263669485035973258507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716351559313381297678009 2787263669485035973258507)
                ·
                  refine ⟨4180895504227553959887761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787263669485035973258507 4180895504227553959887761)
                  ·
                    refine ⟨3135671628170665469915821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180895504227553959887761 3135671628170665469915821)
                    ·
                      refine ⟨1175876860563999551218433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135671628170665469915821 1175876860563999551218433)
                      ·
                        rfl

theorem cell23_2290012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2290012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290012 prefixEnd_2290012 := by exact prefixLift 2290012
  have htrace : WordTrace (prefixWord ++ tailWord_2290012) baseStart_2290012 baseEnd_2290012 := by
    simpa [prefixWord, tailWord_2290012, baseEnd_2290012] using wordTrace_append hprefix tailTrace_2290012
  have hstable : (prefixWord ++ tailWord_2290012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290012).length < 2 ^ (prefixWord ++ tailWord_2290012).sum := by decide
  have hdescent : baseEnd_2290012 < baseStart_2290012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290044 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2290044 : Nat := 118140960795 + 2290044 * 2 ^ 59
def prefixEnd_2290044 : Nat := 4983230072969 + 3 ^ 40 * 2290044 * 2
def baseEnd_2290044 : Nat := 1175893291944943426018285

theorem tailTrace_2290044 : CollatzResearch.WordTrace tailWord_2290044 prefixEnd_2290044 1175893291944943426018285 := by
  unfold tailWord_2290044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41762383257784585611290593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55683177677046114148387457 41762383257784585611290593)
  ·
    refine ⟨31321787443338439208467945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41762383257784585611290593 31321787443338439208467945)
    ·
      refine ⟨23491340582503829406350959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31321787443338439208467945 23491340582503829406350959)
      ·
        refine ⟨35237010873755744109526439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23491340582503829406350959 35237010873755744109526439)
        ·
          refine ⟨52855516310633616164289659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35237010873755744109526439 52855516310633616164289659)
          ·
            refine ⟨79283274465950424246434489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52855516310633616164289659 79283274465950424246434489)
            ·
              refine ⟨59462455849462818184825867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79283274465950424246434489 59462455849462818184825867)
              ·
                refine ⟨89193683774194227277238801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59462455849462818184825867 89193683774194227277238801)
                ·
                  refine ⟨66895262830645670457929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89193683774194227277238801 66895262830645670457929101)
                  ·
                    refine ⟨25085723561492126421723413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66895262830645670457929101 25085723561492126421723413)
                    ·
                      refine ⟨1175893291944943426018285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25085723561492126421723413 1175893291944943426018285)
                      ·
                        rfl

theorem cell23_2290044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2290044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290044 prefixEnd_2290044 := by exact prefixLift 2290044
  have htrace : WordTrace (prefixWord ++ tailWord_2290044) baseStart_2290044 baseEnd_2290044 := by
    simpa [prefixWord, tailWord_2290044, baseEnd_2290044] using wordTrace_append hprefix tailTrace_2290044
  have hstable : (prefixWord ++ tailWord_2290044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290044).length < 2 ^ (prefixWord ++ tailWord_2290044).sum := by decide
  have hdescent : baseEnd_2290044 < baseStart_2290044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290105 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 5]
def baseStart_2290105 : Nat := 118140960795 + 2290105 * 2 ^ 59
def prefixEnd_2290105 : Nat := 4983230072969 + 3 ^ 40 * 2290105 * 2
def baseEnd_2290105 : Nat := 130658290473874187483945

theorem tailTrace_2290105 : CollatzResearch.WordTrace tailWord_2290105 prefixEnd_2290105 130658290473874187483945 := by
  unfold tailWord_2290105
  simp only [CollatzResearch.WordTrace]
  refine ⟨83526991368348178640551769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55684660912232119093701179 83526991368348178640551769)
  ·
    refine ⟨62645243526261133980413827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83526991368348178640551769 62645243526261133980413827)
    ·
      refine ⟨93967865289391700970620741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62645243526261133980413827 93967865289391700970620741)
      ·
        refine ⟨17618974741760943931991389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93967865289391700970620741 17618974741760943931991389)
        ·
          refine ⟨6607115528160353974496771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17618974741760943931991389 6607115528160353974496771)
          ·
            refine ⟨9910673292240530961745157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6607115528160353974496771 9910673292240530961745157)
            ·
              refine ⟨1858251242295099555327217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9910673292240530961745157 1858251242295099555327217)
              ·
                refine ⟨1393688431721324666495413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858251242295099555327217 1393688431721324666495413)
                ·
                  refine ⟨130658290473874187483945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393688431721324666495413 130658290473874187483945)
                  ·
                    rfl

theorem cell23_2290105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 5].length) (baseStart_2290105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290105 prefixEnd_2290105 := by exact prefixLift 2290105
  have htrace : WordTrace (prefixWord ++ tailWord_2290105) baseStart_2290105 baseEnd_2290105 := by
    simpa [prefixWord, tailWord_2290105, baseEnd_2290105] using wordTrace_append hprefix tailTrace_2290105
  have hstable : (prefixWord ++ tailWord_2290105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290105).length < 2 ^ (prefixWord ++ tailWord_2290105).sum := by decide
  have hdescent : baseEnd_2290105 < baseStart_2290105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290121 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_2290121 : Nat := 118140960795 + 2290121 * 2 ^ 59
def prefixEnd_2290121 : Nat := 4983230072969 + 3 ^ 40 * 2290121 * 2
def baseEnd_2290121 : Nat := 1175932829955339624755431

theorem tailTrace_2290121 : CollatzResearch.WordTrace tailWord_2290121 prefixEnd_2290121 1175932829955339624755431 := by
  unfold tailWord_2290121
  simp only [CollatzResearch.WordTrace]
  refine ⟨83527574936290213373134217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55685049957526808915422811 83527574936290213373134217)
  ·
    refine ⟨62645681202217660029850663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83527574936290213373134217 62645681202217660029850663)
    ·
      refine ⟨93968521803326490044775995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62645681202217660029850663 93968521803326490044775995)
      ·
        refine ⟨140952782704989735067163993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93968521803326490044775995 140952782704989735067163993)
        ·
          refine ⟨105714587028742301300372995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140952782704989735067163993 105714587028742301300372995)
          ·
            refine ⟨158571880543113451950559493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105714587028742301300372995 158571880543113451950559493)
            ·
              refine ⟨29732227601833772240729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158571880543113451950559493 29732227601833772240729905)
              ·
                refine ⟨22299170701375329180547429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29732227601833772240729905 22299170701375329180547429)
                ·
                  refine ⟨4181094506507874221352643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22299170701375329180547429 4181094506507874221352643)
                  ·
                    refine ⟨6271641759761811332028965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181094506507874221352643 6271641759761811332028965)
                    ·
                      refine ⟨1175932829955339624755431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6271641759761811332028965 1175932829955339624755431)
                      ·
                        rfl

theorem cell23_2290121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_2290121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290121 prefixEnd_2290121 := by exact prefixLift 2290121
  have htrace : WordTrace (prefixWord ++ tailWord_2290121) baseStart_2290121 baseEnd_2290121 := by
    simpa [prefixWord, tailWord_2290121, baseEnd_2290121] using wordTrace_append hprefix tailTrace_2290121
  have hstable : (prefixWord ++ tailWord_2290121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290121).length < 2 ^ (prefixWord ++ tailWord_2290121).sum := by decide
  have hdescent : baseEnd_2290121 < baseStart_2290121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290138 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_2290138 : Nat := 118140960795 + 2290138 * 2 ^ 59
def prefixEnd_2290138 : Nat := 4983230072969 + 3 ^ 40 * 2290138 * 2
def baseEnd_2290138 : Nat := 1175941559126466058242853

theorem tailTrace_2290138 : CollatzResearch.WordTrace tailWord_2290138 prefixEnd_2290138 1175941559126466058242853 := by
  unfold tailWord_2290138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882048744307156319125767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55685463318152416851002045 20882048744307156319125767)
  ·
    refine ⟨31323073116460734478688651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20882048744307156319125767 31323073116460734478688651)
    ·
      refine ⟨46984609674691101718032977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31323073116460734478688651 46984609674691101718032977)
      ·
        refine ⟨35238457256018326288524733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46984609674691101718032977 35238457256018326288524733)
        ·
          refine ⟨13214421471006872358196775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35238457256018326288524733 13214421471006872358196775)
          ·
            refine ⟨19821632206510308537295163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13214421471006872358196775 19821632206510308537295163)
            ·
              refine ⟨29732448309765462805942745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19821632206510308537295163 29732448309765462805942745)
              ·
                refine ⟨22299336232324097104457059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29732448309765462805942745 22299336232324097104457059)
                ·
                  refine ⟨33449004348486145656685589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22299336232324097104457059 33449004348486145656685589)
                  ·
                    refine ⟨1567922078835288077657137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33449004348486145656685589 1567922078835288077657137)
                    ·
                      refine ⟨1175941559126466058242853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1567922078835288077657137 1175941559126466058242853)
                      ·
                        rfl

theorem cell23_2290138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_2290138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290138 prefixEnd_2290138 := by exact prefixLift 2290138
  have htrace : WordTrace (prefixWord ++ tailWord_2290138) baseStart_2290138 baseEnd_2290138 := by
    simpa [prefixWord, tailWord_2290138, baseEnd_2290138] using wordTrace_append hprefix tailTrace_2290138
  have hstable : (prefixWord ++ tailWord_2290138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290138).length < 2 ^ (prefixWord ++ tailWord_2290138).sum := by decide
  have hdescent : baseEnd_2290138 < baseStart_2290138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290151 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2290151 : Nat := 118140960795 + 2290151 * 2 ^ 59
def prefixEnd_2290151 : Nat := 4983230072969 + 3 ^ 40 * 2290151 * 2
def baseEnd_2290151 : Nat := 1175948234374974507380293

theorem tailTrace_2290151 : CollatzResearch.WordTrace tailWord_2290151 prefixEnd_2290151 1175948234374974507380293 := by
  unfold tailWord_2290151
  simp only [CollatzResearch.WordTrace]
  refine ⟨83528669126181528496726307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55685779417454352331150871 83528669126181528496726307)
  ·
    refine ⟨125293003689272292745089461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83528669126181528496726307 125293003689272292745089461)
    ·
      refine ⟨11746219095869277444852137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125293003689272292745089461 11746219095869277444852137)
      ·
        refine ⟨8809664321901958083639103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11746219095869277444852137 8809664321901958083639103)
        ·
          refine ⟨13214496482852937125458655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8809664321901958083639103 13214496482852937125458655)
          ·
            refine ⟨19821744724279405688187983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13214496482852937125458655 19821744724279405688187983)
            ·
              refine ⟨29732617086419108532281975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19821744724279405688187983 29732617086419108532281975)
              ·
                refine ⟨44598925629628662798422963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29732617086419108532281975 44598925629628662798422963)
                ·
                  refine ⟨66898388444442994197634445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44598925629628662798422963 66898388444442994197634445)
                  ·
                    refine ⟨25086895666666122824112917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66898388444442994197634445 25086895666666122824112917)
                    ·
                      refine ⟨1175948234374974507380293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25086895666666122824112917 1175948234374974507380293)
                      ·
                        rfl

theorem cell23_2290151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2290151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290151 prefixEnd_2290151 := by exact prefixLift 2290151
  have htrace : WordTrace (prefixWord ++ tailWord_2290151) baseStart_2290151 baseEnd_2290151 := by
    simpa [prefixWord, tailWord_2290151, baseEnd_2290151] using wordTrace_append hprefix tailTrace_2290151
  have hstable : (prefixWord ++ tailWord_2290151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290151).length < 2 ^ (prefixWord ++ tailWord_2290151).sum := by decide
  have hdescent : baseEnd_2290151 < baseStart_2290151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290161 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 8]
def baseStart_2290161 : Nat := 118140960795 + 2290161 * 2 ^ 59
def prefixEnd_2290161 : Nat := 4983230072969 + 3 ^ 40 * 2290161 * 2
def baseEnd_2290161 : Nat := 130661485464613274250583

theorem tailTrace_2290161 : CollatzResearch.WordTrace tailWord_2290161 prefixEnd_2290161 130661485464613274250583 := by
  unfold tailWord_2290161
  simp only [CollatzResearch.WordTrace]
  refine ⟨83529033856145300204590337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55686022570763533469726891 83529033856145300204590337)
  ·
    refine ⟨62646775392108975153442753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83529033856145300204590337 62646775392108975153442753)
    ·
      refine ⟨46985081544081731365082065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62646775392108975153442753 46985081544081731365082065)
      ·
        refine ⟨35238811158061298523811549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46985081544081731365082065 35238811158061298523811549)
        ·
          refine ⟨13214554184272986946429331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35238811158061298523811549 13214554184272986946429331)
          ·
            refine ⟨19821831276409480419643997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13214554184272986946429331 19821831276409480419643997)
            ·
              refine ⟨7433186728653555157366499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19821831276409480419643997 7433186728653555157366499)
              ·
                refine ⟨11149780092980332736049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433186728653555157366499 11149780092980332736049749)
                ·
                  refine ⟨130661485464613274250583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11149780092980332736049749 130661485464613274250583)
                  ·
                    rfl

theorem cell23_2290161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_2290161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290161 prefixEnd_2290161 := by exact prefixLift 2290161
  have htrace : WordTrace (prefixWord ++ tailWord_2290161) baseStart_2290161 baseEnd_2290161 := by
    simpa [prefixWord, tailWord_2290161, baseEnd_2290161] using wordTrace_append hprefix tailTrace_2290161
  have hstable : (prefixWord ++ tailWord_2290161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290161).length < 2 ^ (prefixWord ++ tailWord_2290161).sum := by decide
  have hdescent : baseEnd_2290161 < baseStart_2290161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290171 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3]
def baseStart_2290171 : Nat := 118140960795 + 2290171 * 2 ^ 59
def prefixEnd_2290171 : Nat := 4983230072969 + 3 ^ 40 * 2290171 * 2
def baseEnd_2290171 : Nat := 1175958503988064429130201

theorem tailTrace_2290171 : CollatzResearch.WordTrace tailWord_2290171 prefixEnd_2290171 1175958503988064429130201 := by
  unfold tailWord_2290171
  simp only [CollatzResearch.WordTrace]
  refine ⟨83529398586109071912454367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55686265724072714608302911 83529398586109071912454367)
  ·
    refine ⟨125294097879163607868681551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83529398586109071912454367 125294097879163607868681551)
    ·
      refine ⟨187941146818745411803022327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125294097879163607868681551 187941146818745411803022327)
      ·
        refine ⟨281911720228118117704533491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187941146818745411803022327 281911720228118117704533491)
        ·
          refine ⟨422867580342177176556800237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281911720228118117704533491 422867580342177176556800237)
          ·
            refine ⟨158575342628316441208800089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422867580342177176556800237 158575342628316441208800089)
            ·
              refine ⟨118931506971237330906600067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158575342628316441208800089 118931506971237330906600067)
              ·
                refine ⟨178397260456855996359900101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118931506971237330906600067 178397260456855996359900101)
                ·
                  refine ⟨33449486335660499317481269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178397260456855996359900101 33449486335660499317481269)
                  ·
                    refine ⟨3135889343968171811013869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33449486335660499317481269 3135889343968171811013869)
                    ·
                      refine ⟨1175958503988064429130201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3135889343968171811013869 1175958503988064429130201)
                      ·
                        rfl

theorem cell23_2290171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].length) (baseStart_2290171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290171 prefixEnd_2290171 := by exact prefixLift 2290171
  have htrace : WordTrace (prefixWord ++ tailWord_2290171) baseStart_2290171 baseEnd_2290171 := by
    simpa [prefixWord, tailWord_2290171, baseEnd_2290171] using wordTrace_append hprefix tailTrace_2290171
  have hstable : (prefixWord ++ tailWord_2290171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290171).length < 2 ^ (prefixWord ++ tailWord_2290171).sum := by decide
  have hdescent : baseEnd_2290171 < baseStart_2290171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290245 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_2290245 : Nat := 118140960795 + 2290245 * 2 ^ 59
def prefixEnd_2290245 : Nat := 4983230072969 + 3 ^ 40 * 2290245 * 2
def baseEnd_2290245 : Nat := 1175996501556497139604861

theorem tailTrace_2290245 : CollatzResearch.WordTrace tailWord_2290245 prefixEnd_2290245 1175996501556497139604861 := by
  unfold tailWord_2290245
  simp only [CollatzResearch.WordTrace]
  refine ⟨83532097587840982550648189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55688065058560655033765459 83532097587840982550648189)
  ·
    refine ⟨31324536595440368456493071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83532097587840982550648189 31324536595440368456493071)
    ·
      refine ⟨46986804893160552684739607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31324536595440368456493071 46986804893160552684739607)
      ·
        refine ⟨70480207339740829027109411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46986804893160552684739607 70480207339740829027109411)
        ·
          refine ⟨105720311009611243540664117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70480207339740829027109411 105720311009611243540664117)
          ·
            refine ⟨9911279157151054081937261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105720311009611243540664117 9911279157151054081937261)
            ·
              refine ⟨3716729683931645280726473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9911279157151054081937261 3716729683931645280726473)
              ·
                refine ⟨2787547262948733960544855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716729683931645280726473 2787547262948733960544855)
                ·
                  refine ⟨4181320894423100940817283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787547262948733960544855 4181320894423100940817283)
                  ·
                    refine ⟨6271981341634651411225925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181320894423100940817283 6271981341634651411225925)
                    ·
                      refine ⟨1175996501556497139604861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6271981341634651411225925 1175996501556497139604861)
                      ·
                        rfl

theorem cell23_2290245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_2290245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290245 prefixEnd_2290245 := by exact prefixLift 2290245
  have htrace : WordTrace (prefixWord ++ tailWord_2290245) baseStart_2290245 baseEnd_2290245 := by
    simpa [prefixWord, tailWord_2290245, baseEnd_2290245] using wordTrace_append hprefix tailTrace_2290245
  have hstable : (prefixWord ++ tailWord_2290245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290245).length < 2 ^ (prefixWord ++ tailWord_2290245).sum := by decide
  have hdescent : baseEnd_2290245 < baseStart_2290245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290251 : List Nat := [1, 1, 1, 1, 3, 1, 6, 9]
def baseStart_2290251 : Nat := 118140960795 + 2290251 * 2 ^ 59
def prefixEnd_2290251 : Nat := 4983230072969 + 3 ^ 40 * 2290251 * 2
def baseEnd_2290251 : Nat := 43555540090386078375179

theorem tailTrace_2290251 : CollatzResearch.WordTrace tailWord_2290251 prefixEnd_2290251 43555540090386078375179 := by
  unfold tailWord_2290251
  simp only [CollatzResearch.WordTrace]
  refine ⟨83532316425819245575366607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55688210950546163716911071 83532316425819245575366607)
  ·
    refine ⟨125298474638728868363049911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83532316425819245575366607 125298474638728868363049911)
    ·
      refine ⟨187947711958093302544574867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125298474638728868363049911 187947711958093302544574867)
      ·
        refine ⟨281921567937139953816862301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187947711958093302544574867 281921567937139953816862301)
        ·
          refine ⟨105720587976427482681323363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281921567937139953816862301 105720587976427482681323363)
          ·
            refine ⟨158580881964641224021985045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105720587976427482681323363 158580881964641224021985045)
            ·
              refine ⟨7433478842092557376030549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158580881964641224021985045 7433478842092557376030549)
              ·
                refine ⟨43555540090386078375179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7433478842092557376030549 43555540090386078375179)
                ·
                  rfl

theorem cell23_2290251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 9].length) (baseStart_2290251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290251 prefixEnd_2290251 := by exact prefixLift 2290251
  have htrace : WordTrace (prefixWord ++ tailWord_2290251) baseStart_2290251 baseEnd_2290251 := by
    simpa [prefixWord, tailWord_2290251, baseEnd_2290251] using wordTrace_append hprefix tailTrace_2290251
  have hstable : (prefixWord ++ tailWord_2290251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290251).length < 2 ^ (prefixWord ++ tailWord_2290251).sum := by decide
  have hdescent : baseEnd_2290251 < baseStart_2290251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290268 : List Nat := [2, 2, 4, 1, 3, 11]
def baseStart_2290268 : Nat := 118140960795 + 2290268 * 2 ^ 59
def prefixEnd_2290268 : Nat := 4983230072969 + 3 ^ 40 * 2290268 * 2
def baseEnd_2290268 : Nat := 4839540377002265636285

theorem tailTrace_2290268 : CollatzResearch.WordTrace tailWord_2290268 prefixEnd_2290268 4839540377002265636285 := by
  unfold tailWord_2290268
  simp only [CollatzResearch.WordTrace]
  refine ⟨41766468233378828739367729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55688624311171771652490305 41766468233378828739367729)
  ·
    refine ⟨31324851175034121554525797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41766468233378828739367729 31324851175034121554525797)
    ·
      refine ⟨5873409595318897791473587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31324851175034121554525797 5873409595318897791473587)
      ·
        refine ⟨8810114392978346687210381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873409595318897791473587 8810114392978346687210381)
        ·
          refine ⟨3303792897366880007703893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8810114392978346687210381 3303792897366880007703893)
          ·
            refine ⟨4839540377002265636285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3303792897366880007703893 4839540377002265636285)
            ·
              rfl

theorem cell23_2290268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 11].length) (baseStart_2290268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290268 prefixEnd_2290268 := by exact prefixLift 2290268
  have htrace : WordTrace (prefixWord ++ tailWord_2290268) baseStart_2290268 baseEnd_2290268 := by
    simpa [prefixWord, tailWord_2290268, baseEnd_2290268] using wordTrace_append hprefix tailTrace_2290268
  have hstable : (prefixWord ++ tailWord_2290268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290268).length < 2 ^ (prefixWord ++ tailWord_2290268).sum := by decide
  have hdescent : baseEnd_2290268 < baseStart_2290268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290285 : List Nat := [1, 5, 1, 1, 3, 3, 1, 8]
def baseStart_2290285 : Nat := 118140960795 + 2290285 * 2 ^ 59
def prefixEnd_2290285 : Nat := 4983230072969 + 3 ^ 40 * 2290285 * 2
def baseEnd_2290285 : Nat := 43556186695654703077951

theorem tailTrace_2290285 : CollatzResearch.WordTrace tailWord_2290285 prefixEnd_2290285 43556186695654703077951 := by
  unfold tailWord_2290285
  simp only [CollatzResearch.WordTrace]
  refine ⟨83533556507696069382104309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55689037671797379588069539 83533556507696069382104309)
  ·
    refine ⟨7831270922596506504572279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83533556507696069382104309 7831270922596506504572279)
    ·
      refine ⟨11746906383894759756858419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831270922596506504572279 11746906383894759756858419)
      ·
        refine ⟨17620359575842139635287629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11746906383894759756858419 17620359575842139635287629)
        ·
          refine ⟨6607634840940802363232861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17620359575842139635287629 6607634840940802363232861)
          ·
            refine ⟨2477863065352800886212323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6607634840940802363232861 2477863065352800886212323)
            ·
              refine ⟨3716794598029201329318485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477863065352800886212323 3716794598029201329318485)
              ·
                refine ⟨43556186695654703077951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3716794598029201329318485 43556186695654703077951)
                ·
                  rfl

theorem cell23_2290285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 8].length) (baseStart_2290285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290285 prefixEnd_2290285 := by exact prefixLift 2290285
  have htrace : WordTrace (prefixWord ++ tailWord_2290285) baseStart_2290285 baseEnd_2290285 := by
    simpa [prefixWord, tailWord_2290285, baseEnd_2290285] using wordTrace_append hprefix tailTrace_2290285
  have hstable : (prefixWord ++ tailWord_2290285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290285).length < 2 ^ (prefixWord ++ tailWord_2290285).sum := by decide
  have hdescent : baseEnd_2290285 < baseStart_2290285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290328 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_2290328 : Nat := 118140960795 + 2290328 * 2 ^ 59
def prefixEnd_2290328 : Nat := 4983230072969 + 3 ^ 40 * 2290328 * 2
def baseEnd_2290328 : Nat := 392013040150273438288993

theorem tailTrace_2290328 : CollatzResearch.WordTrace tailWord_2290328 prefixEnd_2290328 392013040150273438288993 := by
  unfold tailWord_2290328
  simp only [CollatzResearch.WordTrace]
  refine ⟨41767562423270143862959819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55690083231026858483946425 41767562423270143862959819)
  ·
    refine ⟨62651343634905215794439729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41767562423270143862959819 62651343634905215794439729)
    ·
      refine ⟨46988507726178911845829797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62651343634905215794439729 46988507726178911845829797)
      ·
        refine ⟨8810345198658545971093087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46988507726178911845829797 8810345198658545971093087)
        ·
          refine ⟨13215517797987818956639631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8810345198658545971093087 13215517797987818956639631)
          ·
            refine ⟨19823276696981728434959447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215517797987818956639631 19823276696981728434959447)
            ·
              refine ⟨29734915045472592652439171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19823276696981728434959447 29734915045472592652439171)
              ·
                refine ⟨44602372568208888978658757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29734915045472592652439171 44602372568208888978658757)
                ·
                  refine ⟨8362944856539166683498517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44602372568208888978658757 8362944856539166683498517)
                  ·
                    refine ⟨392013040150273438288993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8362944856539166683498517 392013040150273438288993)
                    ·
                      rfl

theorem cell23_2290328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_2290328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290328 prefixEnd_2290328 := by exact prefixLift 2290328
  have htrace : WordTrace (prefixWord ++ tailWord_2290328) baseStart_2290328 baseEnd_2290328 := by
    simpa [prefixWord, tailWord_2290328, baseEnd_2290328] using wordTrace_append hprefix tailTrace_2290328
  have hstable : (prefixWord ++ tailWord_2290328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290328).length < 2 ^ (prefixWord ++ tailWord_2290328).sum := by decide
  have hdescent : baseEnd_2290328 < baseStart_2290328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290346 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2290346 : Nat := 118140960795 + 2290346 * 2 ^ 59
def prefixEnd_2290346 : Nat := 4983230072969 + 3 ^ 40 * 2290346 * 2
def baseEnd_2290346 : Nat := 1176048363102601244441897

theorem tailTrace_2290346 : CollatzResearch.WordTrace tailWord_2290346 prefixEnd_2290346 1176048363102601244441897 := by
  unfold tailWord_2290346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20883945340118769200018723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55690520906983384533383261 20883945340118769200018723)
  ·
    refine ⟨31325918010178153800028085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20883945340118769200018723 31325918010178153800028085)
    ·
      refine ⟨2936804813454201918752633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31325918010178153800028085 2936804813454201918752633)
      ·
        refine ⟨2202603610090651439064475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936804813454201918752633 2202603610090651439064475)
        ·
          refine ⟨3303905415135977158596713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202603610090651439064475 3303905415135977158596713)
          ·
            refine ⟨2477929061351982868947535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303905415135977158596713 2477929061351982868947535)
            ·
              refine ⟨3716893592027974303421303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477929061351982868947535 3716893592027974303421303)
              ·
                refine ⟨5575340388041961455131955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716893592027974303421303 5575340388041961455131955)
                ·
                  refine ⟨8363010582062942182697933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575340388041961455131955 8363010582062942182697933)
                  ·
                    refine ⟨3136128968273603318511725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8363010582062942182697933 3136128968273603318511725)
                    ·
                      refine ⟨1176048363102601244441897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136128968273603318511725 1176048363102601244441897)
                      ·
                        rfl

theorem cell23_2290346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2290346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290346 prefixEnd_2290346 := by exact prefixLift 2290346
  have htrace : WordTrace (prefixWord ++ tailWord_2290346) baseStart_2290346 baseEnd_2290346 := by
    simpa [prefixWord, tailWord_2290346, baseEnd_2290346] using wordTrace_append hprefix tailTrace_2290346
  have hstable : (prefixWord ++ tailWord_2290346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290346).length < 2 ^ (prefixWord ++ tailWord_2290346).sum := by decide
  have hdescent : baseEnd_2290346 < baseStart_2290346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290375 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 5]
def baseStart_2290375 : Nat := 118140960795 + 2290375 * 2 ^ 59
def prefixEnd_2290375 : Nat := 4983230072969 + 3 ^ 40 * 2290375 * 2
def baseEnd_2290375 : Nat := 130673694893509070108807

theorem tailTrace_2290375 : CollatzResearch.WordTrace tailWord_2290375 prefixEnd_2290375 130673694893509070108807 := by
  unfold tailWord_2290375
  simp only [CollatzResearch.WordTrace]
  refine ⟨83536839077370014752880579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55691226051580009835253719 83536839077370014752880579)
  ·
    refine ⟨125305258616055022129320869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83536839077370014752880579 125305258616055022129320869)
    ·
      refine ⟨23494735990510316649247663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125305258616055022129320869 23494735990510316649247663)
      ·
        refine ⟨35242103985765474973871495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23494735990510316649247663 35242103985765474973871495)
        ·
          refine ⟨52863155978648212460807243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35242103985765474973871495 52863155978648212460807243)
          ·
            refine ⟨79294733967972318691210865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52863155978648212460807243 79294733967972318691210865)
            ·
              refine ⟨59471050475979239018408149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79294733967972318691210865 59471050475979239018408149)
              ·
                refine ⟨1393852745530763414493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59471050475979239018408149 1393852745530763414493941)
                ·
                  refine ⟨130673694893509070108807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393852745530763414493941 130673694893509070108807)
                  ·
                    rfl

theorem cell23_2290375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 5].length) (baseStart_2290375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290375 prefixEnd_2290375 := by exact prefixLift 2290375
  have htrace : WordTrace (prefixWord ++ tailWord_2290375) baseStart_2290375 baseEnd_2290375 := by
    simpa [prefixWord, tailWord_2290375, baseEnd_2290375] using wordTrace_append hprefix tailTrace_2290375
  have hstable : (prefixWord ++ tailWord_2290375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290375).length < 2 ^ (prefixWord ++ tailWord_2290375).sum := by decide
  have hdescent : baseEnd_2290375 < baseStart_2290375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290403 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2290403 : Nat := 118140960795 + 2290403 * 2 ^ 59
def prefixEnd_2290403 : Nat := 4983230072969 + 3 ^ 40 * 2290403 * 2
def baseEnd_2290403 : Nat := 1176077631499907521429135

theorem tailTrace_2290403 : CollatzResearch.WordTrace tailWord_2290403 prefixEnd_2290403 1176077631499907521429135 := by
  unfold tailWord_2290403
  simp only [CollatzResearch.WordTrace]
  refine ⟨83537860321268575534899863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55691906880845717023266575 83537860321268575534899863)
  ·
    refine ⟨125306790481902863302349795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83537860321268575534899863 125306790481902863302349795)
    ·
      refine ⟨187960185722854294953524693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125306790481902863302349795 187960185722854294953524693)
      ·
        refine ⟨4405316852879397537973235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 187960185722854294953524693 4405316852879397537973235)
        ·
          refine ⟨6607975279319096306959853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405316852879397537973235 6607975279319096306959853)
          ·
            refine ⟨2477990729744661115109945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6607975279319096306959853 2477990729744661115109945)
            ·
              refine ⟨1858493047308495836332459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477990729744661115109945 1858493047308495836332459)
              ·
                refine ⟨2787739570962743754498689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858493047308495836332459 2787739570962743754498689)
                ·
                  refine ⟨2090804678222057815874017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787739570962743754498689 2090804678222057815874017)
                  ·
                    refine ⟨1568103508666543361905513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2090804678222057815874017 1568103508666543361905513)
                    ·
                      refine ⟨1176077631499907521429135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568103508666543361905513 1176077631499907521429135)
                      ·
                        rfl

theorem cell23_2290403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2290403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290403 prefixEnd_2290403 := by exact prefixLift 2290403
  have htrace : WordTrace (prefixWord ++ tailWord_2290403) baseStart_2290403 baseEnd_2290403 := by
    simpa [prefixWord, tailWord_2290403, baseEnd_2290403] using wordTrace_append hprefix tailTrace_2290403
  have hstable : (prefixWord ++ tailWord_2290403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290403).length < 2 ^ (prefixWord ++ tailWord_2290403).sum := by decide
  have hdescent : baseEnd_2290403 < baseStart_2290403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290422 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2290422 : Nat := 118140960795 + 2290422 * 2 ^ 59
def prefixEnd_2290422 : Nat := 4983230072969 + 3 ^ 40 * 2290422 * 2
def baseEnd_2290422 : Nat := 392029129210780982363849

theorem tailTrace_2290422 : CollatzResearch.WordTrace tailWord_2290422 prefixEnd_2290422 392029129210780982363849 := by
  unfold tailWord_2290422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221159581762483861240095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55692368872133161186561013 5221159581762483861240095)
  ·
    refine ⟨7831739372643725791860143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221159581762483861240095 7831739372643725791860143)
    ·
      refine ⟨11747609058965588687790215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831739372643725791860143 11747609058965588687790215)
      ·
        refine ⟨17621413588448383031685323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11747609058965588687790215 17621413588448383031685323)
        ·
          refine ⟨26432120382672574547527985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621413588448383031685323 26432120382672574547527985)
          ·
            refine ⟨19824090287004430910645989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26432120382672574547527985 19824090287004430910645989)
            ·
              refine ⟨3717016928813330795746123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19824090287004430910645989 3717016928813330795746123)
              ·
                refine ⟨5575525393219996193619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717016928813330795746123 5575525393219996193619185)
                ·
                  refine ⟨4181644044914997145214389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575525393219996193619185 4181644044914997145214389)
                  ·
                    refine ⟨392029129210780982363849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4181644044914997145214389 392029129210780982363849)
                    ·
                      rfl

theorem cell23_2290422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2290422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290422 prefixEnd_2290422 := by exact prefixLift 2290422
  have htrace : WordTrace (prefixWord ++ tailWord_2290422) baseStart_2290422 baseEnd_2290422 := by
    simpa [prefixWord, tailWord_2290422, baseEnd_2290422] using wordTrace_append hprefix tailTrace_2290422
  have hstable : (prefixWord ++ tailWord_2290422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290422).length < 2 ^ (prefixWord ++ tailWord_2290422).sum := by decide
  have hdescent : baseEnd_2290422 < baseStart_2290422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290442 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2290442 : Nat := 118140960795 + 2290442 * 2 ^ 59
def prefixEnd_2290442 : Nat := 4983230072969 + 3 ^ 40 * 2290442 * 2
def baseEnd_2290442 : Nat := 1176097657245432868841455

theorem tailTrace_2290442 : CollatzResearch.WordTrace tailWord_2290442 prefixEnd_2290442 1176097657245432868841455 := by
  unfold tailWord_2290442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20884820692031821298892395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55692855178751523463713053 20884820692031821298892395)
  ·
    refine ⟨31327231038047731948338593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20884820692031821298892395 31327231038047731948338593)
    ·
      refine ⟨23495423278535798961253945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31327231038047731948338593 23495423278535798961253945)
      ·
        refine ⟨17621567458901849220940459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23495423278535798961253945 17621567458901849220940459)
        ·
          refine ⟨26432351188352773831410689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621567458901849220940459 26432351188352773831410689)
          ·
            refine ⟨19824263391264580373558017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26432351188352773831410689 19824263391264580373558017)
            ·
              refine ⟨14868197543448435280168513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19824263391264580373558017 14868197543448435280168513)
              ·
                refine ⟨11151148157586326460126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14868197543448435280168513 11151148157586326460126385)
                ·
                  refine ⟨8363361118189744845094789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11151148157586326460126385 8363361118189744845094789)
                  ·
                    refine ⟨1568130209660577158455273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8363361118189744845094789 1568130209660577158455273)
                    ·
                      refine ⟨1176097657245432868841455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568130209660577158455273 1176097657245432868841455)
                      ·
                        rfl

theorem cell23_2290442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2290442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290442 prefixEnd_2290442 := by exact prefixLift 2290442
  have htrace : WordTrace (prefixWord ++ tailWord_2290442) baseStart_2290442 baseEnd_2290442 := by
    simpa [prefixWord, tailWord_2290442, baseEnd_2290442] using wordTrace_append hprefix tailTrace_2290442
  have hstable : (prefixWord ++ tailWord_2290442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290442).length < 2 ^ (prefixWord ++ tailWord_2290442).sum := by decide
  have hdescent : baseEnd_2290442 < baseStart_2290442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290465 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 6]
def baseStart_2290465 : Nat := 118140960795 + 2290465 * 2 ^ 59
def prefixEnd_2290465 : Nat := 4983230072969 + 3 ^ 40 * 2290465 * 2
def baseEnd_2290465 : Nat := 130678829700054030983761

theorem tailTrace_2290465 : CollatzResearch.WordTrace tailWord_2290465 prefixEnd_2290465 130678829700054030983761 := by
  unfold tailWord_2290465
  simp only [CollatzResearch.WordTrace]
  refine ⟨83540121647043960123656849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55693414431362640082437899 83540121647043960123656849)
  ·
    refine ⟨62655091235282970092742637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83540121647043960123656849 62655091235282970092742637)
    ·
      refine ⟨23495659213231113784778489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62655091235282970092742637 23495659213231113784778489)
      ·
        refine ⟨17621744409923335338583867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23495659213231113784778489 17621744409923335338583867)
        ·
          refine ⟨26432616614885003007875801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621744409923335338583867 26432616614885003007875801)
          ·
            refine ⟨19824462461163752255906851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26432616614885003007875801 19824462461163752255906851)
            ·
              refine ⟨29736693691745628383860277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19824462461163752255906851 29736693691745628383860277)
              ·
                refine ⟨2787815033601152660986901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29736693691745628383860277 2787815033601152660986901)
                ·
                  refine ⟨130678829700054030983761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2787815033601152660986901 130678829700054030983761)
                  ·
                    rfl

theorem cell23_2290465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_2290465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290465 prefixEnd_2290465 := by exact prefixLift 2290465
  have htrace : WordTrace (prefixWord ++ tailWord_2290465) baseStart_2290465 baseEnd_2290465 := by
    simpa [prefixWord, tailWord_2290465, baseEnd_2290465] using wordTrace_append hprefix tailTrace_2290465
  have hstable : (prefixWord ++ tailWord_2290465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290465).length < 2 ^ (prefixWord ++ tailWord_2290465).sum := by decide
  have hdescent : baseEnd_2290465 < baseStart_2290465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290492 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_2290492 : Nat := 118140960795 + 2290492 * 2 ^ 59
def prefixEnd_2290492 : Nat := 4983230072969 + 3 ^ 40 * 2290492 * 2
def baseEnd_2290492 : Nat := 1176123331278157673216225

theorem tailTrace_2290492 : CollatzResearch.WordTrace tailWord_2290492 prefixEnd_2290492 1176123331278157673216225 := by
  unfold tailWord_2290492
  simp only [CollatzResearch.WordTrace]
  refine ⟨41770553208973071867444865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55694070945297429156593153 41770553208973071867444865)
  ·
    refine ⟨31327914906729803900583649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41770553208973071867444865 31327914906729803900583649)
    ·
      refine ⟨23495936180047352925437737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31327914906729803900583649 23495936180047352925437737)
      ·
        refine ⟨17621952135035514694078303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23495936180047352925437737 17621952135035514694078303)
        ·
          refine ⟨26432928202553272041117455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621952135035514694078303 26432928202553272041117455)
          ·
            refine ⟨39649392303829908061676183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26432928202553272041117455 39649392303829908061676183)
            ·
              refine ⟨59474088455744862092514275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39649392303829908061676183 59474088455744862092514275)
              ·
                refine ⟨89211132683617293138771413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59474088455744862092514275 89211132683617293138771413)
                ·
                  refine ⟨2090885922272280307939955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89211132683617293138771413 2090885922272280307939955)
                  ·
                    refine ⟨3136328883408420461909933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090885922272280307939955 3136328883408420461909933)
                    ·
                      refine ⟨1176123331278157673216225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136328883408420461909933 1176123331278157673216225)
                      ·
                        rfl

theorem cell23_2290492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_2290492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290492 prefixEnd_2290492 := by exact prefixLift 2290492
  have htrace : WordTrace (prefixWord ++ tailWord_2290492) baseStart_2290492 baseEnd_2290492 := by
    simpa [prefixWord, tailWord_2290492, baseEnd_2290492] using wordTrace_append hprefix tailTrace_2290492
  have hstable : (prefixWord ++ tailWord_2290492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290492).length < 2 ^ (prefixWord ++ tailWord_2290492).sum := by decide
  have hdescent : baseEnd_2290492 < baseStart_2290492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290515 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4]
def baseStart_2290515 : Nat := 118140960795 + 2290515 * 2 ^ 59
def prefixEnd_2290515 : Nat := 4983230072969 + 3 ^ 40 * 2290515 * 2
def baseEnd_2290515 : Nat := 1176135141333211083228619

theorem tailTrace_2290515 : CollatzResearch.WordTrace tailWord_2290515 prefixEnd_2290515 1176135141333211083228619 := by
  unfold tailWord_2290515
  simp only [CollatzResearch.WordTrace]
  refine ⟨83541945296862818662976999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55694630197908545775317999 83541945296862818662976999)
  ·
    refine ⟨125312917945294227994465499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83541945296862818662976999 125312917945294227994465499)
    ·
      refine ⟨187969376917941341991698249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125312917945294227994465499 187969376917941341991698249)
      ·
        refine ⟨140977032688456006493773687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187969376917941341991698249 140977032688456006493773687)
        ·
          refine ⟨211465549032684009740660531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140977032688456006493773687 211465549032684009740660531)
          ·
            refine ⟨317198323549026014610990797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211465549032684009740660531 317198323549026014610990797)
            ·
              refine ⟨118949371330884755479121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317198323549026014610990797 118949371330884755479121549)
              ·
                refine ⟨44606014249081783304670581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118949371330884755479121549 44606014249081783304670581)
                ·
                  refine ⟨4181813835851417184812867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44606014249081783304670581 4181813835851417184812867)
                  ·
                    refine ⟨6272720753777125777219301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181813835851417184812867 6272720753777125777219301)
                    ·
                      refine ⟨1176135141333211083228619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6272720753777125777219301 1176135141333211083228619)
                      ·
                        rfl

theorem cell23_2290515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_2290515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290515 prefixEnd_2290515 := by exact prefixLift 2290515
  have htrace : WordTrace (prefixWord ++ tailWord_2290515) baseStart_2290515 baseEnd_2290515 := by
    simpa [prefixWord, tailWord_2290515, baseEnd_2290515] using wordTrace_append hprefix tailTrace_2290515
  have hstable : (prefixWord ++ tailWord_2290515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290515).length < 2 ^ (prefixWord ++ tailWord_2290515).sum := by decide
  have hdescent : baseEnd_2290515 < baseStart_2290515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290549 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2290549 : Nat := 118140960795 + 2290549 * 2 ^ 59
def prefixEnd_2290549 : Nat := 4983230072969 + 3 ^ 40 * 2290549 * 2
def baseEnd_2290549 : Nat := 1176152599675463950203463

theorem tailTrace_2290549 : CollatzResearch.WordTrace tailWord_2290549 prefixEnd_2290549 1176152599675463950203463 := by
  unfold tailWord_2290549
  simp only [CollatzResearch.WordTrace]
  refine ⟨83543185378739642469714701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55695456919159761646476467 83543185378739642469714701)
  ·
    refine ⟨31328694517027365926143013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83543185378739642469714701 31328694517027365926143013)
    ·
      refine ⟨5874130221942631111151815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31328694517027365926143013 5874130221942631111151815)
      ·
        refine ⟨8811195332913946666727723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5874130221942631111151815 8811195332913946666727723)
        ·
          refine ⟨13216792999370920000091585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811195332913946666727723 13216792999370920000091585)
          ·
            refine ⟨9912594749528190000068689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13216792999370920000091585 9912594749528190000068689)
            ·
              refine ⟨7434446062146142500051517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9912594749528190000068689 7434446062146142500051517)
              ·
                refine ⟨2787917273304803437519319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7434446062146142500051517 2787917273304803437519319)
                ·
                  refine ⟨4181875909957205156278979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787917273304803437519319 4181875909957205156278979)
                  ·
                    refine ⟨6272813864935807734418469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181875909957205156278979 6272813864935807734418469)
                    ·
                      refine ⟨1176152599675463950203463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6272813864935807734418469 1176152599675463950203463)
                      ·
                        rfl

theorem cell23_2290549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2290549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290549 prefixEnd_2290549 := by exact prefixLift 2290549
  have htrace : WordTrace (prefixWord ++ tailWord_2290549) baseStart_2290549 baseEnd_2290549 := by
    simpa [prefixWord, tailWord_2290549, baseEnd_2290549] using wordTrace_append hprefix tailTrace_2290549
  have hstable : (prefixWord ++ tailWord_2290549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290549).length < 2 ^ (prefixWord ++ tailWord_2290549).sum := by decide
  have hdescent : baseEnd_2290549 < baseStart_2290549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290595 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2290595 : Nat := 118140960795 + 2290595 * 2 ^ 59
def prefixEnd_2290595 : Nat := 4983230072969 + 3 ^ 40 * 2290595 * 2
def baseEnd_2290595 : Nat := 1176176219785570770228251

theorem tailTrace_2290595 : CollatzResearch.WordTrace tailWord_2290595 prefixEnd_2290595 1176176219785570770228251 := by
  unfold tailWord_2290595
  simp only [CollatzResearch.WordTrace]
  refine ⟨83544863136572992325889239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55696575424381994883926159 83544863136572992325889239)
  ·
    refine ⟨125317294704859488488833859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83544863136572992325889239 125317294704859488488833859)
    ·
      refine ⟨187975942057289232733250789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125317294704859488488833859 187975942057289232733250789)
      ·
        refine ⟨35245489135741731137484523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187975942057289232733250789 35245489135741731137484523)
        ·
          refine ⟨52868233703612596706226785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35245489135741731137484523 52868233703612596706226785)
          ·
            refine ⟨39651175277709447529670089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52868233703612596706226785 39651175277709447529670089)
            ·
              refine ⟨29738381458282085647252567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39651175277709447529670089 29738381458282085647252567)
              ·
                refine ⟨44607572187423128470878851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29738381458282085647252567 44607572187423128470878851)
                ·
                  refine ⟨66911358281134692706318277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44607572187423128470878851 66911358281134692706318277)
                  ·
                    refine ⟨12545879677712754882434677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66911358281134692706318277 12545879677712754882434677)
                    ·
                      refine ⟨1176176219785570770228251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12545879677712754882434677 1176176219785570770228251)
                      ·
                        rfl

theorem cell23_2290595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2290595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290595 prefixEnd_2290595 := by exact prefixLift 2290595
  have htrace : WordTrace (prefixWord ++ tailWord_2290595) baseStart_2290595 baseEnd_2290595 := by
    simpa [prefixWord, tailWord_2290595, baseEnd_2290595] using wordTrace_append hprefix tailTrace_2290595
  have hstable : (prefixWord ++ tailWord_2290595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290595).length < 2 ^ (prefixWord ++ tailWord_2290595).sum := by decide
  have hdescent : baseEnd_2290595 < baseStart_2290595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290616 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2290616 : Nat := 118140960795 + 2290616 * 2 ^ 59
def prefixEnd_2290616 : Nat := 4983230072969 + 3 ^ 40 * 2290616 * 2
def baseEnd_2290616 : Nat := 1176187002879315188065655

theorem tailTrace_2290616 : CollatzResearch.WordTrace tailWord_2290616 prefixEnd_2290616 1176187002879315188065655 := by
  unfold tailWord_2290616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41772814534748456456201851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55697086046331275274935801 41772814534748456456201851)
  ·
    refine ⟨62659221802122684684302777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41772814534748456456201851 62659221802122684684302777)
    ·
      refine ⟨46994416351592013513227083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62659221802122684684302777 46994416351592013513227083)
      ·
        refine ⟨70491624527388020269840625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46994416351592013513227083 70491624527388020269840625)
        ·
          refine ⟨52868718395541015202380469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70491624527388020269840625 52868718395541015202380469)
          ·
            refine ⟨4956442349581970175223169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52868718395541015202380469 4956442349581970175223169)
            ·
              refine ⟨3717331762186477631417377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4956442349581970175223169 3717331762186477631417377)
              ·
                refine ⟨2787998821639858223563033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3717331762186477631417377 2787998821639858223563033)
                ·
                  refine ⟨2090999116229893667672275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787998821639858223563033 2090999116229893667672275)
                  ·
                    refine ⟨3136498674344840501508413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090999116229893667672275 3136498674344840501508413)
                    ·
                      refine ⟨1176187002879315188065655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136498674344840501508413 1176187002879315188065655)
                      ·
                        rfl

theorem cell23_2290616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2290616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290616 prefixEnd_2290616 := by exact prefixLift 2290616
  have htrace : WordTrace (prefixWord ++ tailWord_2290616) baseStart_2290616 baseEnd_2290616 := by
    simpa [prefixWord, tailWord_2290616, baseEnd_2290616] using wordTrace_append hprefix tailTrace_2290616
  have hstable : (prefixWord ++ tailWord_2290616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290616).length < 2 ^ (prefixWord ++ tailWord_2290616).sum := by decide
  have hdescent : baseEnd_2290616 < baseStart_2290616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290622 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2290622 : Nat := 118140960795 + 2290622 * 2 ^ 59
def prefixEnd_2290622 : Nat := 4983230072969 + 3 ^ 40 * 2290622 * 2
def baseEnd_2290622 : Nat := 1176190083763242164590627

theorem tailTrace_2290622 : CollatzResearch.WordTrace tailWord_2290622 prefixEnd_2290622 1176190083763242164590627 := by
  unfold tailWord_2290622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443230988434396992140265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55697231938316783958081413 10443230988434396992140265)
  ·
    refine ⟨7832423241325797744105199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10443230988434396992140265 7832423241325797744105199)
    ·
      refine ⟨11748634861988696616157799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7832423241325797744105199 11748634861988696616157799)
      ·
        refine ⟨17622952292983044924236699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748634861988696616157799 17622952292983044924236699)
        ·
          refine ⟨26434428439474567386355049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17622952292983044924236699 26434428439474567386355049)
          ·
            refine ⟨19825821329605925539766287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26434428439474567386355049 19825821329605925539766287)
            ·
              refine ⟨29738731994408888309649431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19825821329605925539766287 29738731994408888309649431)
              ·
                refine ⟨44608097991613332464474147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29738731994408888309649431 44608097991613332464474147)
                ·
                  refine ⟨66912146987419998696711221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44608097991613332464474147 66912146987419998696711221)
                  ·
                    refine ⟨6273013780070624877816677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66912146987419998696711221 6273013780070624877816677)
                    ·
                      refine ⟨1176190083763242164590627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6273013780070624877816677 1176190083763242164590627)
                      ·
                        rfl

theorem cell23_2290622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2290622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290622 prefixEnd_2290622 := by exact prefixLift 2290622
  have htrace : WordTrace (prefixWord ++ tailWord_2290622) baseStart_2290622 baseEnd_2290622 := by
    simpa [prefixWord, tailWord_2290622, baseEnd_2290622] using wordTrace_append hprefix tailTrace_2290622
  have hstable : (prefixWord ++ tailWord_2290622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290622).length < 2 ^ (prefixWord ++ tailWord_2290622).sum := by decide
  have hdescent : baseEnd_2290622 < baseStart_2290622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290639 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 4, 2]
def baseStart_2290639 : Nat := 118140960795 + 2290639 * 2 ^ 59
def prefixEnd_2290639 : Nat := 4983230072969 + 3 ^ 40 * 2290639 * 2
def baseEnd_2290639 : Nat := 1176198812934368598078049

theorem tailTrace_2290639 : CollatzResearch.WordTrace tailWord_2290639 prefixEnd_2290639 1176198812934368598078049 := by
  unfold tailWord_2290639
  simp only [CollatzResearch.WordTrace]
  refine ⟨83546467948413587840490971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55697645298942391893660647 83546467948413587840490971)
  ·
    refine ⟨125319701922620381760736457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83546467948413587840490971 125319701922620381760736457)
    ·
      refine ⟨93989776441965286320552343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125319701922620381760736457 93989776441965286320552343)
      ·
        refine ⟨140984664662947929480828515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93989776441965286320552343 140984664662947929480828515)
        ·
          refine ⟨211476996994421894221242773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140984664662947929480828515 211476996994421894221242773)
          ·
            refine ⟨9912984234113526291620755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211476996994421894221242773 9912984234113526291620755)
            ·
              refine ⟨14869476351170289437431133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9912984234113526291620755 14869476351170289437431133)
              ·
                refine ⟨5576053631688858539036675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14869476351170289437431133 5576053631688858539036675)
                ·
                  refine ⟨8364080447533287808555013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576053631688858539036675 8364080447533287808555013)
                  ·
                    refine ⟨1568265083912491464104065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8364080447533287808555013 1568265083912491464104065)
                    ·
                      refine ⟨1176198812934368598078049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568265083912491464104065 1176198812934368598078049)
                      ·
                        rfl

theorem cell23_2290639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4, 2].length) (baseStart_2290639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290639 prefixEnd_2290639 := by exact prefixLift 2290639
  have htrace : WordTrace (prefixWord ++ tailWord_2290639) baseStart_2290639 baseEnd_2290639 := by
    simpa [prefixWord, tailWord_2290639, baseEnd_2290639] using wordTrace_append hprefix tailTrace_2290639
  have hstable : (prefixWord ++ tailWord_2290639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290639).length < 2 ^ (prefixWord ++ tailWord_2290639).sum := by decide
  have hdescent : baseEnd_2290639 < baseStart_2290639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290673 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_2290673 : Nat := 118140960795 + 2290673 * 2 ^ 59
def prefixEnd_2290673 : Nat := 4983230072969 + 3 ^ 40 * 2290673 * 2
def baseEnd_2290673 : Nat := 1176216271276621465052893

theorem tailTrace_2290673 : CollatzResearch.WordTrace tailWord_2290673 prefixEnd_2290673 1176216271276621465052893 := by
  unfold tailWord_2290673
  simp only [CollatzResearch.WordTrace]
  refine ⟨83547708030290411647228673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55698472020193607764819115 83547708030290411647228673)
  ·
    refine ⟨62660781022717808735421505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83547708030290411647228673 62660781022717808735421505)
    ·
      refine ⟨46995585767038356551566129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62660781022717808735421505 46995585767038356551566129)
      ·
        refine ⟨35246689325278767413674597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46995585767038356551566129 35246689325278767413674597)
        ·
          refine ⟨6608754248489768890063987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35246689325278767413674597 6608754248489768890063987)
          ·
            refine ⟨9913131372734653335095981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6608754248489768890063987 9913131372734653335095981)
            ·
              refine ⟨3717424264775495000660993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9913131372734653335095981 3717424264775495000660993)
              ·
                refine ⟨2788068198581621250495745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3717424264775495000660993 2788068198581621250495745)
                ·
                  refine ⟨2091051148936215937871809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2788068198581621250495745 2091051148936215937871809)
                  ·
                    refine ⟨1568288361702161953403857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091051148936215937871809 1568288361702161953403857)
                    ·
                      refine ⟨1176216271276621465052893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568288361702161953403857 1176216271276621465052893)
                      ·
                        rfl

theorem cell23_2290673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_2290673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290673 prefixEnd_2290673 := by exact prefixLift 2290673
  have htrace : WordTrace (prefixWord ++ tailWord_2290673) baseStart_2290673 baseEnd_2290673 := by
    simpa [prefixWord, tailWord_2290673, baseEnd_2290673] using wordTrace_append hprefix tailTrace_2290673
  have hstable : (prefixWord ++ tailWord_2290673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290673).length < 2 ^ (prefixWord ++ tailWord_2290673).sum := by decide
  have hdescent : baseEnd_2290673 < baseStart_2290673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290689 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2290689 : Nat := 118140960795 + 2290689 * 2 ^ 59
def prefixEnd_2290689 : Nat := 4983230072969 + 3 ^ 40 * 2290689 * 2
def baseEnd_2290689 : Nat := 1176224486967093402452819

theorem tailTrace_2290689 : CollatzResearch.WordTrace tailWord_2290689 prefixEnd_2290689 1176224486967093402452819 := by
  unfold tailWord_2290689
  simp only [CollatzResearch.WordTrace]
  refine ⟨83548291598232446379811121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55698861065488297586540747 83548291598232446379811121)
  ·
    refine ⟨62661218698674334784858341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83548291598232446379811121 62661218698674334784858341)
    ·
      refine ⟨11748978506001437772160939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62661218698674334784858341 11748978506001437772160939)
      ·
        refine ⟨17623467759002156658241409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748978506001437772160939 17623467759002156658241409)
        ·
          refine ⟨13217600819251617493681057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17623467759002156658241409 13217600819251617493681057)
          ·
            refine ⟨9913200614438713120260793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13217600819251617493681057 9913200614438713120260793)
            ·
              refine ⟨7434900460829034840195595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9913200614438713120260793 7434900460829034840195595)
              ·
                refine ⟨11152350691243552260293393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434900460829034840195595 11152350691243552260293393)
                ·
                  refine ⟨8364263018432664195220045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11152350691243552260293393 8364263018432664195220045)
                  ·
                    refine ⟨3136598631912249073207517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8364263018432664195220045 3136598631912249073207517)
                    ·
                      refine ⟨1176224486967093402452819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136598631912249073207517 1176224486967093402452819)
                      ·
                        rfl

theorem cell23_2290689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2290689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290689 prefixEnd_2290689 := by exact prefixLift 2290689
  have htrace : WordTrace (prefixWord ++ tailWord_2290689) baseStart_2290689 baseEnd_2290689 := by
    simpa [prefixWord, tailWord_2290689, baseEnd_2290689] using wordTrace_append hprefix tailTrace_2290689
  have hstable : (prefixWord ++ tailWord_2290689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290689).length < 2 ^ (prefixWord ++ tailWord_2290689).sum := by decide
  have hdescent : baseEnd_2290689 < baseStart_2290689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290766 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_2290766 : Nat := 118140960795 + 2290766 * 2 ^ 59
def prefixEnd_2290766 : Nat := 4983230072969 + 3 ^ 40 * 2290766 * 2
def baseEnd_2290766 : Nat := 1176264024977489601189965

theorem tailTrace_2290766 : CollatzResearch.WordTrace tailWord_2290766 prefixEnd_2290766 1176264024977489601189965 := by
  unfold tailWord_2290766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443887502369186066295519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55700733345968992353576101 10443887502369186066295519)
  ·
    refine ⟨15665831253553779099443279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443887502369186066295519 15665831253553779099443279)
    ·
      refine ⟨23498746880330668649164919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665831253553779099443279 23498746880330668649164919)
      ·
        refine ⟨35248120320496002973747379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23498746880330668649164919 35248120320496002973747379)
        ·
          refine ⟨52872180480744004460621069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35248120320496002973747379 52872180480744004460621069)
          ·
            refine ⟨19827067680279001672732901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52872180480744004460621069 19827067680279001672732901)
            ·
              refine ⟨3717575190052312813637419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19827067680279001672732901 3717575190052312813637419)
              ·
                refine ⟨5576362785078469220456129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717575190052312813637419 5576362785078469220456129)
                ·
                  refine ⟨4182272088808851915342097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576362785078469220456129 4182272088808851915342097)
                  ·
                    refine ⟨3136704066606638936506573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182272088808851915342097 3136704066606638936506573)
                    ·
                      refine ⟨1176264024977489601189965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136704066606638936506573 1176264024977489601189965)
                      ·
                        rfl

theorem cell23_2290766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_2290766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290766 prefixEnd_2290766 := by exact prefixLift 2290766
  have htrace : WordTrace (prefixWord ++ tailWord_2290766) baseStart_2290766 baseEnd_2290766 := by
    simpa [prefixWord, tailWord_2290766, baseEnd_2290766] using wordTrace_append hprefix tailTrace_2290766
  have hstable : (prefixWord ++ tailWord_2290766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290766).length < 2 ^ (prefixWord ++ tailWord_2290766).sum := by decide
  have hdescent : baseEnd_2290766 < baseStart_2290766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290786 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2290786 : Nat := 118140960795 + 2290786 * 2 ^ 59
def prefixEnd_2290786 : Nat := 4983230072969 + 3 ^ 40 * 2290786 * 2
def baseEnd_2290786 : Nat := 130697143843397724771097

theorem tailTrace_2290786 : CollatzResearch.WordTrace tailWord_2290786 prefixEnd_2290786 130697143843397724771097 := by
  unfold tailWord_2290786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20887957369720257986523053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55701219652587354630728141 20887957369720257986523053)
  ·
    refine ⟨7832984013645096744946145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20887957369720257986523053 7832984013645096744946145)
    ·
      refine ⟨5874738010233822558709609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7832984013645096744946145 5874738010233822558709609)
      ·
        refine ⟨4406053507675366919032207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5874738010233822558709609 4406053507675366919032207)
        ·
          refine ⟨6609080261513050378548311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406053507675366919032207 6609080261513050378548311)
          ·
            refine ⟨9913620392269575567822467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609080261513050378548311 9913620392269575567822467)
            ·
              refine ⟨14870430588404363351733701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913620392269575567822467 14870430588404363351733701)
              ·
                refine ⟨2788205735325818128450069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14870430588404363351733701 2788205735325818128450069)
                ·
                  refine ⟨130697143843397724771097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2788205735325818128450069 130697143843397724771097)
                  ·
                    rfl

theorem cell23_2290786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2290786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290786 prefixEnd_2290786 := by exact prefixLift 2290786
  have htrace : WordTrace (prefixWord ++ tailWord_2290786) baseStart_2290786 baseEnd_2290786 := by
    simpa [prefixWord, tailWord_2290786, baseEnd_2290786] using wordTrace_append hprefix tailTrace_2290786
  have hstable : (prefixWord ++ tailWord_2290786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290786).length < 2 ^ (prefixWord ++ tailWord_2290786).sum := by decide
  have hdescent : baseEnd_2290786 < baseStart_2290786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290796 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_2290796 : Nat := 118140960795 + 2290796 * 2 ^ 59
def prefixEnd_2290796 : Nat := 4983230072969 + 3 ^ 40 * 2290796 * 2
def baseEnd_2290796 : Nat := 1176279429397124483814827

theorem tailTrace_2290796 : CollatzResearch.WordTrace tailWord_2290796 prefixEnd_2290796 1176279429397124483814827 := by
  unfold tailWord_2290796
  simp only [CollatzResearch.WordTrace]
  refine ⟨41776097104422401826978121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55701462805896535769304161 41776097104422401826978121)
  ·
    refine ⟨31332072828316801370233591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41776097104422401826978121 31332072828316801370233591)
    ·
      refine ⟨46998109242475202055350387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31332072828316801370233591 46998109242475202055350387)
      ·
        refine ⟨70497163863712803083025581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46998109242475202055350387 70497163863712803083025581)
        ·
          refine ⟨26436436448892301156134593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70497163863712803083025581 26436436448892301156134593)
          ·
            refine ⟨19827327336669225867100945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26436436448892301156134593 19827327336669225867100945)
            ·
              refine ⟨14870495502501919400325709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19827327336669225867100945 14870495502501919400325709)
              ·
                refine ⟨5576435813438219775122141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14870495502501919400325709 5576435813438219775122141)
                ·
                  refine ⟨2091163430039332415670803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5576435813438219775122141 2091163430039332415670803)
                  ·
                    refine ⟨3136745145058998623506205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091163430039332415670803 3136745145058998623506205)
                    ·
                      refine ⟨1176279429397124483814827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136745145058998623506205 1176279429397124483814827)
                      ·
                        rfl

theorem cell23_2290796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_2290796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290796 prefixEnd_2290796 := by exact prefixLift 2290796
  have htrace : WordTrace (prefixWord ++ tailWord_2290796) baseStart_2290796 baseEnd_2290796 := by
    simpa [prefixWord, tailWord_2290796, baseEnd_2290796] using wordTrace_append hprefix tailTrace_2290796
  have hstable : (prefixWord ++ tailWord_2290796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290796).length < 2 ^ (prefixWord ++ tailWord_2290796).sum := by decide
  have hdescent : baseEnd_2290796 < baseStart_2290796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290814 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2290814 : Nat := 118140960795 + 2290814 * 2 ^ 59
def prefixEnd_2290814 : Nat := 4983230072969 + 3 ^ 40 * 2290814 * 2
def baseEnd_2290814 : Nat := 1176288672048905413389745

theorem tailTrace_2290814 : CollatzResearch.WordTrace tailWord_2290814 prefixEnd_2290814 1176288672048905413389745 := by
  unfold tailWord_2290814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444106340347449091013937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55701900481853061818740997 10444106340347449091013937)
  ·
    refine ⟨7833079755260586818260453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10444106340347449091013937 7833079755260586818260453)
    ·
      refine ⟨1468702454111360028423835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7833079755260586818260453 1468702454111360028423835)
      ·
        refine ⟨2203053681167040042635753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468702454111360028423835 2203053681167040042635753)
        ·
          refine ⟨1652290260875280031976815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203053681167040042635753 1652290260875280031976815)
          ·
            refine ⟨2478435391312920047965223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652290260875280031976815 2478435391312920047965223)
            ·
              refine ⟨3717653086969380071947835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478435391312920047965223 3717653086969380071947835)
              ·
                refine ⟨5576479630454070107921753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717653086969380071947835 5576479630454070107921753)
                ·
                  refine ⟨4182359722840552580941315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576479630454070107921753 4182359722840552580941315)
                  ·
                    refine ⟨6273539584260828871411973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182359722840552580941315 6273539584260828871411973)
                    ·
                      refine ⟨1176288672048905413389745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6273539584260828871411973 1176288672048905413389745)
                      ·
                        rfl

theorem cell23_2290814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2290814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290814 prefixEnd_2290814 := by exact prefixLift 2290814
  have htrace : WordTrace (prefixWord ++ tailWord_2290814) baseStart_2290814 baseEnd_2290814 := by
    simpa [prefixWord, tailWord_2290814, baseEnd_2290814] using wordTrace_append hprefix tailTrace_2290814
  have hstable : (prefixWord ++ tailWord_2290814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290814).length < 2 ^ (prefixWord ++ tailWord_2290814).sum := by decide
  have hdescent : baseEnd_2290814 < baseStart_2290814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290819 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4]
def baseStart_2290819 : Nat := 118140960795 + 2290819 * 2 ^ 59
def prefixEnd_2290819 : Nat := 4983230072969 + 3 ^ 40 * 2290819 * 2
def baseEnd_2290819 : Nat := 1176291239452177893827221

theorem tailTrace_2290819 : CollatzResearch.WordTrace tailWord_2290819 prefixEnd_2290819 1176291239452177893827221 := by
  unfold tailWord_2290819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83553033087761478582043511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55702022058507652388029007 83553033087761478582043511)
  ·
    refine ⟨125329549631642217873065267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83553033087761478582043511 125329549631642217873065267)
    ·
      refine ⟨187994324447463326809597901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125329549631642217873065267 187994324447463326809597901)
      ·
        refine ⟨70497871667798747553599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187994324447463326809597901 70497871667798747553599213)
        ·
          refine ⟨26436701875424530332599705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70497871667798747553599213 26436701875424530332599705)
          ·
            refine ⟨19827526406568397749449779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26436701875424530332599705 19827526406568397749449779)
            ·
              refine ⟨29741289609852596624174669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19827526406568397749449779 29741289609852596624174669)
              ·
                refine ⟨11152983603694723734065501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29741289609852596624174669 11152983603694723734065501)
                ·
                  refine ⟨4182368851385521400274563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11152983603694723734065501 4182368851385521400274563)
                  ·
                    refine ⟨6273553277078282100411845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182368851385521400274563 6273553277078282100411845)
                    ·
                      refine ⟨1176291239452177893827221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6273553277078282100411845 1176291239452177893827221)
                      ·
                        rfl

theorem cell23_2290819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_2290819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290819 prefixEnd_2290819 := by exact prefixLift 2290819
  have htrace : WordTrace (prefixWord ++ tailWord_2290819) baseStart_2290819 baseEnd_2290819 := by
    simpa [prefixWord, tailWord_2290819, baseEnd_2290819] using wordTrace_append hprefix tailTrace_2290819
  have hstable : (prefixWord ++ tailWord_2290819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290819).length < 2 ^ (prefixWord ++ tailWord_2290819).sum := by decide
  have hdescent : baseEnd_2290819 < baseStart_2290819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290830 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2290830 : Nat := 118140960795 + 2290830 * 2 ^ 59
def prefixEnd_2290830 : Nat := 4983230072969 + 3 ^ 40 * 2290830 * 2
def baseEnd_2290830 : Nat := 1176296887739377350789671

theorem tailTrace_2290830 : CollatzResearch.WordTrace tailWord_2290830 prefixEnd_2290830 1176296887739377350789671 := by
  unfold tailWord_2290830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444179286340203432586743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55702289527147751640462629 10444179286340203432586743)
  ·
    refine ⟨15666268929510305148880115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10444179286340203432586743 15666268929510305148880115)
    ·
      refine ⟨23499403394265457723320173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666268929510305148880115 23499403394265457723320173)
      ·
        refine ⟨8812276272849546646245065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23499403394265457723320173 8812276272849546646245065)
        ·
          refine ⟨6609207204637159984683799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8812276272849546646245065 6609207204637159984683799)
          ·
            refine ⟨9913810806955739977025699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609207204637159984683799 9913810806955739977025699)
            ·
              refine ⟨14870716210433609965538549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913810806955739977025699 14870716210433609965538549)
              ·
                refine ⟨1394129644728150934269239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14870716210433609965538549 1394129644728150934269239)
                ·
                  refine ⟨2091194467092226401403859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394129644728150934269239 2091194467092226401403859)
                  ·
                    refine ⟨3136791700638339602105789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091194467092226401403859 3136791700638339602105789)
                    ·
                      refine ⟨1176296887739377350789671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136791700638339602105789 1176296887739377350789671)
                      ·
                        rfl

theorem cell23_2290830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2290830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290830 prefixEnd_2290830 := by exact prefixLift 2290830
  have htrace : WordTrace (prefixWord ++ tailWord_2290830) baseStart_2290830 baseEnd_2290830 := by
    simpa [prefixWord, tailWord_2290830, baseEnd_2290830] using wordTrace_append hprefix tailTrace_2290830
  have hstable : (prefixWord ++ tailWord_2290830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290830).length < 2 ^ (prefixWord ++ tailWord_2290830).sum := by decide
  have hdescent : baseEnd_2290830 < baseStart_2290830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290849 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2290849 : Nat := 118140960795 + 2290849 * 2 ^ 59
def prefixEnd_2290849 : Nat := 4983230072969 + 3 ^ 40 * 2290849 * 2
def baseEnd_2290849 : Nat := 1176306643871812776452083

theorem tailTrace_2290849 : CollatzResearch.WordTrace tailWord_2290849 prefixEnd_2290849 1176306643871812776452083 := by
  unfold tailWord_2290849
  simp only [CollatzResearch.WordTrace]
  refine ⟨83554127277652793705635601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55702751518435195803757067 83554127277652793705635601)
  ·
    refine ⟨62665595458239595279226701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83554127277652793705635601 62665595458239595279226701)
    ·
      refine ⟨23499598296839848229710013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62665595458239595279226701 23499598296839848229710013)
      ·
        refine ⟨8812349361314943086141255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23499598296839848229710013 8812349361314943086141255)
        ·
          refine ⟨13218524041972414629211883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812349361314943086141255 13218524041972414629211883)
          ·
            refine ⟨19827786062958621943817825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218524041972414629211883 19827786062958621943817825)
            ·
              refine ⟨14870839547218966457863369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19827786062958621943817825 14870839547218966457863369)
              ·
                refine ⟨11153129660414224843397527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14870839547218966457863369 11153129660414224843397527)
                ·
                  refine ⟨16729694490621337265096291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11153129660414224843397527 16729694490621337265096291)
                  ·
                    refine ⟨25094541735932005897644437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16729694490621337265096291 25094541735932005897644437)
                    ·
                      refine ⟨1176306643871812776452083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25094541735932005897644437 1176306643871812776452083)
                      ·
                        rfl

theorem cell23_2290849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2290849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290849 prefixEnd_2290849 := by exact prefixLift 2290849
  have htrace : WordTrace (prefixWord ++ tailWord_2290849) baseStart_2290849 baseEnd_2290849 := by
    simpa [prefixWord, tailWord_2290849, baseEnd_2290849] using wordTrace_append hprefix tailTrace_2290849
  have hstable : (prefixWord ++ tailWord_2290849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290849).length < 2 ^ (prefixWord ++ tailWord_2290849).sum := by decide
  have hdescent : baseEnd_2290849 < baseStart_2290849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290853 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_2290853 : Nat := 118140960795 + 2290853 * 2 ^ 59
def prefixEnd_2290853 : Nat := 4983230072969 + 3 ^ 40 * 2290853 * 2
def baseEnd_2290853 : Nat := 1176308697794430760802065

theorem tailTrace_2290853 : CollatzResearch.WordTrace tailWord_2290853 prefixEnd_2290853 1176308697794430760802065 := by
  unfold tailWord_2290853
  simp only [CollatzResearch.WordTrace]
  refine ⟨83554273169638302388781213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55702848779758868259187475 83554273169638302388781213)
  ·
    refine ⟨31332852438614363395792955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83554273169638302388781213 31332852438614363395792955)
    ·
      refine ⟨46999278657921545093689433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31332852438614363395792955 46999278657921545093689433)
      ·
        refine ⟨35249458993441158820267075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46999278657921545093689433 35249458993441158820267075)
        ·
          refine ⟨52874188490161738230400613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35249458993441158820267075 52874188490161738230400613)
          ·
            refine ⟨9913910341905325918200115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52874188490161738230400613 9913910341905325918200115)
            ·
              refine ⟨14870865512857988877300173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913910341905325918200115 14870865512857988877300173)
              ·
                refine ⟨5576574567321745828987565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14870865512857988877300173 5576574567321745828987565)
                ·
                  refine ⟨2091215462745654685870337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5576574567321745828987565 2091215462745654685870337)
                  ·
                    refine ⟨1568411597059241014402753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091215462745654685870337 1568411597059241014402753)
                    ·
                      refine ⟨1176308697794430760802065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568411597059241014402753 1176308697794430760802065)
                      ·
                        rfl

theorem cell23_2290853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_2290853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290853 prefixEnd_2290853 := by exact prefixLift 2290853
  have htrace : WordTrace (prefixWord ++ tailWord_2290853) baseStart_2290853 baseEnd_2290853 := by
    simpa [prefixWord, tailWord_2290853, baseEnd_2290853] using wordTrace_append hprefix tailTrace_2290853
  have hstable : (prefixWord ++ tailWord_2290853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290853).length < 2 ^ (prefixWord ++ tailWord_2290853).sum := by decide
  have hdescent : baseEnd_2290853 < baseStart_2290853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290866 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2290866 : Nat := 118140960795 + 2290866 * 2 ^ 59
def prefixEnd_2290866 : Nat := 4983230072969 + 3 ^ 40 * 2290866 * 2
def baseEnd_2290866 : Nat := 1176315373042939209939505

theorem tailTrace_2290866 : CollatzResearch.WordTrace tailWord_2290866 prefixEnd_2290866 1176315373042939209939505 := by
  unfold tailWord_2290866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888686829647801402251113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55703164879060803739336301 20888686829647801402251113)
  ·
    refine ⟨15666515122235851051688335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20888686829647801402251113 15666515122235851051688335)
    ·
      refine ⟨23499772683353776577532503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666515122235851051688335 23499772683353776577532503)
      ·
        refine ⟨35249659025030664866298755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23499772683353776577532503 35249659025030664866298755)
        ·
          refine ⟨52874488537545997299448133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35249659025030664866298755 52874488537545997299448133)
          ·
            refine ⟨9913966600789874493646525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52874488537545997299448133 9913966600789874493646525)
            ·
              refine ⟨3717737475296202935117447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9913966600789874493646525 3717737475296202935117447)
              ·
                refine ⟨5576606212944304402676171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717737475296202935117447 5576606212944304402676171)
                ·
                  refine ⟨8364909319416456604014257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576606212944304402676171 8364909319416456604014257)
                  ·
                    refine ⟨6273681989562342453010693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8364909319416456604014257 6273681989562342453010693)
                    ·
                      refine ⟨1176315373042939209939505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6273681989562342453010693 1176315373042939209939505)
                      ·
                        rfl

theorem cell23_2290866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2290866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290866 prefixEnd_2290866 := by exact prefixLift 2290866
  have htrace : WordTrace (prefixWord ++ tailWord_2290866) baseStart_2290866 baseEnd_2290866 := by
    simpa [prefixWord, tailWord_2290866, baseEnd_2290866] using wordTrace_append hprefix tailTrace_2290866
  have hstable : (prefixWord ++ tailWord_2290866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290866).length < 2 ^ (prefixWord ++ tailWord_2290866).sum := by decide
  have hdescent : baseEnd_2290866 < baseStart_2290866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290873 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2290873 : Nat := 118140960795 + 2290873 * 2 ^ 59
def prefixEnd_2290873 : Nat := 4983230072969 + 3 ^ 40 * 2290873 * 2
def baseEnd_2290873 : Nat := 1176318967407520682551973

theorem tailTrace_2290873 : CollatzResearch.WordTrace tailWord_2290873 prefixEnd_2290873 1176318967407520682551973 := by
  unfold tailWord_2290873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83555002629565845804509273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55703335086377230536339515 83555002629565845804509273)
  ·
    refine ⟨62666251972174384353381955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83555002629565845804509273 62666251972174384353381955)
    ·
      refine ⟨93999377958261576530072933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62666251972174384353381955 93999377958261576530072933)
      ·
        refine ⟨17624883367174045599388675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93999377958261576530072933 17624883367174045599388675)
        ·
          refine ⟨26437325050761068399083013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17624883367174045599388675 26437325050761068399083013)
          ·
            refine ⟨4956998447017700324828065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26437325050761068399083013 4956998447017700324828065)
            ·
              refine ⟨3717748835263275243621049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4956998447017700324828065 3717748835263275243621049)
              ·
                refine ⟨2788311626447456432715787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3717748835263275243621049 2788311626447456432715787)
                ·
                  refine ⟨4182467439671184649073681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788311626447456432715787 4182467439671184649073681)
                  ·
                    refine ⟨3136850579753388486805261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182467439671184649073681 3136850579753388486805261)
                    ·
                      refine ⟨1176318967407520682551973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3136850579753388486805261 1176318967407520682551973)
                      ·
                        rfl

theorem cell23_2290873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2290873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290873 prefixEnd_2290873 := by exact prefixLift 2290873
  have htrace : WordTrace (prefixWord ++ tailWord_2290873) baseStart_2290873 baseEnd_2290873 := by
    simpa [prefixWord, tailWord_2290873, baseEnd_2290873] using wordTrace_append hprefix tailTrace_2290873
  have hstable : (prefixWord ++ tailWord_2290873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290873).length < 2 ^ (prefixWord ++ tailWord_2290873).sum := by decide
  have hdescent : baseEnd_2290873 < baseStart_2290873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290876 : List Nat := [2, 2, 2, 3, 2, 1, 4, 7]
def baseStart_2290876 : Nat := 118140960795 + 2290876 * 2 ^ 59
def prefixEnd_2290876 : Nat := 4983230072969 + 3 ^ 40 * 2290876 * 2
def baseEnd_2290876 : Nat := 43567426216647561882017

theorem tailTrace_2290876 : CollatzResearch.WordTrace tailWord_2290876 prefixEnd_2290876 43567426216647561882017 := by
  unfold tailWord_2290876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41777556024277488658434241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55703408032369984877912321 41777556024277488658434241)
  ·
    refine ⟨31333167018208116493825681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41777556024277488658434241 31333167018208116493825681)
    ·
      refine ⟨23499875263656087370369261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31333167018208116493825681 23499875263656087370369261)
      ·
        refine ⟨8812453223871032763888473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23499875263656087370369261 8812453223871032763888473)
        ·
          refine ⟨6609339917903274572916355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8812453223871032763888473 6609339917903274572916355)
          ·
            refine ⟨9914009876854911859374533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609339917903274572916355 9914009876854911859374533)
            ·
              refine ⟨1858876851910295973632725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9914009876854911859374533 1858876851910295973632725)
              ·
                refine ⟨43567426216647561882017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1858876851910295973632725 43567426216647561882017)
                ·
                  rfl

theorem cell23_2290876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 7].length) (baseStart_2290876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290876 prefixEnd_2290876 := by exact prefixLift 2290876
  have htrace : WordTrace (prefixWord ++ tailWord_2290876) baseStart_2290876 baseEnd_2290876 := by
    simpa [prefixWord, tailWord_2290876, baseEnd_2290876] using wordTrace_append hprefix tailTrace_2290876
  have hstable : (prefixWord ++ tailWord_2290876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290876).length < 2 ^ (prefixWord ++ tailWord_2290876).sum := by decide
  have hdescent : baseEnd_2290876 < baseStart_2290876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290904 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_2290904 : Nat := 118140960795 + 2290904 * 2 ^ 59
def prefixEnd_2290904 : Nat := 4983230072969 + 3 ^ 40 * 2290904 * 2
def baseEnd_2290904 : Nat := 1176334885307810061264331

theorem tailTrace_2290904 : CollatzResearch.WordTrace tailWord_2290904 prefixEnd_2290904 1176334885307810061264331 := by
  unfold tailWord_2290904
  simp only [CollatzResearch.WordTrace]
  refine ⟨41778066646226769049443883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55704088861635692065925177 41778066646226769049443883)
  ·
    refine ⟨62667099969340153574165825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41778066646226769049443883 62667099969340153574165825)
    ·
      refine ⟨47000324977005115180624369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62667099969340153574165825 47000324977005115180624369)
      ·
        refine ⟨35250243732753836385468277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47000324977005115180624369 35250243732753836385468277)
        ·
          refine ⟨3304710349945672161137651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35250243732753836385468277 3304710349945672161137651)
          ·
            refine ⟨4957065524918508241706477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304710349945672161137651 4957065524918508241706477)
            ·
              refine ⟨1858899571844440590639929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4957065524918508241706477 1858899571844440590639929)
              ·
                refine ⟨1394174678883330442979947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858899571844440590639929 1394174678883330442979947)
                ·
                  refine ⟨2091262018324995664469921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394174678883330442979947 2091262018324995664469921)
                  ·
                    refine ⟨1568446513743746748352441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091262018324995664469921 1568446513743746748352441)
                    ·
                      refine ⟨1176334885307810061264331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568446513743746748352441 1176334885307810061264331)
                      ·
                        rfl

theorem cell23_2290904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_2290904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290904 prefixEnd_2290904 := by exact prefixLift 2290904
  have htrace : WordTrace (prefixWord ++ tailWord_2290904) baseStart_2290904 baseEnd_2290904 := by
    simpa [prefixWord, tailWord_2290904, baseEnd_2290904] using wordTrace_append hprefix tailTrace_2290904
  have hstable : (prefixWord ++ tailWord_2290904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290904).length < 2 ^ (prefixWord ++ tailWord_2290904).sum := by decide
  have hdescent : baseEnd_2290904 < baseStart_2290904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290930 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2290930 : Nat := 118140960795 + 2290930 * 2 ^ 59
def prefixEnd_2290930 : Nat := 4983230072969 + 3 ^ 40 * 2290930 * 2
def baseEnd_2290930 : Nat := 1176348235804826959539211

theorem tailTrace_2290930 : CollatzResearch.WordTrace tailWord_2290930 prefixEnd_2290930 1176348235804826959539211 := by
  unfold tailWord_2290930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20889270397589836134833561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55704721060239563026222829 20889270397589836134833561)
  ·
    refine ⟨15666952798192377101125171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20889270397589836134833561 15666952798192377101125171)
    ·
      refine ⟨23500429197288565651687757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666952798192377101125171 23500429197288565651687757)
      ·
        refine ⟨8812660948983212119382909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23500429197288565651687757 8812660948983212119382909)
        ·
          refine ⟨3304747855868704544768591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8812660948983212119382909 3304747855868704544768591)
          ·
            refine ⟨4957121783803056817152887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304747855868704544768591 4957121783803056817152887)
            ·
              refine ⟨7435682675704585225729331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957121783803056817152887 7435682675704585225729331)
              ·
                refine ⟨11153524013556877838593997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7435682675704585225729331 11153524013556877838593997)
                ·
                  refine ⟨4182571505083829189472749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11153524013556877838593997 4182571505083829189472749)
                  ·
                    refine ⟨1568464314406435946052281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4182571505083829189472749 1568464314406435946052281)
                    ·
                      refine ⟨1176348235804826959539211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568464314406435946052281 1176348235804826959539211)
                      ·
                        rfl

theorem cell23_2290930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2290930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290930 prefixEnd_2290930 := by exact prefixLift 2290930
  have htrace : WordTrace (prefixWord ++ tailWord_2290930) baseStart_2290930 baseEnd_2290930 := by
    simpa [prefixWord, tailWord_2290930, baseEnd_2290930] using wordTrace_append hprefix tailTrace_2290930
  have hstable : (prefixWord ++ tailWord_2290930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290930).length < 2 ^ (prefixWord ++ tailWord_2290930).sum := by decide
  have hdescent : baseEnd_2290930 < baseStart_2290930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290943 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 4, 2]
def baseStart_2290943 : Nat := 118140960795 + 2290943 * 2 ^ 59
def prefixEnd_2290943 : Nat := 4983230072969 + 3 ^ 40 * 2290943 * 2
def baseEnd_2290943 : Nat := 1176354911053335408676651

theorem tailTrace_2290943 : CollatzResearch.WordTrace tailWord_2290943 prefixEnd_2290943 1176354911053335408676651 := by
  unfold tailWord_2290943
  simp only [CollatzResearch.WordTrace]
  refine ⟨83557555739312247759557483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55705037159541498506371655 83557555739312247759557483)
  ·
    refine ⟨125336333608968371639336225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83557555739312247759557483 125336333608968371639336225)
    ·
      refine ⟨94002250206726278729502169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125336333608968371639336225 94002250206726278729502169)
      ·
        refine ⟨70501687655044709047126627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94002250206726278729502169 70501687655044709047126627)
        ·
          refine ⟨105752531482567063570689941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70501687655044709047126627 105752531482567063570689941)
          ·
            refine ⟨4957149913245331104876091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105752531482567063570689941 4957149913245331104876091)
            ·
              refine ⟨7435724869867996657314137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957149913245331104876091 7435724869867996657314137)
              ·
                refine ⟨5576793652400997492985603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7435724869867996657314137 5576793652400997492985603)
                ·
                  refine ⟨8365190478601496239478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576793652400997492985603 8365190478601496239478405)
                  ·
                    refine ⟨1568473214737780544902201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8365190478601496239478405 1568473214737780544902201)
                    ·
                      refine ⟨1176354911053335408676651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568473214737780544902201 1176354911053335408676651)
                      ·
                        rfl

theorem cell23_2290943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_2290943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290943 prefixEnd_2290943 := by exact prefixLift 2290943
  have htrace : WordTrace (prefixWord ++ tailWord_2290943) baseStart_2290943 baseEnd_2290943 := by
    simpa [prefixWord, tailWord_2290943, baseEnd_2290943] using wordTrace_append hprefix tailTrace_2290943
  have hstable : (prefixWord ++ tailWord_2290943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290943).length < 2 ^ (prefixWord ++ tailWord_2290943).sum := by decide
  have hdescent : baseEnd_2290943 < baseStart_2290943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290973 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2290973 : Nat := 118140960795 + 2290973 * 2 ^ 59
def prefixEnd_2290973 : Nat := 4983230072969 + 3 ^ 40 * 2290973 * 2
def baseEnd_2290973 : Nat := 1176370315472970291301513

theorem tailTrace_2290973 : CollatzResearch.WordTrace tailWord_2290973 prefixEnd_2290973 1176370315472970291301513 := by
  unfold tailWord_2290973
  simp only [CollatzResearch.WordTrace]
  refine ⟨83558649929203562883149573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55705766619469041922099715 83558649929203562883149573)
  ·
    refine ⟨15667246861725668040590545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83558649929203562883149573 15667246861725668040590545)
    ·
      refine ⟨11750435146294251030442909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15667246861725668040590545 11750435146294251030442909)
      ·
        refine ⟨4406413179860344136416091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11750435146294251030442909 4406413179860344136416091)
        ·
          refine ⟨6609619769790516204624137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406413179860344136416091 6609619769790516204624137)
          ·
            refine ⟨4957214827342887153468103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609619769790516204624137 4957214827342887153468103)
            ·
              refine ⟨7435822241014330730202155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957214827342887153468103 7435822241014330730202155)
              ·
                refine ⟨11153733361521496095303233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7435822241014330730202155 11153733361521496095303233)
                ·
                  refine ⟨8365300021141122071477425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11153733361521496095303233 8365300021141122071477425)
                  ·
                    refine ⟨6273975015855841553608069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8365300021141122071477425 6273975015855841553608069)
                    ·
                      refine ⟨1176370315472970291301513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6273975015855841553608069 1176370315472970291301513)
                      ·
                        rfl

theorem cell23_2290973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2290973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290973 prefixEnd_2290973 := by exact prefixLift 2290973
  have htrace : WordTrace (prefixWord ++ tailWord_2290973) baseStart_2290973 baseEnd_2290973 := by
    simpa [prefixWord, tailWord_2290973, baseEnd_2290973] using wordTrace_append hprefix tailTrace_2290973
  have hstable : (prefixWord ++ tailWord_2290973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290973).length < 2 ^ (prefixWord ++ tailWord_2290973).sum := by decide
  have hdescent : baseEnd_2290973 < baseStart_2290973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290998 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2290998 : Nat := 118140960795 + 2290998 * 2 ^ 59
def prefixEnd_2290998 : Nat := 4983230072969 + 3 ^ 40 * 2290998 * 2
def baseEnd_2290998 : Nat := 1176383152489332693488899

theorem tailTrace_2290998 : CollatzResearch.WordTrace tailWord_2290998 prefixEnd_2290998 1176383152489332693488899 := by
  unfold tailWord_2290998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222472609632062009550603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55706374502741994768539765 5222472609632062009550603)
  ·
    refine ⟨7833708914448093014325905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222472609632062009550603 7833708914448093014325905)
    ·
      refine ⟨5875281685836069760744429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7833708914448093014325905 5875281685836069760744429)
      ·
        refine ⟨2203230632188526160279161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5875281685836069760744429 2203230632188526160279161)
        ·
          refine ⟨1652422974141394620209371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203230632188526160279161 1652422974141394620209371)
          ·
            refine ⟨2478634461212091930314057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652422974141394620209371 2478634461212091930314057)
            ·
              refine ⟨1858975845909068947735543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478634461212091930314057 1858975845909068947735543)
              ·
                refine ⟨2788463768863603421603315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858975845909068947735543 2788463768863603421603315)
                ·
                  refine ⟨4182695653295405132404973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788463768863603421603315 4182695653295405132404973)
                  ·
                    refine ⟨1568510869985776924651865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4182695653295405132404973 1568510869985776924651865)
                    ·
                      refine ⟨1176383152489332693488899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568510869985776924651865 1176383152489332693488899)
                      ·
                        rfl

theorem cell23_2290998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2290998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2290998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2290998 prefixEnd_2290998 := by exact prefixLift 2290998
  have htrace : WordTrace (prefixWord ++ tailWord_2290998) baseStart_2290998 baseEnd_2290998 := by
    simpa [prefixWord, tailWord_2290998, baseEnd_2290998] using wordTrace_append hprefix tailTrace_2290998
  have hstable : (prefixWord ++ tailWord_2290998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290998).length < 2 ^ (prefixWord ++ tailWord_2290998).sum := by decide
  have hdescent : baseEnd_2290998 < baseStart_2290998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291016 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2291016 : Nat := 118140960795 + 2291016 * 2 ^ 59
def prefixEnd_2291016 : Nat := 4983230072969 + 3 ^ 40 * 2291016 * 2
def baseEnd_2291016 : Nat := 1176392395141113623063815

theorem tailTrace_2291016 : CollatzResearch.WordTrace tailWord_2291016 prefixEnd_2291016 1176392395141113623063815 := by
  unfold tailWord_2291016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41780109134023890613482451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55706812178698520817976601 41780109134023890613482451)
  ·
    refine ⟨62670163701035835920223677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41780109134023890613482451 62670163701035835920223677)
    ·
      refine ⟨23501311387888438470083879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62670163701035835920223677 23501311387888438470083879)
      ·
        refine ⟨35251967081832657705125819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23501311387888438470083879 35251967081832657705125819)
        ·
          refine ⟨52877950622748986557688729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35251967081832657705125819 52877950622748986557688729)
          ·
            refine ⟨39658462967061739918266547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52877950622748986557688729 39658462967061739918266547)
            ·
              refine ⟨59487694450592609877399821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39658462967061739918266547 59487694450592609877399821)
              ·
                refine ⟨22307885418972228704024933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59487694450592609877399821 22307885418972228704024933)
                ·
                  refine ⟨4182728516057292882004675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22307885418972228704024933 4182728516057292882004675)
                  ·
                    refine ⟨6274092774085939323007013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182728516057292882004675 6274092774085939323007013)
                    ·
                      refine ⟨1176392395141113623063815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6274092774085939323007013 1176392395141113623063815)
                      ·
                        rfl

theorem cell23_2291016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2291016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291016 prefixEnd_2291016 := by exact prefixLift 2291016
  have htrace : WordTrace (prefixWord ++ tailWord_2291016) baseStart_2291016 baseEnd_2291016 := by
    simpa [prefixWord, tailWord_2291016, baseEnd_2291016] using wordTrace_append hprefix tailTrace_2291016
  have hstable : (prefixWord ++ tailWord_2291016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291016).length < 2 ^ (prefixWord ++ tailWord_2291016).sum := by decide
  have hdescent : baseEnd_2291016 < baseStart_2291016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291033 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 4, 2]
def baseStart_2291033 : Nat := 118140960795 + 2291033 * 2 ^ 59
def prefixEnd_2291033 : Nat := 4983230072969 + 3 ^ 40 * 2291033 * 2
def baseEnd_2291033 : Nat := 1176401124312240056551237

theorem tailTrace_2291033 : CollatzResearch.WordTrace tailWord_2291033 prefixEnd_2291033 1176401124312240056551237 := by
  unfold tailWord_2291033
  simp only [CollatzResearch.WordTrace]
  refine ⟨83560838308986193130333753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55707225539324128753555835 83560838308986193130333753)
  ·
    refine ⟨62670628731739644847750315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83560838308986193130333753 62670628731739644847750315)
    ·
      refine ⟨94005943097609467271625473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62670628731739644847750315 94005943097609467271625473)
      ·
        refine ⟨70504457323207100453719105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94005943097609467271625473 70504457323207100453719105)
        ·
          refine ⟨52878342992405325340289329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70504457323207100453719105 52878342992405325340289329)
          ·
            refine ⟨39658757244303994005216997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52878342992405325340289329 39658757244303994005216997)
            ·
              refine ⟨7436016983306998875978187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39658757244303994005216997 7436016983306998875978187)
              ·
                refine ⟨11154025474960498313967281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7436016983306998875978187 11154025474960498313967281)
                ·
                  refine ⟨8365519106220373735475461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11154025474960498313967281 8365519106220373735475461)
                  ·
                    refine ⟨1568534832416320075401649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8365519106220373735475461 1568534832416320075401649)
                    ·
                      refine ⟨1176401124312240056551237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568534832416320075401649 1176401124312240056551237)
                      ·
                        rfl

theorem cell23_2291033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_2291033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291033 prefixEnd_2291033 := by exact prefixLift 2291033
  have htrace : WordTrace (prefixWord ++ tailWord_2291033) baseStart_2291033 baseEnd_2291033 := by
    simpa [prefixWord, tailWord_2291033, baseEnd_2291033] using wordTrace_append hprefix tailTrace_2291033
  have hstable : (prefixWord ++ tailWord_2291033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291033).length < 2 ^ (prefixWord ++ tailWord_2291033).sum := by decide
  have hdescent : baseEnd_2291033 < baseStart_2291033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291043 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 3, 4]
def baseStart_2291043 : Nat := 118140960795 + 2291043 * 2 ^ 59
def prefixEnd_2291043 : Nat := 4983230072969 + 3 ^ 40 * 2291043 * 2
def baseEnd_2291043 : Nat := 392135419706261672475397

theorem tailTrace_2291043 : CollatzResearch.WordTrace tailWord_2291043 prefixEnd_2291043 392135419706261672475397 := by
  unfold tailWord_2291043
  simp only [CollatzResearch.WordTrace]
  refine ⟨83561203038949964838197783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55707468692633309892131855 83561203038949964838197783)
  ·
    refine ⟨125341804558424947257296675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83561203038949964838197783 125341804558424947257296675)
    ·
      refine ⟨188012706837637420885945013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125341804558424947257296675 188012706837637420885945013)
      ·
        refine ⟨17626191266028508208057345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188012706837637420885945013 17626191266028508208057345)
        ·
          refine ⟨13219643449521381156043009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17626191266028508208057345 13219643449521381156043009)
          ·
            refine ⟨9914732587141035867032257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13219643449521381156043009 9914732587141035867032257)
            ·
              refine ⟨7436049440355776900274193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9914732587141035867032257 7436049440355776900274193)
              ·
                refine ⟨5577037080266832675205645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7436049440355776900274193 5577037080266832675205645)
                ·
                  refine ⟨2091388905100062253202117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5577037080266832675205645 2091388905100062253202117)
                  ·
                    refine ⟨392135419706261672475397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2091388905100062253202117 392135419706261672475397)
                    ·
                      rfl

theorem cell23_2291043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 4].length) (baseStart_2291043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291043 prefixEnd_2291043 := by exact prefixLift 2291043
  have htrace : WordTrace (prefixWord ++ tailWord_2291043) baseStart_2291043 baseEnd_2291043 := by
    simpa [prefixWord, tailWord_2291043, baseEnd_2291043] using wordTrace_append hprefix tailTrace_2291043
  have hstable : (prefixWord ++ tailWord_2291043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291043).length < 2 ^ (prefixWord ++ tailWord_2291043).sum := by decide
  have hdescent : baseEnd_2291043 < baseStart_2291043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291053 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2291053 : Nat := 118140960795 + 2291053 * 2 ^ 59
def prefixEnd_2291053 : Nat := 4983230072969 + 3 ^ 40 * 2291053 * 2
def baseEnd_2291053 : Nat := 1176411393925329978301145

theorem tailTrace_2291053 : CollatzResearch.WordTrace tailWord_2291053 prefixEnd_2291053 1176411393925329978301145 := by
  unfold tailWord_2291053
  simp only [CollatzResearch.WordTrace]
  refine ⟨83561567768913736546061813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55707711845942491030707875 83561567768913736546061813)
  ·
    refine ⟨7833896978335662801193295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83561567768913736546061813 7833896978335662801193295)
    ·
      refine ⟨11750845467503494201789943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7833896978335662801193295 11750845467503494201789943)
      ·
        refine ⟨17626268201255241302684915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11750845467503494201789943 17626268201255241302684915)
        ·
          refine ⟨26439402301882861954027373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17626268201255241302684915 26439402301882861954027373)
          ·
            refine ⟨9914775863206073232760265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26439402301882861954027373 9914775863206073232760265)
            ·
              refine ⟨7436081897404554924570199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9914775863206073232760265 7436081897404554924570199)
              ·
                refine ⟨11154122846106832386855299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7436081897404554924570199 11154122846106832386855299)
                ·
                  refine ⟨16731184269160248580282949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11154122846106832386855299 16731184269160248580282949)
                  ·
                    refine ⟨3137097050467546608803053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16731184269160248580282949 3137097050467546608803053)
                    ·
                      refine ⟨1176411393925329978301145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137097050467546608803053 1176411393925329978301145)
                      ·
                        rfl

theorem cell23_2291053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2291053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291053 prefixEnd_2291053 := by exact prefixLift 2291053
  have htrace : WordTrace (prefixWord ++ tailWord_2291053) baseStart_2291053 baseEnd_2291053 := by
    simpa [prefixWord, tailWord_2291053, baseEnd_2291053] using wordTrace_append hprefix tailTrace_2291053
  have hstable : (prefixWord ++ tailWord_2291053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291053).length < 2 ^ (prefixWord ++ tailWord_2291053).sum := by decide
  have hdescent : baseEnd_2291053 < baseStart_2291053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291066 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_2291066 : Nat := 118140960795 + 2291066 * 2 ^ 59
def prefixEnd_2291066 : Nat := 4983230072969 + 3 ^ 40 * 2291066 * 2
def baseEnd_2291066 : Nat := 1176418069173838427438585

theorem tailTrace_2291066 : CollatzResearch.WordTrace tailWord_2291066 prefixEnd_2291066 1176418069173838427438585 := by
  unfold tailWord_2291066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20890510479466659941571263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55708027945244426510856701 20890510479466659941571263)
  ·
    refine ⟨31335765719199989912356895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20890510479466659941571263 31335765719199989912356895)
    ·
      refine ⟨47003648578799984868535343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31335765719199989912356895 47003648578799984868535343)
      ·
        refine ⟨70505472868199977302803015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47003648578799984868535343 70505472868199977302803015)
        ·
          refine ⟨105758209302299965954204523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70505472868199977302803015 105758209302299965954204523)
          ·
            refine ⟨158637313953449948931306785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105758209302299965954204523 158637313953449948931306785)
            ·
              refine ⟨118977985465087461698480089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158637313953449948931306785 118977985465087461698480089)
              ·
                refine ⟨89233489098815596273860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118977985465087461698480089 89233489098815596273860067)
                ·
                  refine ⟨133850233648223394410790101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89233489098815596273860067 133850233648223394410790101)
                  ·
                    refine ⟨3137114851130235806502893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133850233648223394410790101 3137114851130235806502893)
                    ·
                      refine ⟨1176418069173838427438585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137114851130235806502893 1176418069173838427438585)
                      ·
                        rfl

theorem cell23_2291066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_2291066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291066 prefixEnd_2291066 := by exact prefixLift 2291066
  have htrace : WordTrace (prefixWord ++ tailWord_2291066) baseStart_2291066 baseEnd_2291066 := by
    simpa [prefixWord, tailWord_2291066, baseEnd_2291066] using wordTrace_append hprefix tailTrace_2291066
  have hstable : (prefixWord ++ tailWord_2291066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291066).length < 2 ^ (prefixWord ++ tailWord_2291066).sum := by decide
  have hdescent : baseEnd_2291066 < baseStart_2291066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291093 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_2291093 : Nat := 118140960795 + 2291093 * 2 ^ 59
def prefixEnd_2291093 : Nat := 4983230072969 + 3 ^ 40 * 2291093 * 2
def baseEnd_2291093 : Nat := 1176431933151509821800961

theorem tailTrace_2291093 : CollatzResearch.WordTrace tailWord_2291093 prefixEnd_2291093 1176431933151509821800961 := by
  unfold tailWord_2291093
  simp only [CollatzResearch.WordTrace]
  refine ⟨83563026688768823377517933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55708684459179215585011955 83563026688768823377517933)
  ·
    refine ⟨31336135008288308766569225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83563026688768823377517933 31336135008288308766569225)
    ·
      refine ⟨23502101256216231574926919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31336135008288308766569225 23502101256216231574926919)
      ·
        refine ⟨35253151884324347362390379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23502101256216231574926919 35253151884324347362390379)
        ·
          refine ⟨52879727826486521043585569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35253151884324347362390379 52879727826486521043585569)
          ·
            refine ⟨39659795869864890782689177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52879727826486521043585569 39659795869864890782689177)
            ·
              refine ⟨29744846902398668087016883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39659795869864890782689177 29744846902398668087016883)
              ·
                refine ⟨44617270353598002130525325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29744846902398668087016883 44617270353598002130525325)
                ·
                  refine ⟨16731476382599250798946997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44617270353598002130525325 16731476382599250798946997)
                  ·
                    refine ⟨1568575910868679762401281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16731476382599250798946997 1568575910868679762401281)
                    ·
                      refine ⟨1176431933151509821800961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568575910868679762401281 1176431933151509821800961)
                      ·
                        rfl

theorem cell23_2291093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_2291093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291093 prefixEnd_2291093 := by exact prefixLift 2291093
  have htrace : WordTrace (prefixWord ++ tailWord_2291093) baseStart_2291093 baseEnd_2291093 := by
    simpa [prefixWord, tailWord_2291093, baseEnd_2291093] using wordTrace_append hprefix tailTrace_2291093
  have hstable : (prefixWord ++ tailWord_2291093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291093).length < 2 ^ (prefixWord ++ tailWord_2291093).sum := by decide
  have hdescent : baseEnd_2291093 < baseStart_2291093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291103 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 3, 5]
def baseStart_2291103 : Nat := 118140960795 + 2291103 * 2 ^ 59
def prefixEnd_2291103 : Nat := 4983230072969 + 3 ^ 40 * 2291103 * 2
def baseEnd_2291103 : Nat := 392145689319351594225305

theorem tailTrace_2291103 : CollatzResearch.WordTrace tailWord_2291103 prefixEnd_2291103 392145689319351594225305 := by
  unfold tailWord_2291103
  simp only [CollatzResearch.WordTrace]
  refine ⟨83563391418732595085381963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55708927612488396723587975 83563391418732595085381963)
  ·
    refine ⟨125345087128098892628072945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83563391418732595085381963 125345087128098892628072945)
    ·
      refine ⟨94008815346074169471054709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125345087128098892628072945 94008815346074169471054709)
      ·
        refine ⟨8813326438694453387911379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94008815346074169471054709 8813326438694453387911379)
        ·
          refine ⟨13219989658041680081867069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813326438694453387911379 13219989658041680081867069)
          ·
            refine ⟨4957496121765630030700151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13219989658041680081867069 4957496121765630030700151)
            ·
              refine ⟨7436244182648445046050227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957496121765630030700151 7436244182648445046050227)
              ·
                refine ⟨11154366273972667569075341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7436244182648445046050227 11154366273972667569075341)
                ·
                  refine ⟨4182887352739750338403253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154366273972667569075341 4182887352739750338403253)
                  ·
                    refine ⟨392145689319351594225305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4182887352739750338403253 392145689319351594225305)
                    ·
                      rfl

theorem cell23_2291103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_2291103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291103 prefixEnd_2291103 := by exact prefixLift 2291103
  have htrace : WordTrace (prefixWord ++ tailWord_2291103) baseStart_2291103 baseEnd_2291103 := by
    simpa [prefixWord, tailWord_2291103, baseEnd_2291103] using wordTrace_append hprefix tailTrace_2291103
  have hstable : (prefixWord ++ tailWord_2291103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291103).length < 2 ^ (prefixWord ++ tailWord_2291103).sum := by decide
  have hdescent : baseEnd_2291103 < baseStart_2291103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291116 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_2291116 : Nat := 118140960795 + 2291116 * 2 ^ 59
def prefixEnd_2291116 : Nat := 4983230072969 + 3 ^ 40 * 2291116 * 2
def baseEnd_2291116 : Nat := 392147914402187743937785

theorem tailTrace_2291116 : CollatzResearch.WordTrace tailWord_2291116 prefixEnd_2291116 392147914402187743937785 := by
  unfold tailWord_2291116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41781932783842749152802601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55709243711790332203736801 41781932783842749152802601)
  ·
    refine ⟨31336449587882061864601951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41781932783842749152802601 31336449587882061864601951)
    ·
      refine ⟨47004674381823092796902927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31336449587882061864601951 47004674381823092796902927)
      ·
        refine ⟨70507011572734639195354391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47004674381823092796902927 70507011572734639195354391)
        ·
          refine ⟨105760517359101958793031587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70507011572734639195354391 105760517359101958793031587)
          ·
            refine ⟨158640776038652938189547381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105760517359101958793031587 158640776038652938189547381)
            ·
              refine ⟨14872572753623712955270067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158640776038652938189547381 14872572753623712955270067)
              ·
                refine ⟨22308859130435569432905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14872572753623712955270067 22308859130435569432905101)
                ·
                  refine ⟨8365822173913338537339413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22308859130435569432905101 8365822173913338537339413)
                  ·
                    refine ⟨392147914402187743937785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8365822173913338537339413 392147914402187743937785)
                    ·
                      rfl

theorem cell23_2291116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_2291116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291116 prefixEnd_2291116 := by exact prefixLift 2291116
  have htrace : WordTrace (prefixWord ++ tailWord_2291116) baseStart_2291116 baseEnd_2291116 := by
    simpa [prefixWord, tailWord_2291116, baseEnd_2291116] using wordTrace_append hprefix tailTrace_2291116
  have hstable : (prefixWord ++ tailWord_2291116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291116).length < 2 ^ (prefixWord ++ tailWord_2291116).sum := by decide
  have hdescent : baseEnd_2291116 < baseStart_2291116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291123 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 4]
def baseStart_2291123 : Nat := 118140960795 + 2291123 * 2 ^ 59
def prefixEnd_2291123 : Nat := 4983230072969 + 3 ^ 40 * 2291123 * 2
def baseEnd_2291123 : Nat := 1176447337571144704425823

theorem tailTrace_2291123 : CollatzResearch.WordTrace tailWord_2291123 prefixEnd_2291123 1176447337571144704425823 := by
  unfold tailWord_2291123
  simp only [CollatzResearch.WordTrace]
  refine ⟨83564120878660138501110023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55709413919106759000740015 83564120878660138501110023)
  ·
    refine ⟨125346181317990207751665035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83564120878660138501110023 125346181317990207751665035)
    ·
      refine ⟨188019271976985311627497553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125346181317990207751665035 188019271976985311627497553)
      ·
        refine ⟨141014453982738983720623165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188019271976985311627497553 141014453982738983720623165)
        ·
          refine ⟨52880420243527118895233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141014453982738983720623165 52880420243527118895233687)
          ·
            refine ⟨79320630365290678342850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52880420243527118895233687 79320630365290678342850531)
            ·
              refine ⟨118980945547936017514275797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79320630365290678342850531 118980945547936017514275797)
              ·
                refine ⟨2788615911279750410490839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118980945547936017514275797 2788615911279750410490839)
                ·
                  refine ⟨4182923866919625615736259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788615911279750410490839 4182923866919625615736259)
                  ·
                    refine ⟨6274385800379438423604389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182923866919625615736259 6274385800379438423604389)
                    ·
                      refine ⟨1176447337571144704425823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6274385800379438423604389 1176447337571144704425823)
                      ·
                        rfl

theorem cell23_2291123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_2291123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291123 prefixEnd_2291123 := by exact prefixLift 2291123
  have htrace : WordTrace (prefixWord ++ tailWord_2291123) baseStart_2291123 baseEnd_2291123 := by
    simpa [prefixWord, tailWord_2291123, baseEnd_2291123] using wordTrace_append hprefix tailTrace_2291123
  have hstable : (prefixWord ++ tailWord_2291123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291123).length < 2 ^ (prefixWord ++ tailWord_2291123).sum := by decide
  have hdescent : baseEnd_2291123 < baseStart_2291123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291136 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2291136 : Nat := 118140960795 + 2291136 * 2 ^ 59
def prefixEnd_2291136 : Nat := 4983230072969 + 3 ^ 40 * 2291136 * 2
def baseEnd_2291136 : Nat := 1176454012819653153563263

theorem tailTrace_2291136 : CollatzResearch.WordTrace tailWord_2291136 prefixEnd_2291136 1176454012819653153563263 := by
  unfold tailWord_2291136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782297513806520860666631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55709730018408694480888841 41782297513806520860666631)
  ·
    refine ⟨62673446270709781290999947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41782297513806520860666631 62673446270709781290999947)
    ·
      refine ⟨94010169406064671936499921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62673446270709781290999947 94010169406064671936499921)
      ·
        refine ⟨70507627054548503952374941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94010169406064671936499921 70507627054548503952374941)
        ·
          refine ⟨26440360145455688982140603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70507627054548503952374941 26440360145455688982140603)
          ·
            refine ⟨39660540218183533473210905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26440360145455688982140603 39660540218183533473210905)
            ·
              refine ⟨29745405163637650104908179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39660540218183533473210905 29745405163637650104908179)
              ·
                refine ⟨44618107745456475157362269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29745405163637650104908179 44618107745456475157362269)
                ·
                  refine ⟨16731790404546178184010851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44618107745456475157362269 16731790404546178184010851)
                  ·
                    refine ⟨25097685606819267276016277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16731790404546178184010851 25097685606819267276016277)
                    ·
                      refine ⟨1176454012819653153563263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25097685606819267276016277 1176454012819653153563263)
                      ·
                        rfl

theorem cell23_2291136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2291136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291136 prefixEnd_2291136 := by exact prefixLift 2291136
  have htrace : WordTrace (prefixWord ++ tailWord_2291136) baseStart_2291136 baseEnd_2291136 := by
    simpa [prefixWord, tailWord_2291136, baseEnd_2291136] using wordTrace_append hprefix tailTrace_2291136
  have hstable : (prefixWord ++ tailWord_2291136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291136).length < 2 ^ (prefixWord ++ tailWord_2291136).sum := by decide
  have hdescent : baseEnd_2291136 < baseStart_2291136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291140 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2291140 : Nat := 118140960795 + 2291140 * 2 ^ 59
def prefixEnd_2291140 : Nat := 4983230072969 + 3 ^ 40 * 2291140 * 2
def baseEnd_2291140 : Nat := 1176456066742271137913245

theorem tailTrace_2291140 : CollatzResearch.WordTrace tailWord_2291140 prefixEnd_2291140 1176456066742271137913245 := by
  unfold tailWord_2291140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782370459799275202239437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55709827279732366936319249 41782370459799275202239437)
  ·
    refine ⟨15668388922424728200839789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41782370459799275202239437 15668388922424728200839789)
    ·
      refine ⟨5875645845909273075314921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15668388922424728200839789 5875645845909273075314921)
      ·
        refine ⟨4406734384431954806486191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875645845909273075314921 4406734384431954806486191)
        ·
          refine ⟨6610101576647932209729287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406734384431954806486191 6610101576647932209729287)
          ·
            refine ⟨9915152364971898314593931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610101576647932209729287 9915152364971898314593931)
            ·
              refine ⟨14872728547457847471890897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915152364971898314593931 14872728547457847471890897)
              ·
                refine ⟨11154546410593385603918173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14872728547457847471890897 11154546410593385603918173)
                ·
                  refine ⟨4182954903972519601469315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154546410593385603918173 4182954903972519601469315)
                  ·
                    refine ⟨6274432355958779402203973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182954903972519601469315 6274432355958779402203973)
                    ·
                      refine ⟨1176456066742271137913245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6274432355958779402203973 1176456066742271137913245)
                      ·
                        rfl

theorem cell23_2291140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2291140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291140 prefixEnd_2291140 := by exact prefixLift 2291140
  have htrace : WordTrace (prefixWord ++ tailWord_2291140) baseStart_2291140 baseEnd_2291140 := by
    simpa [prefixWord, tailWord_2291140, baseEnd_2291140] using wordTrace_append hprefix tailTrace_2291140
  have hstable : (prefixWord ++ tailWord_2291140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291140).length < 2 ^ (prefixWord ++ tailWord_2291140).sum := by decide
  have hdescent : baseEnd_2291140 < baseStart_2291140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291143 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_2291143 : Nat := 118140960795 + 2291143 * 2 ^ 59
def prefixEnd_2291143 : Nat := 4983230072969 + 3 ^ 40 * 2291143 * 2
def baseEnd_2291143 : Nat := 1176457607184234626175731

theorem tailTrace_2291143 : CollatzResearch.WordTrace tailWord_2291143 prefixEnd_2291143 1176457607184234626175731 := by
  unfold tailWord_2291143
  simp only [CollatzResearch.WordTrace]
  refine ⟨83564850338587681916838083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55709900225725121277892055 83564850338587681916838083)
  ·
    refine ⟨125347275507881522875257125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83564850338587681916838083 125347275507881522875257125)
    ·
      refine ⟨23502614157727785539110711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125347275507881522875257125 23502614157727785539110711)
      ·
        refine ⟨35253921236591678308666067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23502614157727785539110711 35253921236591678308666067)
        ·
          refine ⟨52880881854887517462999101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35253921236591678308666067 52880881854887517462999101)
          ·
            refine ⟨19830330695582819048624663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52880881854887517462999101 19830330695582819048624663)
            ·
              refine ⟨29745496043374228572936995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19830330695582819048624663 29745496043374228572936995)
              ·
                refine ⟨44618244065061342859405493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29745496043374228572936995 44618244065061342859405493)
                ·
                  refine ⟨4182960381099500893069265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44618244065061342859405493 4182960381099500893069265)
                  ·
                    refine ⟨3137220285824625669801949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182960381099500893069265 3137220285824625669801949)
                    ·
                      refine ⟨1176457607184234626175731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137220285824625669801949 1176457607184234626175731)
                      ·
                        rfl

theorem cell23_2291143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_2291143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291143 prefixEnd_2291143 := by exact prefixLift 2291143
  have htrace : WordTrace (prefixWord ++ tailWord_2291143) baseStart_2291143 baseEnd_2291143 := by
    simpa [prefixWord, tailWord_2291143, baseEnd_2291143] using wordTrace_append hprefix tailTrace_2291143
  have hstable : (prefixWord ++ tailWord_2291143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291143).length < 2 ^ (prefixWord ++ tailWord_2291143).sum := by decide
  have hdescent : baseEnd_2291143 < baseStart_2291143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291150 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2291150 : Nat := 118140960795 + 2291150 * 2 ^ 59
def prefixEnd_2291150 : Nat := 4983230072969 + 3 ^ 40 * 2291150 * 2
def baseEnd_2291150 : Nat := 392153733849605366262733

theorem tailTrace_2291150 : CollatzResearch.WordTrace tailWord_2291150 prefixEnd_2291150 392153733849605366262733 := by
  unfold tailWord_2291150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445638206195290264042863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55710070433041548074895269 10445638206195290264042863)
  ·
    refine ⟨15668457309292935396064295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10445638206195290264042863 15668457309292935396064295)
    ·
      refine ⟨23502685963939403094096443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15668457309292935396064295 23502685963939403094096443)
      ·
        refine ⟨35254028945909104641144665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23502685963939403094096443 35254028945909104641144665)
        ·
          refine ⟨26440521709431828480858499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35254028945909104641144665 26440521709431828480858499)
          ·
            refine ⟨39660782564147742721287749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26440521709431828480858499 39660782564147742721287749)
            ·
              refine ⟨7436396730777701760241453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39660782564147742721287749 7436396730777701760241453)
              ·
                refine ⟨2788648774041638160090545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7436396730777701760241453 2788648774041638160090545)
                ·
                  refine ⟨2091486580531228620067909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2788648774041638160090545 2091486580531228620067909)
                  ·
                    refine ⟨392153733849605366262733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2091486580531228620067909 392153733849605366262733)
                    ·
                      rfl

theorem cell23_2291150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2291150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291150 prefixEnd_2291150 := by exact prefixLift 2291150
  have htrace : WordTrace (prefixWord ++ tailWord_2291150) baseStart_2291150 baseEnd_2291150 := by
    simpa [prefixWord, tailWord_2291150, baseEnd_2291150] using wordTrace_append hprefix tailTrace_2291150
  have hstable : (prefixWord ++ tailWord_2291150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291150).length < 2 ^ (prefixWord ++ tailWord_2291150).sum := by decide
  have hdescent : baseEnd_2291150 < baseStart_2291150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291157 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2291157 : Nat := 118140960795 + 2291157 * 2 ^ 59
def prefixEnd_2291157 : Nat := 4983230072969 + 3 ^ 40 * 2291157 * 2
def baseEnd_2291157 : Nat := 1176464795913397571400667

theorem tailTrace_2291157 : CollatzResearch.WordTrace tailWord_2291157 prefixEnd_2291157 1176464795913397571400667 := by
  unfold tailWord_2291157
  simp only [CollatzResearch.WordTrace]
  refine ⟨83565360960536962307847725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55710240640357974871898483 83565360960536962307847725)
  ·
    refine ⟨31337010360201360865442897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83565360960536962307847725 31337010360201360865442897)
    ·
      refine ⟨23502757770151020649082173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31337010360201360865442897 23502757770151020649082173)
      ·
        refine ⟨8813534163806632743405815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23502757770151020649082173 8813534163806632743405815)
        ·
          refine ⟨13220301245709949115108723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813534163806632743405815 13220301245709949115108723)
          ·
            refine ⟨19830451868564923672663085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13220301245709949115108723 19830451868564923672663085)
            ·
              refine ⟨7436419450711846377248657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19830451868564923672663085 7436419450711846377248657)
              ·
                refine ⟨5577314588033884782936493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7436419450711846377248657 5577314588033884782936493)
                ·
                  refine ⟨2091492970512706793601185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5577314588033884782936493 2091492970512706793601185)
                  ·
                    refine ⟨1568619727884530095200889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091492970512706793601185 1568619727884530095200889)
                    ·
                      refine ⟨1176464795913397571400667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568619727884530095200889 1176464795913397571400667)
                      ·
                        rfl

theorem cell23_2291157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2291157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291157 prefixEnd_2291157 := by exact prefixLift 2291157
  have htrace : WordTrace (prefixWord ++ tailWord_2291157) baseStart_2291157 baseEnd_2291157 := by
    simpa [prefixWord, tailWord_2291157, baseEnd_2291157] using wordTrace_append hprefix tailTrace_2291157
  have hstable : (prefixWord ++ tailWord_2291157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291157).length < 2 ^ (prefixWord ++ tailWord_2291157).sum := by decide
  have hdescent : baseEnd_2291157 < baseStart_2291157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291204 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2291204 : Nat := 118140960795 + 2291204 * 2 ^ 59
def prefixEnd_2291204 : Nat := 4983230072969 + 3 ^ 40 * 2291204 * 2
def baseEnd_2291204 : Nat := 1176488929504158887512951

theorem tailTrace_2291204 : CollatzResearch.WordTrace tailWord_2291204 prefixEnd_2291204 1176488929504158887512951 := by
  unfold tailWord_2291204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41783537595683344667404333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55711383460911126223205777 41783537595683344667404333)
  ·
    refine ⟨15668826598381254250276625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41783537595683344667404333 15668826598381254250276625)
    ·
      refine ⟨11751619948785940687707469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15668826598381254250276625 11751619948785940687707469)
      ·
        refine ⟨4406857480794727757890301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11751619948785940687707469 4406857480794727757890301)
        ·
          refine ⟨1652571555298022909208863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4406857480794727757890301 1652571555298022909208863)
          ·
            refine ⟨2478857332947034363813295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652571555298022909208863 2478857332947034363813295)
            ·
              refine ⟨3718285999420551545719943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478857332947034363813295 3718285999420551545719943)
              ·
                refine ⟨5577428999130827318579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718285999420551545719943 5577428999130827318579915)
                ·
                  refine ⟨8366143498696240977869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5577428999130827318579915 8366143498696240977869873)
                  ·
                    refine ⟨6274607624022180733402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8366143498696240977869873 6274607624022180733402405)
                    ·
                      refine ⟨1176488929504158887512951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6274607624022180733402405 1176488929504158887512951)
                      ·
                        rfl

theorem cell23_2291204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2291204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291204 prefixEnd_2291204 := by exact prefixLift 2291204
  have htrace : WordTrace (prefixWord ++ tailWord_2291204) baseStart_2291204 baseEnd_2291204 := by
    simpa [prefixWord, tailWord_2291204, baseEnd_2291204] using wordTrace_append hprefix tailTrace_2291204
  have hstable : (prefixWord ++ tailWord_2291204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291204).length < 2 ^ (prefixWord ++ tailWord_2291204).sum := by decide
  have hdescent : baseEnd_2291204 < baseStart_2291204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291207 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2291207 : Nat := 118140960795 + 2291207 * 2 ^ 59
def prefixEnd_2291207 : Nat := 4983230072969 + 3 ^ 40 * 2291207 * 2
def baseEnd_2291207 : Nat := 1176490469946122375775437

theorem tailTrace_2291207 : CollatzResearch.WordTrace tailWord_2291207 prefixEnd_2291207 1176490469946122375775437 := by
  unfold tailWord_2291207
  simp only [CollatzResearch.WordTrace]
  refine ⟨83567184610355820847167875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55711456406903880564778583 83567184610355820847167875)
  ·
    refine ⟨125350776915533731270751813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83567184610355820847167875 125350776915533731270751813)
    ·
      refine ⟨23503270671662574613265965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125350776915533731270751813 23503270671662574613265965)
      ·
        refine ⟨8813726501873465479974737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23503270671662574613265965 8813726501873465479974737)
        ·
          refine ⟨6610294876405099109981053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8813726501873465479974737 6610294876405099109981053)
          ·
            refine ⟨2478860578651912166242895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6610294876405099109981053 2478860578651912166242895)
            ·
              refine ⟨3718290867977868249364343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478860578651912166242895 3718290867977868249364343)
              ·
                refine ⟨5577436301966802374046515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718290867977868249364343 5577436301966802374046515)
                ·
                  refine ⟨8366154452950203561069773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5577436301966802374046515 8366154452950203561069773)
                  ·
                    refine ⟨3137307919856326335401165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8366154452950203561069773 3137307919856326335401165)
                    ·
                      refine ⟨1176490469946122375775437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137307919856326335401165 1176490469946122375775437)
                      ·
                        rfl

theorem cell23_2291207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2291207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291207 prefixEnd_2291207 := by exact prefixLift 2291207
  have htrace : WordTrace (prefixWord ++ tailWord_2291207) baseStart_2291207 baseEnd_2291207 := by
    simpa [prefixWord, tailWord_2291207, baseEnd_2291207] using wordTrace_append hprefix tailTrace_2291207
  have hstable : (prefixWord ++ tailWord_2291207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291207).length < 2 ^ (prefixWord ++ tailWord_2291207).sum := by decide
  have hdescent : baseEnd_2291207 < baseStart_2291207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291217 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_2291217 : Nat := 118140960795 + 2291217 * 2 ^ 59
def prefixEnd_2291217 : Nat := 4983230072969 + 3 ^ 40 * 2291217 * 2
def baseEnd_2291217 : Nat := 1176495604752667336650391

theorem tailTrace_2291217 : CollatzResearch.WordTrace tailWord_2291217 prefixEnd_2291217 1176495604752667336650391 := by
  unfold tailWord_2291217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83567549340319592555031905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55711699560213061703354603 83567549340319592555031905)
  ·
    refine ⟨62675662005239694416273929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83567549340319592555031905 62675662005239694416273929)
    ·
      refine ⟨47006746503929770812205447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62675662005239694416273929 47006746503929770812205447)
      ·
        refine ⟨70510119755894656218308171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47006746503929770812205447 70510119755894656218308171)
        ·
          refine ⟨105765179633841984327462257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70510119755894656218308171 105765179633841984327462257)
          ·
            refine ⟨79323884725381488245596693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105765179633841984327462257 79323884725381488245596693)
            ·
              refine ⟨3718307096502257261512345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79323884725381488245596693 3718307096502257261512345)
              ·
                refine ⟨2788730322376692946134259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718307096502257261512345 2788730322376692946134259)
                ·
                  refine ⟨4183095483565039419201389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788730322376692946134259 4183095483565039419201389)
                  ·
                    refine ⟨1568660806336889782200521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4183095483565039419201389 1568660806336889782200521)
                    ·
                      refine ⟨1176495604752667336650391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568660806336889782200521 1176495604752667336650391)
                      ·
                        rfl

theorem cell23_2291217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_2291217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291217 prefixEnd_2291217 := by exact prefixLift 2291217
  have htrace : WordTrace (prefixWord ++ tailWord_2291217) baseStart_2291217 baseEnd_2291217 := by
    simpa [prefixWord, tailWord_2291217, baseEnd_2291217] using wordTrace_append hprefix tailTrace_2291217
  have hstable : (prefixWord ++ tailWord_2291217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291217).length < 2 ^ (prefixWord ++ tailWord_2291217).sum := by decide
  have hdescent : baseEnd_2291217 < baseStart_2291217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291233 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2291233 : Nat := 118140960795 + 2291233 * 2 ^ 59
def prefixEnd_2291233 : Nat := 4983230072969 + 3 ^ 40 * 2291233 * 2
def baseEnd_2291233 : Nat := 1176503820443139274050317

theorem tailTrace_2291233 : CollatzResearch.WordTrace tailWord_2291233 prefixEnd_2291233 1176503820443139274050317 := by
  unfold tailWord_2291233
  simp only [CollatzResearch.WordTrace]
  refine ⟨83568132908261627287614353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55712088605507751525076235 83568132908261627287614353)
  ·
    refine ⟨62676099681196220465710765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83568132908261627287614353 62676099681196220465710765)
    ·
      refine ⟨23503537380448582674641537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62676099681196220465710765 23503537380448582674641537)
      ·
        refine ⟨17627653035336437005981153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23503537380448582674641537 17627653035336437005981153)
        ·
          refine ⟨13220739776502327754485865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17627653035336437005981153 13220739776502327754485865)
          ·
            refine ⟨9915554832376745815864399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13220739776502327754485865 9915554832376745815864399)
            ·
              refine ⟨14873332248565118723796599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915554832376745815864399 14873332248565118723796599)
              ·
                refine ⟨22309998372847678085694899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14873332248565118723796599 22309998372847678085694899)
                ·
                  refine ⟨33464997559271517128542349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22309998372847678085694899 33464997559271517128542349)
                  ·
                    refine ⟨12549374084726818923203381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33464997559271517128542349 12549374084726818923203381)
                    ·
                      refine ⟨1176503820443139274050317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12549374084726818923203381 1176503820443139274050317)
                      ·
                        rfl

theorem cell23_2291233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2291233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291233 prefixEnd_2291233 := by exact prefixLift 2291233
  have htrace : WordTrace (prefixWord ++ tailWord_2291233) baseStart_2291233 baseEnd_2291233 := by
    simpa [prefixWord, tailWord_2291233, baseEnd_2291233] using wordTrace_append hprefix tailTrace_2291233
  have hstable : (prefixWord ++ tailWord_2291233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291233).length < 2 ^ (prefixWord ++ tailWord_2291233).sum := by decide
  have hdescent : baseEnd_2291233 < baseStart_2291233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291290 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_2291290 : Nat := 118140960795 + 2291290 * 2 ^ 59
def prefixEnd_2291290 : Nat := 4983230072969 + 3 ^ 40 * 2291290 * 2
def baseEnd_2291290 : Nat := 1176533088840445551037555

theorem tailTrace_2291290 : CollatzResearch.WordTrace tailWord_2291290 prefixEnd_2291290 1176533088840445551037555 := by
  unfold tailWord_2291290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892552967263781505609831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55713474579370084014959549 20892552967263781505609831)
  ·
    refine ⟨31338829450895672258414747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20892552967263781505609831 31338829450895672258414747)
    ·
      refine ⟨47008244176343508387622121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31338829450895672258414747 47008244176343508387622121)
      ·
        refine ⟨35256183132257631290716591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47008244176343508387622121 35256183132257631290716591)
        ·
          refine ⟨52884274698386446936074887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35256183132257631290716591 52884274698386446936074887)
          ·
            refine ⟨79326412047579670404112331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52884274698386446936074887 79326412047579670404112331)
            ·
              refine ⟨118989618071369505606168497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79326412047579670404112331 118989618071369505606168497)
              ·
                refine ⟨89242213553527129204626373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118989618071369505606168497 89242213553527129204626373)
                ·
                  refine ⟨16732915041286336725867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89242213553527129204626373 16732915041286336725867445)
                  ·
                    refine ⟨1568710785120594068050073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16732915041286336725867445 1568710785120594068050073)
                    ·
                      refine ⟨1176533088840445551037555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568710785120594068050073 1176533088840445551037555)
                      ·
                        rfl

theorem cell23_2291290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_2291290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291290 prefixEnd_2291290 := by exact prefixLift 2291290
  have htrace : WordTrace (prefixWord ++ tailWord_2291290) baseStart_2291290 baseEnd_2291290 := by
    simpa [prefixWord, tailWord_2291290, baseEnd_2291290] using wordTrace_append hprefix tailTrace_2291290
  have hstable : (prefixWord ++ tailWord_2291290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291290).length < 2 ^ (prefixWord ++ tailWord_2291290).sum := by decide
  have hdescent : baseEnd_2291290 < baseStart_2291290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291300 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_2291300 : Nat := 118140960795 + 2291300 * 2 ^ 59
def prefixEnd_2291300 : Nat := 4983230072969 + 3 ^ 40 * 2291300 * 2
def baseEnd_2291300 : Nat := 392179407882330170637503

theorem tailTrace_2291300 : CollatzResearch.WordTrace tailWord_2291300 prefixEnd_2291300 392179407882330170637503 := by
  unfold tailWord_2291300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41785288299509448865151677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55713717732679265153535569 41785288299509448865151677)
  ·
    refine ⟨15669483112316043324431879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41785288299509448865151677 15669483112316043324431879)
    ·
      refine ⟨23504224668474064986647819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15669483112316043324431879 23504224668474064986647819)
      ·
        refine ⟨35256337002711097479971729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23504224668474064986647819 35256337002711097479971729)
        ·
          refine ⟨26442252752033323109978797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35256337002711097479971729 26442252752033323109978797)
          ·
            refine ⟨9915844782012496166242049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26442252752033323109978797 9915844782012496166242049)
            ·
              refine ⟨7436883586509372124681537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9915844782012496166242049 7436883586509372124681537)
              ·
                refine ⟨5577662689882029093511153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7436883586509372124681537 5577662689882029093511153)
                ·
                  refine ⟨4183247017411521820133365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5577662689882029093511153 4183247017411521820133365)
                  ·
                    refine ⟨392179407882330170637503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4183247017411521820133365 392179407882330170637503)
                    ·
                      rfl

theorem cell23_2291300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_2291300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291300 prefixEnd_2291300 := by exact prefixLift 2291300
  have htrace : WordTrace (prefixWord ++ tailWord_2291300) baseStart_2291300 baseEnd_2291300 := by
    simpa [prefixWord, tailWord_2291300, baseEnd_2291300] using wordTrace_append hprefix tailTrace_2291300
  have hstable : (prefixWord ++ tailWord_2291300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291300).length < 2 ^ (prefixWord ++ tailWord_2291300).sum := by decide
  have hdescent : baseEnd_2291300 < baseStart_2291300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291304 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 5]
def baseStart_2291304 : Nat := 118140960795 + 2291304 * 2 ^ 59
def prefixEnd_2291304 : Nat := 4983230072969 + 3 ^ 40 * 2291304 * 2
def baseEnd_2291304 : Nat := 130726697507734277362499

theorem tailTrace_2291304 : CollatzResearch.WordTrace tailWord_2291304 prefixEnd_2291304 130726697507734277362499 := by
  unfold tailWord_2291304
  simp only [CollatzResearch.WordTrace]
  refine ⟨41785361245502203206724483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55713814994002937608965977 41785361245502203206724483)
  ·
    refine ⟨62678041868253304810086725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41785361245502203206724483 62678041868253304810086725)
    ·
      refine ⟨11752132850297494651891261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62678041868253304810086725 11752132850297494651891261)
      ·
        refine ⟨4407049818861560494459223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11752132850297494651891261 4407049818861560494459223)
        ·
          refine ⟨6610574728292340741688835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407049818861560494459223 6610574728292340741688835)
          ·
            refine ⟨9915862092438511112533253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610574728292340741688835 9915862092438511112533253)
            ·
              refine ⟨1859224142332220833599985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9915862092438511112533253 1859224142332220833599985)
              ·
                refine ⟨1394418106749165625199989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859224142332220833599985 1394418106749165625199989)
                ·
                  refine ⟨130726697507734277362499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1394418106749165625199989 130726697507734277362499)
                  ·
                    rfl

theorem cell23_2291304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 5].length) (baseStart_2291304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291304 prefixEnd_2291304 := by exact prefixLift 2291304
  have htrace : WordTrace (prefixWord ++ tailWord_2291304) baseStart_2291304 baseEnd_2291304 := by
    simpa [prefixWord, tailWord_2291304, baseEnd_2291304] using wordTrace_append hprefix tailTrace_2291304
  have hstable : (prefixWord ++ tailWord_2291304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291304).length < 2 ^ (prefixWord ++ tailWord_2291304).sum := by decide
  have hdescent : baseEnd_2291304 < baseStart_2291304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291340 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2291340 : Nat := 118140960795 + 2291340 * 2 ^ 59
def prefixEnd_2291340 : Nat := 4983230072969 + 3 ^ 40 * 2291340 * 2
def baseEnd_2291340 : Nat := 1176558762873170355412325

theorem tailTrace_2291340 : CollatzResearch.WordTrace tailWord_2291340 prefixEnd_2291340 1176558762873170355412325 := by
  unfold tailWord_2291340
  simp only [CollatzResearch.WordTrace]
  refine ⟨41786017759436992280879737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55714690345915989707839649 41786017759436992280879737)
  ·
    refine ⟨31339513319577744210659803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41786017759436992280879737 31339513319577744210659803)
    ·
      refine ⟨47009269979366616315989705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31339513319577744210659803 47009269979366616315989705)
      ·
        refine ⟨35256952484524962236992279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47009269979366616315989705 35256952484524962236992279)
        ·
          refine ⟨52885428726787443355488419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35256952484524962236992279 52885428726787443355488419)
          ·
            refine ⟨79328143090181165033232629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52885428726787443355488419 79328143090181165033232629)
            ·
              refine ⟨7437013414704484221865559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79328143090181165033232629 7437013414704484221865559)
              ·
                refine ⟨11155520122056726332798339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7437013414704484221865559 11155520122056726332798339)
                ·
                  refine ⟨16733280183085089499197509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11155520122056726332798339 16733280183085089499197509)
                  ·
                    refine ⟨3137490034328454281099533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16733280183085089499197509 3137490034328454281099533)
                    ·
                      refine ⟨1176558762873170355412325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137490034328454281099533 1176558762873170355412325)
                      ·
                        rfl

theorem cell23_2291340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2291340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291340 prefixEnd_2291340 := by exact prefixLift 2291340
  have htrace : WordTrace (prefixWord ++ tailWord_2291340) baseStart_2291340 baseEnd_2291340 := by
    simpa [prefixWord, tailWord_2291340, baseEnd_2291340] using wordTrace_append hprefix tailTrace_2291340
  have hstable : (prefixWord ++ tailWord_2291340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291340).length < 2 ^ (prefixWord ++ tailWord_2291340).sum := by decide
  have hdescent : baseEnd_2291340 < baseStart_2291340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291360 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 8]
def baseStart_2291360 : Nat := 118140960795 + 2291360 * 2 ^ 59
def prefixEnd_2291360 : Nat := 4983230072969 + 3 ^ 40 * 2291360 * 2
def baseEnd_2291360 : Nat := 130729892498473364129137

theorem tailTrace_2291360 : CollatzResearch.WordTrace tailWord_2291360 prefixEnd_2291360 130729892498473364129137 := by
  unfold tailWord_2291360
  simp only [CollatzResearch.WordTrace]
  refine ⟨41786382489400763988743767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55715176652534351984991689 41786382489400763988743767)
  ·
    refine ⟨62679573734101145983115651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41786382489400763988743767 62679573734101145983115651)
    ·
      refine ⟨94019360601151718974673477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62679573734101145983115651 94019360601151718974673477)
      ·
        refine ⟨17628630112715947307751277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94019360601151718974673477 17628630112715947307751277)
        ·
          refine ⟨6610736292268480240406729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17628630112715947307751277 6610736292268480240406729)
          ·
            refine ⟨4958052219201360180305047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6610736292268480240406729 4958052219201360180305047)
            ·
              refine ⟨7437078328802040270457571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958052219201360180305047 7437078328802040270457571)
              ·
                refine ⟨11155617493203060405686357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7437078328802040270457571 11155617493203060405686357)
                ·
                  refine ⟨130729892498473364129137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11155617493203060405686357 130729892498473364129137)
                  ·
                    rfl

theorem cell23_2291360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_2291360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291360 prefixEnd_2291360 := by exact prefixLift 2291360
  have htrace : WordTrace (prefixWord ++ tailWord_2291360) baseStart_2291360 baseEnd_2291360 := by
    simpa [prefixWord, tailWord_2291360, baseEnd_2291360] using wordTrace_append hprefix tailTrace_2291360
  have hstable : (prefixWord ++ tailWord_2291360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291360).length < 2 ^ (prefixWord ++ tailWord_2291360).sum := by decide
  have hdescent : baseEnd_2291360 < baseStart_2291360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291363 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2291363 : Nat := 118140960795 + 2291363 * 2 ^ 59
def prefixEnd_2291363 : Nat := 4983230072969 + 3 ^ 40 * 2291363 * 2
def baseEnd_2291363 : Nat := 1176570572928223765424719

theorem tailTrace_2291363 : CollatzResearch.WordTrace tailWord_2291363 prefixEnd_2291363 1176570572928223765424719 := by
  unfold tailWord_2291363
  simp only [CollatzResearch.WordTrace]
  refine ⟨83572874397790659489846743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55715249598527106326564495 83572874397790659489846743)
  ·
    refine ⟨125359311596685989234770115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83572874397790659489846743 125359311596685989234770115)
    ·
      refine ⟨188038967395028983852155173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125359311596685989234770115 188038967395028983852155173)
      ·
        refine ⟨35257306386567934472279095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188038967395028983852155173 35257306386567934472279095)
        ·
          refine ⟨52885959579851901708418643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35257306386567934472279095 52885959579851901708418643)
          ·
            refine ⟨79328939369777852562627965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52885959579851901708418643 79328939369777852562627965)
            ·
              refine ⟨29748352263666694710985487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79328939369777852562627965 29748352263666694710985487)
              ·
                refine ⟨44622528395500042066478231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29748352263666694710985487 44622528395500042066478231)
                ·
                  refine ⟨66933792593250063099717347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44622528395500042066478231 66933792593250063099717347)
                  ·
                    refine ⟨100400688889875094649576021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66933792593250063099717347 100400688889875094649576021)
                    ·
                      refine ⟨1176570572928223765424719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100400688889875094649576021 1176570572928223765424719)
                      ·
                        rfl

theorem cell23_2291363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2291363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291363 prefixEnd_2291363 := by exact prefixLift 2291363
  have htrace : WordTrace (prefixWord ++ tailWord_2291363) baseStart_2291363 baseEnd_2291363 := by
    simpa [prefixWord, tailWord_2291363, baseEnd_2291363] using wordTrace_append hprefix tailTrace_2291363
  have hstable : (prefixWord ++ tailWord_2291363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291363).length < 2 ^ (prefixWord ++ tailWord_2291363).sum := by decide
  have hdescent : baseEnd_2291363 < baseStart_2291363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291364 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_2291364 : Nat := 118140960795 + 2291364 * 2 ^ 59
def prefixEnd_2291364 : Nat := 4983230072969 + 3 ^ 40 * 2291364 * 2
def baseEnd_2291364 : Nat := 392190362136292753837405

theorem tailTrace_2291364 : CollatzResearch.WordTrace tailWord_2291364 prefixEnd_2291364 392190362136292753837405 := by
  unfold tailWord_2291364
  simp only [CollatzResearch.WordTrace]
  refine ⟨41786455435393518330316573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55715273913858024440422097 41786455435393518330316573)
  ·
    refine ⟨15669920788272569373868715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41786455435393518330316573 15669920788272569373868715)
    ·
      refine ⟨23504881182408854060803073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15669920788272569373868715 23504881182408854060803073)
      ·
        refine ⟨17628660886806640545602305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23504881182408854060803073 17628660886806640545602305)
        ·
          refine ⟨13221495665104980409201729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17628660886806640545602305 13221495665104980409201729)
          ·
            refine ⟨9916121748828735306901297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13221495665104980409201729 9916121748828735306901297)
            ·
              refine ⟨7437091311621551480175973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9916121748828735306901297 7437091311621551480175973)
              ·
                refine ⟨1394454620929040902532995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7437091311621551480175973 1394454620929040902532995)
                ·
                  refine ⟨2091681931393561353799493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394454620929040902532995 2091681931393561353799493)
                  ·
                    refine ⟨392190362136292753837405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2091681931393561353799493 392190362136292753837405)
                    ·
                      rfl

theorem cell23_2291364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_2291364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291364 prefixEnd_2291364 := by exact prefixLift 2291364
  have htrace : WordTrace (prefixWord ++ tailWord_2291364) baseStart_2291364 baseEnd_2291364 := by
    simpa [prefixWord, tailWord_2291364, baseEnd_2291364] using wordTrace_append hprefix tailTrace_2291364
  have hstable : (prefixWord ++ tailWord_2291364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291364).length < 2 ^ (prefixWord ++ tailWord_2291364).sum := by decide
  have hdescent : baseEnd_2291364 < baseStart_2291364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291454 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2291454 : Nat := 118140960795 + 2291454 * 2 ^ 59
def prefixEnd_2291454 : Nat := 4983230072969 + 3 ^ 40 * 2291454 * 2
def baseEnd_2291454 : Nat := 392205766555927636462267

theorem tailTrace_2291454 : CollatzResearch.WordTrace tailWord_2291454 prefixEnd_2291454 392205766555927636462267 := by
  unfold tailWord_2291454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447024180057622753926177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55717462293640654687606277 10447024180057622753926177)
  ·
    refine ⟨7835268135043217065444633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10447024180057622753926177 7835268135043217065444633)
    ·
      refine ⟨5876451101282412799083475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7835268135043217065444633 5876451101282412799083475)
      ·
        refine ⟨8814676651923619198625213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5876451101282412799083475 8814676651923619198625213)
        ·
          refine ⟨3305503744471357199484455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8814676651923619198625213 3305503744471357199484455)
          ·
            refine ⟨4958255616707035799226683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305503744471357199484455 4958255616707035799226683)
            ·
              refine ⟨7437383425060553698840025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958255616707035799226683 7437383425060553698840025)
              ·
                refine ⟨5578037568795415274130019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7437383425060553698840025 5578037568795415274130019)
                ·
                  refine ⟨8367056353193122911195029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578037568795415274130019 8367056353193122911195029)
                  ·
                    refine ⟨392205766555927636462267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8367056353193122911195029 392205766555927636462267)
                    ·
                      rfl

theorem cell23_2291454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2291454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291454 prefixEnd_2291454 := by exact prefixLift 2291454
  have htrace : WordTrace (prefixWord ++ tailWord_2291454) baseStart_2291454 baseEnd_2291454 := by
    simpa [prefixWord, tailWord_2291454, baseEnd_2291454] using wordTrace_append hprefix tailTrace_2291454
  have hstable : (prefixWord ++ tailWord_2291454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291454).length < 2 ^ (prefixWord ++ tailWord_2291454).sum := by decide
  have hdescent : baseEnd_2291454 < baseStart_2291454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291480 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_2291480 : Nat := 118140960795 + 2291480 * 2 ^ 59
def prefixEnd_2291480 : Nat := 4983230072969 + 3 ^ 40 * 2291480 * 2
def baseEnd_2291480 : Nat := 392210216721599935887227

theorem tailTrace_2291480 : CollatzResearch.WordTrace tailWord_2291480 prefixEnd_2291480 392210216721599935887227 := by
  unfold tailWord_2291480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41788570869183394235927947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55718094492244525647903929 41788570869183394235927947)
  ·
    refine ⟨62682856303775091353891921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41788570869183394235927947 62682856303775091353891921)
    ·
      refine ⟨47012142227831318515418941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62682856303775091353891921 47012142227831318515418941)
      ·
        refine ⟨17629553335436744443282103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47012142227831318515418941 17629553335436744443282103)
        ·
          refine ⟨26444330003155116664923155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17629553335436744443282103 26444330003155116664923155)
          ·
            refine ⟨39666495004732674997384733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26444330003155116664923155 39666495004732674997384733)
            ·
              refine ⟨14874935626774753124019275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39666495004732674997384733 14874935626774753124019275)
              ·
                refine ⟨22312403440162129686028913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14874935626774753124019275 22312403440162129686028913)
                ·
                  refine ⟨16734302580121597264521685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22312403440162129686028913 16734302580121597264521685)
                  ·
                    refine ⟨392210216721599935887227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16734302580121597264521685 392210216721599935887227)
                    ·
                      rfl

theorem cell23_2291480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_2291480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291480 prefixEnd_2291480 := by exact prefixLift 2291480
  have htrace : WordTrace (prefixWord ++ tailWord_2291480) baseStart_2291480 baseEnd_2291480 := by
    simpa [prefixWord, tailWord_2291480, baseEnd_2291480] using wordTrace_append hprefix tailTrace_2291480
  have hstable : (prefixWord ++ tailWord_2291480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291480).length < 2 ^ (prefixWord ++ tailWord_2291480).sum := by decide
  have hdescent : baseEnd_2291480 < baseStart_2291480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291551 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 4, 2]
def baseStart_2291551 : Nat := 118140960795 + 2291551 * 2 ^ 59
def prefixEnd_2291551 : Nat := 4983230072969 + 3 ^ 40 * 2291551 * 2
def baseEnd_2291551 : Nat := 1176667107291269029873855

theorem tailTrace_2291551 : CollatzResearch.WordTrace tailWord_2291551 prefixEnd_2291551 1176667107291269029873855 := by
  unfold tailWord_2291551
  simp only [CollatzResearch.WordTrace]
  refine ⟨83579731321109567597690507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55719820880739711731793671 83579731321109567597690507)
  ·
    refine ⟨125369596981664351396535761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83579731321109567597690507 125369596981664351396535761)
    ·
      refine ⟨94027197736248263547401821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125369596981664351396535761 94027197736248263547401821)
      ·
        refine ⟨35260199151093098830275683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94027197736248263547401821 35260199151093098830275683)
        ·
          refine ⟨52890298726639648245413525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35260199151093098830275683 52890298726639648245413525)
          ·
            refine ⟨2479232752811233511503759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52890298726639648245413525 2479232752811233511503759)
            ·
              refine ⟨3718849129216850267255639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479232752811233511503759 3718849129216850267255639)
              ·
                refine ⟨5578273693825275400883459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718849129216850267255639 5578273693825275400883459)
                ·
                  refine ⟨8367410540737913101325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578273693825275400883459 8367410540737913101325189)
                  ·
                    refine ⟨1568889476388358706498473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8367410540737913101325189 1568889476388358706498473)
                    ·
                      refine ⟨1176667107291269029873855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568889476388358706498473 1176667107291269029873855)
                      ·
                        rfl

theorem cell23_2291551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_2291551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291551 prefixEnd_2291551 := by exact prefixLift 2291551
  have htrace : WordTrace (prefixWord ++ tailWord_2291551) baseStart_2291551 baseEnd_2291551 := by
    simpa [prefixWord, tailWord_2291551, baseEnd_2291551] using wordTrace_append hprefix tailTrace_2291551
  have hstable : (prefixWord ++ tailWord_2291551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291551).length < 2 ^ (prefixWord ++ tailWord_2291551).sum := by decide
  have hdescent : baseEnd_2291551 < baseStart_2291551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291587 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 4, 5]
def baseStart_2291587 : Nat := 118140960795 + 2291587 * 2 ^ 59
def prefixEnd_2291587 : Nat := 4983230072969 + 3 ^ 40 * 2291587 * 2
def baseEnd_2291587 : Nat := 392228530864943629674563

theorem tailTrace_2291587 : CollatzResearch.WordTrace tailWord_2291587 prefixEnd_2291587 392228530864943629674563 := by
  unfold tailWord_2291587
  simp only [CollatzResearch.WordTrace]
  refine ⟨83581044348979145746001015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55720696232652763830667343 83581044348979145746001015)
  ·
    refine ⟨125371566523468718619001523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83581044348979145746001015 125371566523468718619001523)
    ·
      refine ⟨188057349785203077928502285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125371566523468718619001523 188057349785203077928502285)
      ·
        refine ⟨70521506169451154223188357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188057349785203077928502285 70521506169451154223188357)
        ·
          refine ⟨13222782406772091416847817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70521506169451154223188357 13222782406772091416847817)
          ·
            refine ⟨9917086805079068562635863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13222782406772091416847817 9917086805079068562635863)
            ·
              refine ⟨14875630207618602843953795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9917086805079068562635863 14875630207618602843953795)
              ·
                refine ⟨22313445311427904265930693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14875630207618602843953795 22313445311427904265930693)
                ·
                  refine ⟨4183770995892732049862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22313445311427904265930693 4183770995892732049862005)
                  ·
                    refine ⟨392228530864943629674563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4183770995892732049862005 392228530864943629674563)
                    ·
                      rfl

theorem cell23_2291587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].length) (baseStart_2291587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291587 prefixEnd_2291587 := by exact prefixLift 2291587
  have htrace : WordTrace (prefixWord ++ tailWord_2291587) baseStart_2291587 baseEnd_2291587 := by
    simpa [prefixWord, tailWord_2291587, baseEnd_2291587] using wordTrace_append hprefix tailTrace_2291587
  have hstable : (prefixWord ++ tailWord_2291587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291587).length < 2 ^ (prefixWord ++ tailWord_2291587).sum := by decide
  have hdescent : baseEnd_2291587 < baseStart_2291587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291591 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 7]
def baseStart_2291591 : Nat := 118140960795 + 2291591 * 2 ^ 59
def prefixEnd_2291591 : Nat := 4983230072969 + 3 ^ 40 * 2291591 * 2
def baseEnd_2291591 : Nat := 130743071835272097041519

theorem tailTrace_2291591 : CollatzResearch.WordTrace tailWord_2291591 prefixEnd_2291591 130743071835272097041519 := by
  unfold tailWord_2291591
  simp only [CollatzResearch.WordTrace]
  refine ⟨83581190240964654429146627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55720793493976436286097751 83581190240964654429146627)
  ·
    refine ⟨125371785361446981643719941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83581190240964654429146627 125371785361446981643719941)
    ·
      refine ⟨23507209755271309058197489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125371785361446981643719941 23507209755271309058197489)
      ·
        refine ⟨17630407316453481793648117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23507209755271309058197489 17630407316453481793648117)
        ·
          refine ⟨1652850685917513918154511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17630407316453481793648117 1652850685917513918154511)
          ·
            refine ⟨2479276028876270877231767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652850685917513918154511 2479276028876270877231767)
            ·
              refine ⟨3718914043314406315847651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479276028876270877231767 3718914043314406315847651)
              ·
                refine ⟨5578371064971609473771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718914043314406315847651 5578371064971609473771477)
                ·
                  refine ⟨130743071835272097041519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5578371064971609473771477 130743071835272097041519)
                  ·
                    rfl

theorem cell23_2291591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 7].length) (baseStart_2291591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291591 prefixEnd_2291591 := by exact prefixLift 2291591
  have htrace : WordTrace (prefixWord ++ tailWord_2291591) baseStart_2291591 baseEnd_2291591 := by
    simpa [prefixWord, tailWord_2291591, baseEnd_2291591] using wordTrace_append hprefix tailTrace_2291591
  have hstable : (prefixWord ++ tailWord_2291591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291591).length < 2 ^ (prefixWord ++ tailWord_2291591).sum := by decide
  have hdescent : baseEnd_2291591 < baseStart_2291591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291602 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2291602 : Nat := 118140960795 + 2291602 * 2 ^ 59
def prefixEnd_2291602 : Nat := 4983230072969 + 3 ^ 40 * 2291602 * 2
def baseEnd_2291602 : Nat := 1176693294804648330336121

theorem tailTrace_2291602 : CollatzResearch.WordTrace tailWord_2291602 prefixEnd_2291602 1176693294804648330336121 := by
  unfold tailWord_2291602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895397860981200826949265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55721060962616535538531373 20895397860981200826949265)
  ·
    refine ⟨15671548395735900620211949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20895397860981200826949265 15671548395735900620211949)
    ·
      refine ⟨5876830648400962732579481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15671548395735900620211949 5876830648400962732579481)
      ·
        refine ⟨4407622986300722049434611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5876830648400962732579481 4407622986300722049434611)
        ·
          refine ⟨6611434479451083074151917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407622986300722049434611 6611434479451083074151917)
          ·
            refine ⟨2479287929794156152806969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6611434479451083074151917 2479287929794156152806969)
            ·
              refine ⟨1859465947345617114605227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479287929794156152806969 1859465947345617114605227)
              ·
                refine ⟨2789198921018425671907841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859465947345617114605227 2789198921018425671907841)
                ·
                  refine ⟨2091899190763819253930881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789198921018425671907841 2091899190763819253930881)
                  ·
                    refine ⟨1568924393072864440448161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091899190763819253930881 1568924393072864440448161)
                    ·
                      refine ⟨1176693294804648330336121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1568924393072864440448161 1176693294804648330336121)
                      ·
                        rfl

theorem cell23_2291602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2291602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291602 prefixEnd_2291602 := by exact prefixLift 2291602
  have htrace : WordTrace (prefixWord ++ tailWord_2291602) baseStart_2291602 baseEnd_2291602 := by
    simpa [prefixWord, tailWord_2291602, baseEnd_2291602] using wordTrace_append hprefix tailTrace_2291602
  have hstable : (prefixWord ++ tailWord_2291602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291602).length < 2 ^ (prefixWord ++ tailWord_2291602).sum := by decide
  have hdescent : baseEnd_2291602 < baseStart_2291602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291707 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 6]
def baseStart_2291707 : Nat := 118140960795 + 2291707 * 2 ^ 59
def prefixEnd_2291707 : Nat := 4983230072969 + 3 ^ 40 * 2291707 * 2
def baseEnd_2291707 : Nat := 392249070091123473174379

theorem tailTrace_2291707 : CollatzResearch.WordTrace tailWord_2291707 prefixEnd_2291707 392249070091123473174379 := by
  unfold tailWord_2291707
  simp only [CollatzResearch.WordTrace]
  refine ⟨83585421108544406240369375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55723614072362937493579583 83585421108544406240369375)
  ·
    refine ⟨125378131662816609360554063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83585421108544406240369375 125378131662816609360554063)
    ·
      refine ⟨188067197494224914040831095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125378131662816609360554063 188067197494224914040831095)
      ·
        refine ⟨282100796241337371061246643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188067197494224914040831095 282100796241337371061246643)
        ·
          refine ⟨423151194362006056591869965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282100796241337371061246643 423151194362006056591869965)
          ·
            refine ⟨158681697885752271221951237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423151194362006056591869965 158681697885752271221951237)
            ·
              refine ⟨29752818353578550854115857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158681697885752271221951237 29752818353578550854115857)
              ·
                refine ⟨22314613765183913140586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29752818353578550854115857 22314613765183913140586893)
                ·
                  refine ⟨8367980161943967427720085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22314613765183913140586893 8367980161943967427720085)
                  ·
                    refine ⟨392249070091123473174379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8367980161943967427720085 392249070091123473174379)
                    ·
                      rfl

theorem cell23_2291707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_2291707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291707 prefixEnd_2291707 := by exact prefixLift 2291707
  have htrace : WordTrace (prefixWord ++ tailWord_2291707) baseStart_2291707 baseEnd_2291707 := by
    simpa [prefixWord, tailWord_2291707, baseEnd_2291707] using wordTrace_append hprefix tailTrace_2291707
  have hstable : (prefixWord ++ tailWord_2291707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291707).length < 2 ^ (prefixWord ++ tailWord_2291707).sum := by decide
  have hdescent : baseEnd_2291707 < baseStart_2291707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291708 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_2291708 : Nat := 118140960795 + 2291708 * 2 ^ 59
def prefixEnd_2291708 : Nat := 4983230072969 + 3 ^ 40 * 2291708 * 2
def baseEnd_2291708 : Nat := 1176747723754024915610633

theorem tailTrace_2291708 : CollatzResearch.WordTrace tailWord_2291708 prefixEnd_2291708 1176747723754024915610633 := by
  unfold tailWord_2291708
  simp only [CollatzResearch.WordTrace]
  refine ⟨41792728790770391705577889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55723638387693855607437185 41792728790770391705577889)
  ·
    refine ⟨31344546593077793779183417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41792728790770391705577889 31344546593077793779183417)
    ·
      refine ⟨23508409944808345334387563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31344546593077793779183417 23508409944808345334387563)
      ·
        refine ⟨35262614917212518001581345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23508409944808345334387563 35262614917212518001581345)
        ·
          refine ⟨26446961187909388501186009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35262614917212518001581345 26446961187909388501186009)
          ·
            refine ⟨19835220890932041375889507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26446961187909388501186009 19835220890932041375889507)
            ·
              refine ⟨29752831336398062063834261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19835220890932041375889507 29752831336398062063834261)
              ·
                refine ⟨1394663968893659159242231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29752831336398062063834261 1394663968893659159242231)
                ·
                  refine ⟨2091995953340488738863347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394663968893659159242231 2091995953340488738863347)
                  ·
                    refine ⟨3137993930010733108295021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091995953340488738863347 3137993930010733108295021)
                    ·
                      refine ⟨1176747723754024915610633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3137993930010733108295021 1176747723754024915610633)
                      ·
                        rfl

theorem cell23_2291708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_2291708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291708 prefixEnd_2291708 := by exact prefixLift 2291708
  have htrace : WordTrace (prefixWord ++ tailWord_2291708) baseStart_2291708 baseEnd_2291708 := by
    simpa [prefixWord, tailWord_2291708, baseEnd_2291708] using wordTrace_append hprefix tailTrace_2291708
  have hstable : (prefixWord ++ tailWord_2291708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291708).length < 2 ^ (prefixWord ++ tailWord_2291708).sum := by decide
  have hdescent : baseEnd_2291708 < baseStart_2291708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291741 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2291741 : Nat := 118140960795 + 2291741 * 2 ^ 59
def prefixEnd_2291741 : Nat := 4983230072969 + 3 ^ 40 * 2291741 * 2
def baseEnd_2291741 : Nat := 392254889538541095499327

theorem tailTrace_2291741 : CollatzResearch.WordTrace tailWord_2291741 prefixEnd_2291741 392254889538541095499327 := by
  unfold tailWord_2291741
  simp only [CollatzResearch.WordTrace]
  refine ⟨83586661190421230047107077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55724440793614153364738051 83586661190421230047107077)
  ·
    refine ⟨15672498973203980633832577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83586661190421230047107077 15672498973203980633832577)
    ·
      refine ⟨11754374229902985475374433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15672498973203980633832577 11754374229902985475374433)
      ·
        refine ⟨8815780672427239106530825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11754374229902985475374433 8815780672427239106530825)
        ·
          refine ⟨6611835504320429329898119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8815780672427239106530825 6611835504320429329898119)
          ·
            refine ⟨9917753256480643994847179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611835504320429329898119 9917753256480643994847179)
            ·
              refine ⟨14876629884720965992270769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9917753256480643994847179 14876629884720965992270769)
              ·
                refine ⟨11157472413540724494203077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14876629884720965992270769 11157472413540724494203077)
                ·
                  refine ⟨2092026077538885842663077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11157472413540724494203077 2092026077538885842663077)
                  ·
                    refine ⟨392254889538541095499327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092026077538885842663077 392254889538541095499327)
                    ·
                      rfl

theorem cell23_2291741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2291741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291741 prefixEnd_2291741 := by exact prefixLift 2291741
  have htrace : WordTrace (prefixWord ++ tailWord_2291741) baseStart_2291741 baseEnd_2291741 := by
    simpa [prefixWord, tailWord_2291741, baseEnd_2291741] using wordTrace_append hprefix tailTrace_2291741
  have hstable : (prefixWord ++ tailWord_2291741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291741).length < 2 ^ (prefixWord ++ tailWord_2291741).sum := by decide
  have hdescent : baseEnd_2291741 < baseStart_2291741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291754 : List Nat := [3, 1, 4, 1, 2, 1, 11]
def baseStart_2291754 : Nat := 118140960795 + 2291754 * 2 ^ 59
def prefixEnd_2291754 : Nat := 4983230072969 + 3 ^ 40 * 2291754 * 2
def baseEnd_2291754 : Nat := 14528041282273231304141

theorem tailTrace_2291754 : CollatzResearch.WordTrace tailWord_2291754 prefixEnd_2291754 14528041282273231304141 := by
  unfold tailWord_2291754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20896783834843533316832579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55724756892916088844886877 20896783834843533316832579)
  ·
    refine ⟨31345175752265299975248869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20896783834843533316832579 31345175752265299975248869)
    ·
      refine ⟨5877220453549743745359163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31345175752265299975248869 5877220453549743745359163)
      ·
        refine ⟨8815830680324615618038745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5877220453549743745359163 8815830680324615618038745)
        ·
          refine ⟨6611873010243461713529059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8815830680324615618038745 6611873010243461713529059)
          ·
            refine ⟨9917809515365192570293589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611873010243461713529059 9917809515365192570293589)
            ·
              refine ⟨14528041282273231304141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9917809515365192570293589 14528041282273231304141)
              ·
                rfl

theorem cell23_2291754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 11].length) (baseStart_2291754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291754 prefixEnd_2291754 := by exact prefixLift 2291754
  have htrace : WordTrace (prefixWord ++ tailWord_2291754) baseStart_2291754 baseEnd_2291754 := by
    simpa [prefixWord, tailWord_2291754, baseEnd_2291754] using wordTrace_append hprefix tailTrace_2291754
  have hstable : (prefixWord ++ tailWord_2291754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291754).length < 2 ^ (prefixWord ++ tailWord_2291754).sum := by decide
  have hdescent : baseEnd_2291754 < baseStart_2291754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291765 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_2291765 : Nat := 118140960795 + 2291765 * 2 ^ 59
def prefixEnd_2291765 : Nat := 4983230072969 + 3 ^ 40 * 2291765 * 2
def baseEnd_2291765 : Nat := 1176776992151331192597871

theorem tailTrace_2291765 : CollatzResearch.WordTrace tailWord_2291765 prefixEnd_2291765 1176776992151331192597871 := by
  unfold tailWord_2291765
  simp only [CollatzResearch.WordTrace]
  refine ⟨83587536542334282145980749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55725024361556188097320499 83587536542334282145980749)
  ·
    refine ⟨31345326203375355804742781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83587536542334282145980749 31345326203375355804742781)
    ·
      refine ⟨11754497326265758426778543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31345326203375355804742781 11754497326265758426778543)
      ·
        refine ⟨17631745989398637640167815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11754497326265758426778543 17631745989398637640167815)
        ·
          refine ⟨26447618984097956460251723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17631745989398637640167815 26447618984097956460251723)
          ·
            refine ⟨39671428476146934690377585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26447618984097956460251723 39671428476146934690377585)
            ·
              refine ⟨29753571357110201017783189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39671428476146934690377585 29753571357110201017783189)
              ·
                refine ⟨1394698657364540672708587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29753571357110201017783189 1394698657364540672708587)
                ·
                  refine ⟨2092047986046811009062881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394698657364540672708587 2092047986046811009062881)
                  ·
                    refine ⟨1569035989535108256797161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092047986046811009062881 1569035989535108256797161)
                    ·
                      refine ⟨1176776992151331192597871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569035989535108256797161 1176776992151331192597871)
                      ·
                        rfl

theorem cell23_2291765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_2291765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291765 prefixEnd_2291765 := by exact prefixLift 2291765
  have htrace : WordTrace (prefixWord ++ tailWord_2291765) baseStart_2291765 baseEnd_2291765 := by
    simpa [prefixWord, tailWord_2291765, baseEnd_2291765] using wordTrace_append hprefix tailTrace_2291765
  have hstable : (prefixWord ++ tailWord_2291765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291765).length < 2 ^ (prefixWord ++ tailWord_2291765).sum := by decide
  have hdescent : baseEnd_2291765 < baseStart_2291765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 3, 3, 2]
def baseStart_2291791 : Nat := 118140960795 + 2291791 * 2 ^ 59
def prefixEnd_2291791 : Nat := 4983230072969 + 3 ^ 40 * 2291791 * 2
def baseEnd_2291791 : Nat := 1176790342648348090872751

theorem tailTrace_2291791 : CollatzResearch.WordTrace tailWord_2291791 prefixEnd_2291791 1176790342648348090872751 := by
  unfold tailWord_2291791
  simp only [CollatzResearch.WordTrace]
  refine ⟨83588484840240088586427227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55725656560160059057618151 83588484840240088586427227)
  ·
    refine ⟨125382727260360132879640841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83588484840240088586427227 125382727260360132879640841)
    ·
      refine ⟨94037045445270099659730631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125382727260360132879640841 94037045445270099659730631)
      ·
        refine ⟨141055568167905149489595947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94037045445270099659730631 141055568167905149489595947)
        ·
          refine ⟨211583352251857724234393921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141055568167905149489595947 211583352251857724234393921)
          ·
            refine ⟨158687514188893293175795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211583352251857724234393921 158687514188893293175795441)
            ·
              refine ⟨119015635641669969881846581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158687514188893293175795441 119015635641669969881846581)
              ·
                refine ⟨11157715841406559676423117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119015635641669969881846581 11157715841406559676423117)
                ·
                  refine ⟨4184143440527459878658669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11157715841406559676423117 4184143440527459878658669)
                  ·
                    refine ⟨1569053790197797454497001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4184143440527459878658669 1569053790197797454497001)
                    ·
                      refine ⟨1176790342648348090872751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569053790197797454497001 1176790342648348090872751)
                      ·
                        rfl

theorem cell23_2291791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3, 2].length) (baseStart_2291791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291791 prefixEnd_2291791 := by exact prefixLift 2291791
  have htrace : WordTrace (prefixWord ++ tailWord_2291791) baseStart_2291791 baseEnd_2291791 := by
    simpa [prefixWord, tailWord_2291791, baseEnd_2291791] using wordTrace_append hprefix tailTrace_2291791
  have hstable : (prefixWord ++ tailWord_2291791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291791).length < 2 ^ (prefixWord ++ tailWord_2291791).sum := by decide
  have hdescent : baseEnd_2291791 < baseStart_2291791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291872 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2]
def baseStart_2291872 : Nat := 118140960795 + 2291872 * 2 ^ 59
def prefixEnd_2291872 : Nat := 4983230072969 + 3 ^ 40 * 2291872 * 2
def baseEnd_2291872 : Nat := 1176831934581362273959879

theorem tailTrace_2291872 : CollatzResearch.WordTrace tailWord_2291872 prefixEnd_2291872 1176831934581362273959879 := by
  unfold tailWord_2291872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41795719576473319710062935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55727626101964426280083913 41795719576473319710062935)
  ·
    refine ⟨62693579364709979565094403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41795719576473319710062935 62693579364709979565094403)
    ·
      refine ⟨94040369047064969347641605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62693579364709979565094403 94040369047064969347641605)
      ·
        refine ⟨17632569196324681752682801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94040369047064969347641605 17632569196324681752682801)
        ·
          refine ⟨13224426897243511314512101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17632569196324681752682801 13224426897243511314512101)
          ·
            refine ⟨2479580043233158371471019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13224426897243511314512101 2479580043233158371471019)
            ·
              refine ⟨3719370064849737557206529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479580043233158371471019 3719370064849737557206529)
              ·
                refine ⟨2789527548637303167904897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719370064849737557206529 2789527548637303167904897)
                ·
                  refine ⟨2092145661477977375928673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789527548637303167904897 2092145661477977375928673)
                  ·
                    refine ⟨1569109246108483031946505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092145661477977375928673 1569109246108483031946505)
                    ·
                      refine ⟨1176831934581362273959879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569109246108483031946505 1176831934581362273959879)
                      ·
                        rfl

theorem cell23_2291872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_2291872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291872 prefixEnd_2291872 := by exact prefixLift 2291872
  have htrace : WordTrace (prefixWord ++ tailWord_2291872) baseStart_2291872 baseEnd_2291872 := by
    simpa [prefixWord, tailWord_2291872, baseEnd_2291872] using wordTrace_append hprefix tailTrace_2291872
  have hstable : (prefixWord ++ tailWord_2291872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291872).length < 2 ^ (prefixWord ++ tailWord_2291872).sum := by decide
  have hdescent : baseEnd_2291872 < baseStart_2291872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291884 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2291884 : Nat := 118140960795 + 2291884 * 2 ^ 59
def prefixEnd_2291884 : Nat := 4983230072969 + 3 ^ 40 * 2291884 * 2
def baseEnd_2291884 : Nat := 1176838096349216227009823

theorem tailTrace_2291884 : CollatzResearch.WordTrace tailWord_2291884 prefixEnd_2291884 1176838096349216227009823 := by
  unfold tailWord_2291884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41795938414451582734781353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55727917885935443646375137 41795938414451582734781353)
  ·
    refine ⟨31346953810838687051086015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41795938414451582734781353 31346953810838687051086015)
    ·
      refine ⟨47020430716258030576629023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31346953810838687051086015 47020430716258030576629023)
      ·
        refine ⟨70530646074387045864943535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47020430716258030576629023 70530646074387045864943535)
        ·
          refine ⟨105795969111580568797415303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70530646074387045864943535 105795969111580568797415303)
          ·
            refine ⟨158693953667370853196122955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105795969111580568797415303 158693953667370853196122955)
            ·
              refine ⟨238040930501056279794184433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158693953667370853196122955 238040930501056279794184433)
              ·
                refine ⟨178530697875792209845638325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238040930501056279794184433 178530697875792209845638325)
                ·
                  refine ⟨16737252925855519673028593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178530697875792209845638325 16737252925855519673028593)
                  ·
                    refine ⟨12552939694391639754771445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16737252925855519673028593 12552939694391639754771445)
                    ·
                      refine ⟨1176838096349216227009823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12552939694391639754771445 1176838096349216227009823)
                      ·
                        rfl

theorem cell23_2291884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2291884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291884 prefixEnd_2291884 := by exact prefixLift 2291884
  have htrace : WordTrace (prefixWord ++ tailWord_2291884) baseStart_2291884 baseEnd_2291884 := by
    simpa [prefixWord, tailWord_2291884, baseEnd_2291884] using wordTrace_append hprefix tailTrace_2291884
  have hstable : (prefixWord ++ tailWord_2291884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291884).length < 2 ^ (prefixWord ++ tailWord_2291884).sum := by decide
  have hdescent : baseEnd_2291884 < baseStart_2291884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291889 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2291889 : Nat := 118140960795 + 2291889 * 2 ^ 59
def prefixEnd_2291889 : Nat := 4983230072969 + 3 ^ 40 * 2291889 * 2
def baseEnd_2291889 : Nat := 1176840663752488707447301

theorem tailTrace_2291889 : CollatzResearch.WordTrace tailWord_2291889 prefixEnd_2291889 1176840663752488707447301 := by
  unfold tailWord_2291889
  simp only [CollatzResearch.WordTrace]
  refine ⟨83592059193885051323494721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55728039462590034215663147 83592059193885051323494721)
  ·
    refine ⟨62694044395413788492621041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83592059193885051323494721 62694044395413788492621041)
    ·
      refine ⟨47020533296560341369465781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62694044395413788492621041 47020533296560341369465781)
      ·
        refine ⟨4408174996552532003387417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47020533296560341369465781 4408174996552532003387417)
        ·
          refine ⟨3306131247414399002540563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408174996552532003387417 3306131247414399002540563)
          ·
            refine ⟨4959196871121598503810845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306131247414399002540563 4959196871121598503810845)
            ·
              refine ⟨1859698826670599438929067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4959196871121598503810845 1859698826670599438929067)
              ·
                refine ⟨2789548240005899158393601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859698826670599438929067 2789548240005899158393601)
                ·
                  refine ⟨2092161180004424368795201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789548240005899158393601 2092161180004424368795201)
                  ·
                    refine ⟨1569120885003318276596401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092161180004424368795201 1569120885003318276596401)
                    ·
                      refine ⟨1176840663752488707447301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569120885003318276596401 1176840663752488707447301)
                      ·
                        rfl

theorem cell23_2291889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2291889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291889 prefixEnd_2291889 := by exact prefixLift 2291889
  have htrace : WordTrace (prefixWord ++ tailWord_2291889) baseStart_2291889 baseEnd_2291889 := by
    simpa [prefixWord, tailWord_2291889, baseEnd_2291889] using wordTrace_append hprefix tailTrace_2291889
  have hstable : (prefixWord ++ tailWord_2291889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291889).length < 2 ^ (prefixWord ++ tailWord_2291889).sum := by decide
  have hdescent : baseEnd_2291889 < baseStart_2291889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291921 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_2291921 : Nat := 118140960795 + 2291921 * 2 ^ 59
def prefixEnd_2291921 : Nat := 4983230072969 + 3 ^ 40 * 2291921 * 2
def baseEnd_2291921 : Nat := 392285698377810860749051

theorem tailTrace_2291921 : CollatzResearch.WordTrace tailWord_2291921 prefixEnd_2291921 392285698377810860749051 := by
  unfold tailWord_2291921
  simp only [CollatzResearch.WordTrace]
  refine ⟨83593226329769120788659617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55728817553179413859106411 83593226329769120788659617)
  ·
    refine ⟨62694919747326840591494713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83593226329769120788659617 62694919747326840591494713)
    ·
      refine ⟨47021189810495130443621035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62694919747326840591494713 47021189810495130443621035)
      ·
        refine ⟨70531784715742695665431553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47021189810495130443621035 70531784715742695665431553)
        ·
          refine ⟨52898838536807021749073665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70531784715742695665431553 52898838536807021749073665)
          ·
            refine ⟨39674128902605266311805249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52898838536807021749073665 39674128902605266311805249)
            ·
              refine ⟨29755596676953949733853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39674128902605266311805249 29755596676953949733853937)
              ·
                refine ⟨22316697507715462300390453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29755596676953949733853937 22316697507715462300390453)
                ·
                  refine ⟨2092190391348324590661605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22316697507715462300390453 2092190391348324590661605)
                  ·
                    refine ⟨392285698377810860749051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092190391348324590661605 392285698377810860749051)
                    ·
                      rfl

theorem cell23_2291921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_2291921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291921 prefixEnd_2291921 := by exact prefixLift 2291921
  have htrace : WordTrace (prefixWord ++ tailWord_2291921) baseStart_2291921 baseEnd_2291921 := by
    simpa [prefixWord, tailWord_2291921, baseEnd_2291921] using wordTrace_append hprefix tailTrace_2291921
  have hstable : (prefixWord ++ tailWord_2291921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291921).length < 2 ^ (prefixWord ++ tailWord_2291921).sum := by decide
  have hdescent : baseEnd_2291921 < baseStart_2291921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291928 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2291928 : Nat := 118140960795 + 2291928 * 2 ^ 59
def prefixEnd_2291928 : Nat := 4983230072969 + 3 ^ 40 * 2291928 * 2
def baseEnd_2291928 : Nat := 1176860689498014054859621

theorem tailTrace_2291928 : CollatzResearch.WordTrace tailWord_2291928 prefixEnd_2291928 1176860689498014054859621 := by
  unfold tailWord_2291928
  simp only [CollatzResearch.WordTrace]
  refine ⟨41796740820371880492082219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55728987760495840656109625 41796740820371880492082219)
  ·
    refine ⟨62695111230557820738123329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41796740820371880492082219 62695111230557820738123329)
    ·
      refine ⟨47021333422918365553592497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62695111230557820738123329 47021333422918365553592497)
      ·
        refine ⟨35266000067188774165194373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47021333422918365553592497 35266000067188774165194373)
        ·
          refine ⟨6612375012597895155973945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35266000067188774165194373 6612375012597895155973945)
          ·
            refine ⟨4959281259448421366980459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6612375012597895155973945 4959281259448421366980459)
            ·
              refine ⟨7438921889172632050470689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959281259448421366980459 7438921889172632050470689)
              ·
                refine ⟨5579191416879474037853017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7438921889172632050470689 5579191416879474037853017)
                ·
                  refine ⟨4184393562659605528389763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579191416879474037853017 4184393562659605528389763)
                  ·
                    refine ⟨6276590343989408292584645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184393562659605528389763 6276590343989408292584645)
                    ·
                      refine ⟨1176860689498014054859621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6276590343989408292584645 1176860689498014054859621)
                      ·
                        rfl

theorem cell23_2291928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2291928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291928 prefixEnd_2291928 := by exact prefixLift 2291928
  have htrace : WordTrace (prefixWord ++ tailWord_2291928) baseStart_2291928 baseEnd_2291928 := by
    simpa [prefixWord, tailWord_2291928, baseEnd_2291928] using wordTrace_append hprefix tailTrace_2291928
  have hstable : (prefixWord ++ tailWord_2291928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291928).length < 2 ^ (prefixWord ++ tailWord_2291928).sum := by decide
  have hdescent : baseEnd_2291928 < baseStart_2291928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3]
def baseStart_2291931 : Nat := 118140960795 + 2291931 * 2 ^ 59
def prefixEnd_2291931 : Nat := 4983230072969 + 3 ^ 40 * 2291931 * 2
def baseEnd_2291931 : Nat := 1176862229939977543122107

theorem tailTrace_2291931 : CollatzResearch.WordTrace tailWord_2291931 prefixEnd_2291931 1176862229939977543122107 := by
  unfold tailWord_2291931
  simp only [CollatzResearch.WordTrace]
  refine ⟨83593591059732892496523647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55729060706488594997682431 83593591059732892496523647)
  ·
    refine ⟨125390386589599338744785471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83593591059732892496523647 125390386589599338744785471)
    ·
      refine ⟨188085579884399008117178207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125390386589599338744785471 188085579884399008117178207)
      ·
        refine ⟨282128369826598512175767311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188085579884399008117178207 282128369826598512175767311)
        ·
          refine ⟨423192554739897768263650967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282128369826598512175767311 423192554739897768263650967)
          ·
            refine ⟨634788832109846652395476451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423192554739897768263650967 634788832109846652395476451)
            ·
              refine ⟨952183248164769978593214677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634788832109846652395476451 952183248164769978593214677)
              ·
                refine ⟨22316794878861796373278469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 952183248164769978593214677 22316794878861796373278469)
                ·
                  refine ⟨4184399039786586819989713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22316794878861796373278469 4184399039786586819989713)
                  ·
                    refine ⟨3138299279839940114992285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184399039786586819989713 3138299279839940114992285)
                    ·
                      refine ⟨1176862229939977543122107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3138299279839940114992285 1176862229939977543122107)
                      ·
                        rfl

theorem cell23_2291931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].length) (baseStart_2291931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2291931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2291931 prefixEnd_2291931 := by exact prefixLift 2291931
  have htrace : WordTrace (prefixWord ++ tailWord_2291931) baseStart_2291931 baseEnd_2291931 := by
    simpa [prefixWord, tailWord_2291931, baseEnd_2291931] using wordTrace_append hprefix tailTrace_2291931
  have hstable : (prefixWord ++ tailWord_2291931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291931).length < 2 ^ (prefixWord ++ tailWord_2291931).sum := by decide
  have hdescent : baseEnd_2291931 < baseStart_2291931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292028 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_2292028 : Nat := 118140960795 + 2292028 * 2 ^ 59
def prefixEnd_2292028 : Nat := 4983230072969 + 3 ^ 40 * 2292028 * 2
def baseEnd_2292028 : Nat := 392304012521154554536387

theorem tailTrace_2292028 : CollatzResearch.WordTrace tailWord_2292028 prefixEnd_2292028 392304012521154554536387 := by
  unfold tailWord_2292028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41798564470190739031402369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55731419293587652041869825 41798564470190739031402369)
  ·
    refine ⟨31348923352643054273551777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41798564470190739031402369 31348923352643054273551777)
    ·
      refine ⟨23511692514482290705163833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31348923352643054273551777 23511692514482290705163833)
      ·
        refine ⟨17633769385861718028872875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23511692514482290705163833 17633769385861718028872875)
        ·
          refine ⟨26450654078792577043309313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17633769385861718028872875 26450654078792577043309313)
          ·
            refine ⟨19837990559094432782481985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26450654078792577043309313 19837990559094432782481985)
            ·
              refine ⟨14878492919320824586861489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19837990559094432782481985 14878492919320824586861489)
              ·
                refine ⟨11158869689490618440146117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14878492919320824586861489 11158869689490618440146117)
                ·
                  refine ⟨2092288066779490957527397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11158869689490618440146117 2092288066779490957527397)
                  ·
                    refine ⟨392304012521154554536387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092288066779490957527397 392304012521154554536387)
                    ·
                      rfl

theorem cell23_2292028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_2292028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292028 prefixEnd_2292028 := by exact prefixLift 2292028
  have htrace : WordTrace (prefixWord ++ tailWord_2292028) baseStart_2292028 baseEnd_2292028 := by
    simpa [prefixWord, tailWord_2292028, baseEnd_2292028] using wordTrace_append hprefix tailTrace_2292028
  have hstable : (prefixWord ++ tailWord_2292028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292028).length < 2 ^ (prefixWord ++ tailWord_2292028).sum := by decide
  have hdescent : baseEnd_2292028 < baseStart_2292028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292035 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 1, 1, 4]
def baseStart_2292035 : Nat := 118140960795 + 2292035 * 2 ^ 59
def prefixEnd_2292035 : Nat := 4983230072969 + 3 ^ 40 * 2292035 * 2
def baseEnd_2292035 : Nat := 1176915631928045136221629

theorem tailTrace_2292035 : CollatzResearch.WordTrace tailWord_2292035 prefixEnd_2292035 1176915631928045136221629 := by
  unfold tailWord_2292035
  simp only [CollatzResearch.WordTrace]
  refine ⟨83597384251356118258309559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55731589500904078838873039 83597384251356118258309559)
  ·
    refine ⟨125396076377034177387464339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83597384251356118258309559 125396076377034177387464339)
    ·
      refine ⟨188094114565551266081196509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125396076377034177387464339 188094114565551266081196509)
      ·
        refine ⟨70535292962081724780448691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188094114565551266081196509 70535292962081724780448691)
        ·
          refine ⟨105802939443122587170673037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70535292962081724780448691 105802939443122587170673037)
          ·
            refine ⟨39676102291170970189002389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105802939443122587170673037 39676102291170970189002389)
            ·
              refine ⟨1859817294898639227609487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39676102291170970189002389 1859817294898639227609487)
              ·
                refine ⟨2789725942347958841414231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859817294898639227609487 2789725942347958841414231)
                ·
                  refine ⟨4184588913521938262121347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789725942347958841414231 4184588913521938262121347)
                  ·
                    refine ⟨6276883370282907393182021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184588913521938262121347 6276883370282907393182021)
                    ·
                      refine ⟨1176915631928045136221629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6276883370282907393182021 1176915631928045136221629)
                      ·
                        rfl

theorem cell23_2292035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_2292035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292035 prefixEnd_2292035 := by exact prefixLift 2292035
  have htrace : WordTrace (prefixWord ++ tailWord_2292035) baseStart_2292035 baseEnd_2292035 := by
    simpa [prefixWord, tailWord_2292035, baseEnd_2292035] using wordTrace_append hprefix tailTrace_2292035
  have hstable : (prefixWord ++ tailWord_2292035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292035).length < 2 ^ (prefixWord ++ tailWord_2292035).sum := by decide
  have hdescent : baseEnd_2292035 < baseStart_2292035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292052 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_2292052 : Nat := 118140960795 + 2292052 * 2 ^ 59
def prefixEnd_2292052 : Nat := 4983230072969 + 3 ^ 40 * 2292052 * 2
def baseEnd_2292052 : Nat := 1176924361099171569709051

theorem tailTrace_2292052 : CollatzResearch.WordTrace tailWord_2292052 prefixEnd_2292052 1176924361099171569709051 := by
  unfold tailWord_2292052
  simp only [CollatzResearch.WordTrace]
  refine ⟨41799002146147265080839205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55732002861529686774452273 41799002146147265080839205)
  ·
    refine ⟨7837312902402612202657351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41799002146147265080839205 7837312902402612202657351)
    ·
      refine ⟨11755969353603918303986027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837312902402612202657351 11755969353603918303986027)
      ·
        refine ⟨17633954030405877455979041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11755969353603918303986027 17633954030405877455979041)
        ·
          refine ⟨13225465522804408091984281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17633954030405877455979041 13225465522804408091984281)
          ·
            refine ⟨9919099142103306068988211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13225465522804408091984281 9919099142103306068988211)
            ·
              refine ⟨14878648713154959103482317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919099142103306068988211 14878648713154959103482317)
              ·
                refine ⟨5579493267433109663805869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14878648713154959103482317 5579493267433109663805869)
                ·
                  refine ⟨2092309975287416123927201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5579493267433109663805869 2092309975287416123927201)
                  ·
                    refine ⟨1569232481465562092945401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092309975287416123927201 1569232481465562092945401)
                    ·
                      refine ⟨1176924361099171569709051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569232481465562092945401 1176924361099171569709051)
                      ·
                        rfl

theorem cell23_2292052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_2292052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292052 prefixEnd_2292052 := by exact prefixLift 2292052
  have htrace : WordTrace (prefixWord ++ tailWord_2292052) baseStart_2292052 baseEnd_2292052 := by
    simpa [prefixWord, tailWord_2292052, baseEnd_2292052] using wordTrace_append hprefix tailTrace_2292052
  have hstable : (prefixWord ++ tailWord_2292052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292052).length < 2 ^ (prefixWord ++ tailWord_2292052).sum := by decide
  have hdescent : baseEnd_2292052 < baseStart_2292052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292072 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2292072 : Nat := 118140960795 + 2292072 * 2 ^ 59
def prefixEnd_2292072 : Nat := 4983230072969 + 3 ^ 40 * 2292072 * 2
def baseEnd_2292072 : Nat := 1176934630712261491458959

theorem tailTrace_2292072 : CollatzResearch.WordTrace tailWord_2292072 prefixEnd_2292072 1176934630712261491458959 := by
  unfold tailWord_2292072
  simp only [CollatzResearch.WordTrace]
  refine ⟨41799366876111036788703235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55732489168148049051604313 41799366876111036788703235)
  ·
    refine ⟨62699050314166555183054853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41799366876111036788703235 62699050314166555183054853)
    ·
      refine ⟨11756071933906229096822785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62699050314166555183054853 11756071933906229096822785)
      ·
        refine ⟨8817053950429671822617089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11756071933906229096822785 8817053950429671822617089)
        ·
          refine ⟨6612790462822253866962817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8817053950429671822617089 6612790462822253866962817)
          ·
            refine ⟨4959592847116690400222113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6612790462822253866962817 4959592847116690400222113)
            ·
              refine ⟨3719694635337517800166585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959592847116690400222113 3719694635337517800166585)
              ·
                refine ⟨2789770976503138350124939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719694635337517800166585 2789770976503138350124939)
                ·
                  refine ⟨4184656464754707525187409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789770976503138350124939 4184656464754707525187409)
                  ·
                    refine ⟨3138492348566030643890557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184656464754707525187409 3138492348566030643890557)
                    ·
                      refine ⟨1176934630712261491458959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3138492348566030643890557 1176934630712261491458959)
                      ·
                        rfl

theorem cell23_2292072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2292072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292072 prefixEnd_2292072 := by exact prefixLift 2292072
  have htrace : WordTrace (prefixWord ++ tailWord_2292072) baseStart_2292072 baseEnd_2292072 := by
    simpa [prefixWord, tailWord_2292072, baseEnd_2292072] using wordTrace_append hprefix tailTrace_2292072
  have hstable : (prefixWord ++ tailWord_2292072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292072).length < 2 ^ (prefixWord ++ tailWord_2292072).sum := by decide
  have hdescent : baseEnd_2292072 < baseStart_2292072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292128 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2292128 : Nat := 118140960795 + 2292128 * 2 ^ 59
def prefixEnd_2292128 : Nat := 4983230072969 + 3 ^ 40 * 2292128 * 2
def baseEnd_2292128 : Nat := 1176963385628913272358701

theorem tailTrace_2292128 : CollatzResearch.WordTrace tailWord_2292128 prefixEnd_2292128 1176963385628913272358701 := by
  unfold tailWord_2292128
  simp only [CollatzResearch.WordTrace]
  refine ⟨41800388120009597570722519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55733850826679463427630025 41800388120009597570722519)
  ·
    refine ⟨62700582180014396356083779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41800388120009597570722519 62700582180014396356083779)
    ·
      refine ⟨94050873270021594534125669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62700582180014396356083779 94050873270021594534125669)
      ·
        refine ⟨17634538738129048975148563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94050873270021594534125669 17634538738129048975148563)
        ·
          refine ⟨26451808107193573462722845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17634538738129048975148563 26451808107193573462722845)
          ·
            refine ⟨9919428040197590048521067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26451808107193573462722845 9919428040197590048521067)
            ·
              refine ⟨14879142060296385072781601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919428040197590048521067 14879142060296385072781601)
              ·
                refine ⟨11159356545222288804586201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14879142060296385072781601 11159356545222288804586201)
                ·
                  refine ⟨8369517408916716603439651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11159356545222288804586201 8369517408916716603439651)
                  ·
                    refine ⟨12554276113375074905159477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8369517408916716603439651 12554276113375074905159477)
                    ·
                      refine ⟨1176963385628913272358701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12554276113375074905159477 1176963385628913272358701)
                      ·
                        rfl

theorem cell23_2292128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2292128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292128 prefixEnd_2292128 := by exact prefixLift 2292128
  have htrace : WordTrace (prefixWord ++ tailWord_2292128) baseStart_2292128 baseEnd_2292128 := by
    simpa [prefixWord, tailWord_2292128, baseEnd_2292128] using wordTrace_append hprefix tailTrace_2292128
  have hstable : (prefixWord ++ tailWord_2292128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292128).length < 2 ^ (prefixWord ++ tailWord_2292128).sum := by decide
  have hdescent : baseEnd_2292128 < baseStart_2292128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292129 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2292129 : Nat := 118140960795 + 2292129 * 2 ^ 59
def prefixEnd_2292129 : Nat := 4983230072969 + 3 ^ 40 * 2292129 * 2
def baseEnd_2292129 : Nat := 1176963899109567768446197

theorem tailTrace_2292129 : CollatzResearch.WordTrace tailWord_2292129 prefixEnd_2292129 1176963899109567768446197 := by
  unfold tailWord_2292129
  simp only [CollatzResearch.WordTrace]
  refine ⟨83600812713015572312231441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55733875142010381541487627 83600812713015572312231441)
  ·
    refine ⟨62700609534761679234173581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83600812713015572312231441 62700609534761679234173581)
    ·
      refine ⟨23512728575535629712815093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62700609534761679234173581 23512728575535629712815093)
      ·
        refine ⟨2204318303956465285576415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23512728575535629712815093 2204318303956465285576415)
        ·
          refine ⟨3306477455934697928364623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204318303956465285576415 3306477455934697928364623)
          ·
            refine ⟨4959716183902046892546935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306477455934697928364623 4959716183902046892546935)
            ·
              refine ⟨7439574275853070338820403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959716183902046892546935 7439574275853070338820403)
              ·
                refine ⟨11159361413779605508230605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439574275853070338820403 11159361413779605508230605)
                ·
                  refine ⟨4184760530167352065586477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11159361413779605508230605 4184760530167352065586477)
                  ·
                    refine ⟨1569285198812757024594929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4184760530167352065586477 1569285198812757024594929)
                    ·
                      refine ⟨1176963899109567768446197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569285198812757024594929 1176963899109567768446197)
                      ·
                        rfl

theorem cell23_2292129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2292129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292129 prefixEnd_2292129 := by exact prefixLift 2292129
  have htrace : WordTrace (prefixWord ++ tailWord_2292129) baseStart_2292129 baseEnd_2292129 := by
    simpa [prefixWord, tailWord_2292129, baseEnd_2292129] using wordTrace_append hprefix tailTrace_2292129
  have hstable : (prefixWord ++ tailWord_2292129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292129).length < 2 ^ (prefixWord ++ tailWord_2292129).sum := by decide
  have hdescent : baseEnd_2292129 < baseStart_2292129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292158 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2292158 : Nat := 118140960795 + 2292158 * 2 ^ 59
def prefixEnd_2292158 : Nat := 4983230072969 + 3 ^ 40 * 2292158 * 2
def baseEnd_2292158 : Nat := 1176978790048548154983563

theorem tailTrace_2292158 : CollatzResearch.WordTrace tailWord_2292158 prefixEnd_2292158 1176978790048548154983563 := by
  unfold tailWord_2292158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450233803738813783129641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55734580286607006843358085 10450233803738813783129641)
  ·
    refine ⟨7837675352804110337347231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10450233803738813783129641 7837675352804110337347231)
    ·
      refine ⟨11756513029206165506020847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837675352804110337347231 11756513029206165506020847)
      ·
        refine ⟨17634769543809248259031271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11756513029206165506020847 17634769543809248259031271)
        ·
          refine ⟨26452154315713872388546907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17634769543809248259031271 26452154315713872388546907)
          ·
            refine ⟨39678231473570808582820361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452154315713872388546907 39678231473570808582820361)
            ·
              refine ⟨29758673605178106437115271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39678231473570808582820361 29758673605178106437115271)
              ·
                refine ⟨44638010407767159655672907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29758673605178106437115271 44638010407767159655672907)
                ·
                  refine ⟨66957015611650739483509361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44638010407767159655672907 66957015611650739483509361)
                  ·
                    refine ⟨50217761708738054612632021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66957015611650739483509361 50217761708738054612632021)
                    ·
                      refine ⟨1176978790048548154983563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50217761708738054612632021 1176978790048548154983563)
                      ·
                        rfl

theorem cell23_2292158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2292158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292158 prefixEnd_2292158 := by exact prefixLift 2292158
  have htrace : WordTrace (prefixWord ++ tailWord_2292158) baseStart_2292158 baseEnd_2292158 := by
    simpa [prefixWord, tailWord_2292158, baseEnd_2292158] using wordTrace_append hprefix tailTrace_2292158
  have hstable : (prefixWord ++ tailWord_2292158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292158).length < 2 ^ (prefixWord ++ tailWord_2292158).sum := by decide
  have hdescent : baseEnd_2292158 < baseStart_2292158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292185 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 5, 2]
def baseStart_2292185 : Nat := 118140960795 + 2292185 * 2 ^ 59
def prefixEnd_2292185 : Nat := 4983230072969 + 3 ^ 40 * 2292185 * 2
def baseEnd_2292185 : Nat := 1176992654026219549345939

theorem tailTrace_2292185 : CollatzResearch.WordTrace tailWord_2292185 prefixEnd_2292185 1176992654026219549345939 := by
  unfold tailWord_2292185
  simp only [CollatzResearch.WordTrace]
  refine ⟨83602855200812693876270009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55735236800541795917513339 83602855200812693876270009)
  ·
    refine ⟨62702141400609520407202507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83602855200812693876270009 62702141400609520407202507)
    ·
      refine ⟨94053212100914280610803761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62702141400609520407202507 94053212100914280610803761)
      ·
        refine ⟨70539909075685710458102821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94053212100914280610803761 70539909075685710458102821)
        ·
          refine ⟨13226232951691070710894279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70539909075685710458102821 13226232951691070710894279)
          ·
            refine ⟨19839349427536606066341419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13226232951691070710894279 19839349427536606066341419)
            ·
              refine ⟨29759024141304909099512129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19839349427536606066341419 29759024141304909099512129)
              ·
                refine ⟨22319268105978681824634097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29759024141304909099512129 22319268105978681824634097)
                ·
                  refine ⟨16739451079484011368475573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22319268105978681824634097 16739451079484011368475573)
                  ·
                    refine ⟨1569323538701626065794585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16739451079484011368475573 1569323538701626065794585)
                    ·
                      refine ⟨1176992654026219549345939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569323538701626065794585 1176992654026219549345939)
                      ·
                        rfl

theorem cell23_2292185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_2292185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292185 prefixEnd_2292185 := by exact prefixLift 2292185
  have htrace : WordTrace (prefixWord ++ tailWord_2292185) baseStart_2292185 baseEnd_2292185 := by
    simpa [prefixWord, tailWord_2292185, baseEnd_2292185] using wordTrace_append hprefix tailTrace_2292185
  have hstable : (prefixWord ++ tailWord_2292185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292185).length < 2 ^ (prefixWord ++ tailWord_2292185).sum := by decide
  have hdescent : baseEnd_2292185 < baseStart_2292185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292195 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 7]
def baseStart_2292195 : Nat := 118140960795 + 2292195 * 2 ^ 59
def prefixEnd_2292195 : Nat := 4983230072969 + 3 ^ 40 * 2292195 * 2
def baseEnd_2292195 : Nat := 392332596277588170073631

theorem tailTrace_2292195 : CollatzResearch.WordTrace tailWord_2292195 prefixEnd_2292195 392332596277588170073631 := by
  unfold tailWord_2292195
  simp only [CollatzResearch.WordTrace]
  refine ⟨83603219930776465584134039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55735479953850977056089359 83603219930776465584134039)
  ·
    refine ⟨125404829896164698376201059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83603219930776465584134039 125404829896164698376201059)
    ·
      refine ⟨188107244844247047564301589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125404829896164698376201059 188107244844247047564301589)
      ·
        refine ⟨8817527102074080354576637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188107244844247047564301589 8817527102074080354576637)
        ·
          refine ⟨3306572663277780132966239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8817527102074080354576637 3306572663277780132966239)
          ·
            refine ⟨4959858994916670199449359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306572663277780132966239 4959858994916670199449359)
            ·
              refine ⟨7439788492375005299174039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959858994916670199449359 7439788492375005299174039)
              ·
                refine ⟨11159682738562507948761059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439788492375005299174039 11159682738562507948761059)
                ·
                  refine ⟨16739524107843761923141589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11159682738562507948761059 16739524107843761923141589)
                  ·
                    refine ⟨392332596277588170073631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16739524107843761923141589 392332596277588170073631)
                    ·
                      rfl

theorem cell23_2292195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].length) (baseStart_2292195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292195 prefixEnd_2292195 := by exact prefixLift 2292195
  have htrace : WordTrace (prefixWord ++ tailWord_2292195) baseStart_2292195 baseEnd_2292195 := by
    simpa [prefixWord, tailWord_2292195, baseEnd_2292195] using wordTrace_append hprefix tailTrace_2292195
  have hstable : (prefixWord ++ tailWord_2292195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292195).length < 2 ^ (prefixWord ++ tailWord_2292195).sum := by decide
  have hdescent : baseEnd_2292195 < baseStart_2292195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292235 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3]
def baseStart_2292235 : Nat := 118140960795 + 2292235 * 2 ^ 59
def prefixEnd_2292235 : Nat := 4983230072969 + 3 ^ 40 * 2292235 * 2
def baseEnd_2292235 : Nat := 1177018328058944353720709

theorem tailTrace_2292235 : CollatzResearch.WordTrace tailWord_2292235 prefixEnd_2292235 1177018328058944353720709 := by
  unfold tailWord_2292235
  simp only [CollatzResearch.WordTrace]
  refine ⟨83604678850631552415590159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55736452567087701610393439 83604678850631552415590159)
  ·
    refine ⟨125407018275947328623385239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83604678850631552415590159 125407018275947328623385239)
    ·
      refine ⟨188110527413920992935077859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125407018275947328623385239 188110527413920992935077859)
      ·
        refine ⟨282165791120881489402616789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188110527413920992935077859 282165791120881489402616789)
        ·
          refine ⟨6613260729395659907873831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 282165791120881489402616789 6613260729395659907873831)
          ·
            refine ⟨9919891094093489861810747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613260729395659907873831 9919891094093489861810747)
            ·
              refine ⟨14879836641140234792716121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919891094093489861810747 14879836641140234792716121)
              ·
                refine ⟨11159877480855176094537091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14879836641140234792716121 11159877480855176094537091)
                ·
                  refine ⟨16739816221282764141805637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11159877480855176094537091 16739816221282764141805637)
                  ·
                    refine ⟨3138715541490518276588557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16739816221282764141805637 3138715541490518276588557)
                    ·
                      refine ⟨1177018328058944353720709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3138715541490518276588557 1177018328058944353720709)
                      ·
                        rfl

theorem cell23_2292235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].length) (baseStart_2292235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292235 prefixEnd_2292235 := by exact prefixLift 2292235
  have htrace : WordTrace (prefixWord ++ tailWord_2292235) baseStart_2292235 baseEnd_2292235 := by
    simpa [prefixWord, tailWord_2292235, baseEnd_2292235] using wordTrace_append hprefix tailTrace_2292235
  have hstable : (prefixWord ++ tailWord_2292235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292235).length < 2 ^ (prefixWord ++ tailWord_2292235).sum := by decide
  have hdescent : baseEnd_2292235 < baseStart_2292235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292259 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 1, 4]
def baseStart_2292259 : Nat := 118140960795 + 2292259 * 2 ^ 59
def prefixEnd_2292259 : Nat := 4983230072969 + 3 ^ 40 * 2292259 * 2
def baseEnd_2292259 : Nat := 392343550531550753273533

theorem tailTrace_2292259 : CollatzResearch.WordTrace tailWord_2292259 prefixEnd_2292259 392343550531550753273533 := by
  unfold tailWord_2292259
  simp only [CollatzResearch.WordTrace]
  refine ⟨83605554202544604514463831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55737036135029736342975887 83605554202544604514463831)
  ·
    refine ⟨125408331303816906771695747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83605554202544604514463831 125408331303816906771695747)
    ·
      refine ⟨188112496955725360157543621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125408331303816906771695747 188112496955725360157543621)
      ·
        refine ⟨35271093179198505029539429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188112496955725360157543621 35271093179198505029539429)
        ·
          refine ⟨6613329971099719693038643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35271093179198505029539429 6613329971099719693038643)
          ·
            refine ⟨9919994956649579539557965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613329971099719693038643 9919994956649579539557965)
            ·
              refine ⟨3719998108743592327334237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9919994956649579539557965 3719998108743592327334237)
              ·
                refine ⟨1394999290778847122750339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3719998108743592327334237 1394999290778847122750339)
                ·
                  refine ⟨2092498936168270684125509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394999290778847122750339 2092498936168270684125509)
                  ·
                    refine ⟨392343550531550753273533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092498936168270684125509 392343550531550753273533)
                    ·
                      rfl

theorem cell23_2292259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 4].length) (baseStart_2292259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292259 prefixEnd_2292259 := by exact prefixLift 2292259
  have htrace : WordTrace (prefixWord ++ tailWord_2292259) baseStart_2292259 baseEnd_2292259 := by
    simpa [prefixWord, tailWord_2292259, baseEnd_2292259] using wordTrace_append hprefix tailTrace_2292259
  have hstable : (prefixWord ++ tailWord_2292259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292259).length < 2 ^ (prefixWord ++ tailWord_2292259).sum := by decide
  have hdescent : baseEnd_2292259 < baseStart_2292259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292289 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 6]
def baseStart_2292289 : Nat := 118140960795 + 2292289 * 2 ^ 59
def prefixEnd_2292289 : Nat := 4983230072969 + 3 ^ 40 * 2292289 * 2
def baseEnd_2292289 : Nat := 130782895112698571382829

theorem tailTrace_2292289 : CollatzResearch.WordTrace tailWord_2292289 prefixEnd_2292289 130782895112698571382829 := by
  unfold tailWord_2292289
  simp only [CollatzResearch.WordTrace]
  refine ⟨83606648392435919638055921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55737765594957279758703947 83606648392435919638055921)
  ·
    refine ⟨62704986294326939728541941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83606648392435919638055921 62704986294326939728541941)
    ·
      refine ⟨5878592465093150599550807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62704986294326939728541941 5878592465093150599550807)
      ·
        refine ⟨8817888697639725899326211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878592465093150599550807 8817888697639725899326211)
        ·
          refine ⟨13226833046459588848989317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8817888697639725899326211 13226833046459588848989317)
          ·
            refine ⟨2480031196211172909185497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13226833046459588848989317 2480031196211172909185497)
            ·
              refine ⟨1860023397158379681889123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480031196211172909185497 1860023397158379681889123)
              ·
                refine ⟨2790035095737569522833685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860023397158379681889123 2790035095737569522833685)
                ·
                  refine ⟨130782895112698571382829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2790035095737569522833685 130782895112698571382829)
                  ·
                    rfl

theorem cell23_2292289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_2292289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292289 prefixEnd_2292289 := by exact prefixLift 2292289
  have htrace : WordTrace (prefixWord ++ tailWord_2292289) baseStart_2292289 baseEnd_2292289 := by
    simpa [prefixWord, tailWord_2292289, baseEnd_2292289] using wordTrace_append hprefix tailTrace_2292289
  have hstable : (prefixWord ++ tailWord_2292289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292289).length < 2 ^ (prefixWord ++ tailWord_2292289).sum := by decide
  have hdescent : baseEnd_2292289 < baseStart_2292289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292302 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2292302 : Nat := 118140960795 + 2292302 * 2 ^ 59
def prefixEnd_2292302 : Nat := 4983230072969 + 3 ^ 40 * 2292302 * 2
def baseEnd_2292302 : Nat := 392350910420931863860967

theorem tailTrace_2292302 : CollatzResearch.WordTrace tailWord_2292302 prefixEnd_2292302 392350910420931863860967 := by
  unfold tailWord_2292302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450890317673602857284895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55738081694259215238852773 10450890317673602857284895)
  ·
    refine ⟨15676335476510404285927343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10450890317673602857284895 15676335476510404285927343)
    ·
      refine ⟨23514503214765606428891015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15676335476510404285927343 23514503214765606428891015)
      ·
        refine ⟨35271754822148409643336523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23514503214765606428891015 35271754822148409643336523)
        ·
          refine ⟨52907632233222614465004785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35271754822148409643336523 52907632233222614465004785)
          ·
            refine ⟨39680724174916960848753589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52907632233222614465004785 39680724174916960848753589)
            ·
              refine ⟨3720067891398465079570649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39680724174916960848753589 3720067891398465079570649)
              ·
                refine ⟨2790050918548848809677987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720067891398465079570649 2790050918548848809677987)
                ·
                  refine ⟨4185076377823273214516981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790050918548848809677987 4185076377823273214516981)
                  ·
                    refine ⟨392350910420931863860967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4185076377823273214516981 392350910420931863860967)
                    ·
                      rfl

theorem cell23_2292302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2292302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292302 prefixEnd_2292302 := by exact prefixLift 2292302
  have htrace : WordTrace (prefixWord ++ tailWord_2292302) baseStart_2292302 baseEnd_2292302 := by
    simpa [prefixWord, tailWord_2292302, baseEnd_2292302] using wordTrace_append hprefix tailTrace_2292302
  have hstable : (prefixWord ++ tailWord_2292302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292302).length < 2 ^ (prefixWord ++ tailWord_2292302).sum := by decide
  have hdescent : baseEnd_2292302 < baseStart_2292302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292332 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_2292332 : Nat := 118140960795 + 2292332 * 2 ^ 59
def prefixEnd_2292332 : Nat := 4983230072969 + 3 ^ 40 * 2292332 * 2
def baseEnd_2292332 : Nat := 392356045227476824735921

theorem tailTrace_2292332 : CollatzResearch.WordTrace tailWord_2292332 prefixEnd_2292332 392356045227476824735921 := by
  unfold tailWord_2292332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41804108365640068990935625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55738811154186758654580833 41804108365640068990935625)
  ·
    refine ⟨31353081274230051743201719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41804108365640068990935625 31353081274230051743201719)
    ·
      refine ⟨47029621911345077614802579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31353081274230051743201719 47029621911345077614802579)
      ·
        refine ⟨70544432867017616422203869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47029621911345077614802579 70544432867017616422203869)
        ·
          refine ⟨26454162325131606158326451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70544432867017616422203869 26454162325131606158326451)
          ·
            refine ⟨39681243487697409237489677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26454162325131606158326451 39681243487697409237489677)
            ·
              refine ⟨14880466307886528464058629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39681243487697409237489677 14880466307886528464058629)
              ·
                refine ⟨2790087432728724087010993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14880466307886528464058629 2790087432728724087010993)
                ·
                  refine ⟨2092565574546543065258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790087432728724087010993 2092565574546543065258245)
                  ·
                    refine ⟨392356045227476824735921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092565574546543065258245 392356045227476824735921)
                    ·
                      rfl

theorem cell23_2292332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_2292332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292332 prefixEnd_2292332 := by exact prefixLift 2292332
  have htrace : WordTrace (prefixWord ++ tailWord_2292332) baseStart_2292332 baseEnd_2292332 := by
    simpa [prefixWord, tailWord_2292332, baseEnd_2292332] using wordTrace_append hprefix tailTrace_2292332
  have hstable : (prefixWord ++ tailWord_2292332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292332).length < 2 ^ (prefixWord ++ tailWord_2292332).sum := by decide
  have hdescent : baseEnd_2292332 < baseStart_2292332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292333 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2292333 : Nat := 118140960795 + 2292333 * 2 ^ 59
def prefixEnd_2292333 : Nat := 4983230072969 + 3 ^ 40 * 2292333 * 2
def baseEnd_2292333 : Nat := 1177068649163084970295259

theorem tailTrace_2292333 : CollatzResearch.WordTrace tailWord_2292333 prefixEnd_2292333 1177068649163084970295259 := by
  unfold tailWord_2292333
  simp only [CollatzResearch.WordTrace]
  refine ⟨83608253204276515152657653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55738835469517676768438435 83608253204276515152657653)
  ·
    refine ⟨7838273737900923295561655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83608253204276515152657653 7838273737900923295561655)
    ·
      refine ⟨11757410606851384943342483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7838273737900923295561655 11757410606851384943342483)
      ·
        refine ⟨17636115910277077415013725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11757410606851384943342483 17636115910277077415013725)
        ·
          refine ⟨6613543466353904030630147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17636115910277077415013725 6613543466353904030630147)
          ·
            refine ⟨9920315199530856045945221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613543466353904030630147 9920315199530856045945221)
            ·
              refine ⟨1860059099912035508614729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9920315199530856045945221 1860059099912035508614729)
              ·
                refine ⟨1395044324934026631461047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860059099912035508614729 1395044324934026631461047)
                ·
                  refine ⟨2092566487401039947191571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395044324934026631461047 2092566487401039947191571)
                  ·
                    refine ⟨3138849731101559920787357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2092566487401039947191571 3138849731101559920787357)
                    ·
                      refine ⟨1177068649163084970295259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3138849731101559920787357 1177068649163084970295259)
                      ·
                        rfl

theorem cell23_2292333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2292333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292333 prefixEnd_2292333 := by exact prefixLift 2292333
  have htrace : WordTrace (prefixWord ++ tailWord_2292333) baseStart_2292333 baseEnd_2292333 := by
    simpa [prefixWord, tailWord_2292333, baseEnd_2292333] using wordTrace_append hprefix tailTrace_2292333
  have hstable : (prefixWord ++ tailWord_2292333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292333).length < 2 ^ (prefixWord ++ tailWord_2292333).sum := by decide
  have hdescent : baseEnd_2292333 < baseStart_2292333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292345 : List Nat := [1, 2, 1, 3, 3, 2, 3, 8]
def baseStart_2292345 : Nat := 118140960795 + 2292345 * 2 ^ 59
def prefixEnd_2292345 : Nat := 4983230072969 + 3 ^ 40 * 2292345 * 2
def baseEnd_2292345 : Nat := 43595363367812552716489

theorem tailTrace_2292345 : CollatzResearch.WordTrace tailWord_2292345 prefixEnd_2292345 43595363367812552716489 := by
  unfold tailWord_2292345
  simp only [CollatzResearch.WordTrace]
  refine ⟨83608690880233041202094489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55739127253488694134729659 83608690880233041202094489)
  ·
    refine ⟨62706518160174780901570867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83608690880233041202094489 62706518160174780901570867)
    ·
      refine ⟨94059777240262171352356301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62706518160174780901570867 94059777240262171352356301)
      ·
        refine ⟨35272416465098314257133613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94059777240262171352356301 35272416465098314257133613)
        ·
          refine ⟨13227156174411867846425105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35272416465098314257133613 13227156174411867846425105)
          ·
            refine ⟨9920367130808900884818829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13227156174411867846425105 9920367130808900884818829)
            ·
              refine ⟨3720137674053337831807061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9920367130808900884818829 3720137674053337831807061)
              ·
                refine ⟨43595363367812552716489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3720137674053337831807061 43595363367812552716489)
                ·
                  rfl

theorem cell23_2292345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 8].length) (baseStart_2292345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292345 prefixEnd_2292345 := by exact prefixLift 2292345
  have htrace : WordTrace (prefixWord ++ tailWord_2292345) baseStart_2292345 baseEnd_2292345 := by
    simpa [prefixWord, tailWord_2292345, baseEnd_2292345] using wordTrace_append hprefix tailTrace_2292345
  have hstable : (prefixWord ++ tailWord_2292345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292345).length < 2 ^ (prefixWord ++ tailWord_2292345).sum := by decide
  have hdescent : baseEnd_2292345 < baseStart_2292345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292352 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_2292352 : Nat := 118140960795 + 2292352 * 2 ^ 59
def prefixEnd_2292352 : Nat := 4983230072969 + 3 ^ 40 * 2292352 * 2
def baseEnd_2292352 : Nat := 1177078405295520395957671

theorem tailTrace_2292352 : CollatzResearch.WordTrace tailWord_2292352 prefixEnd_2292352 1177078405295520395957671 := by
  unfold tailWord_2292352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41804473095603840698799655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55739297460805120931732873 41804473095603840698799655)
  ·
    refine ⟨62706709643405761048199483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41804473095603840698799655 62706709643405761048199483)
    ·
      refine ⟨94060064465108641572299225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62706709643405761048199483 94060064465108641572299225)
      ·
        refine ⟨70545048348831481179224419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94060064465108641572299225 70545048348831481179224419)
        ·
          refine ⟨105817572523247221768836629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70545048348831481179224419 105817572523247221768836629)
          ·
            refine ⟨4960198712027213520414217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105817572523247221768836629 4960198712027213520414217)
            ·
              refine ⟨3720149034020410140310663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960198712027213520414217 3720149034020410140310663)
              ·
                refine ⟨5580223551030615210465995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720149034020410140310663 5580223551030615210465995)
                ·
                  refine ⟨8370335326545922815698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580223551030615210465995 8370335326545922815698993)
                  ·
                    refine ⟨6277751494909442111774245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8370335326545922815698993 6277751494909442111774245)
                    ·
                      refine ⟨1177078405295520395957671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6277751494909442111774245 1177078405295520395957671)
                      ·
                        rfl

theorem cell23_2292352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_2292352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292352 prefixEnd_2292352 := by exact prefixLift 2292352
  have htrace : WordTrace (prefixWord ++ tailWord_2292352) baseStart_2292352 baseEnd_2292352 := by
    simpa [prefixWord, tailWord_2292352, baseEnd_2292352] using wordTrace_append hprefix tailTrace_2292352
  have hstable : (prefixWord ++ tailWord_2292352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292352).length < 2 ^ (prefixWord ++ tailWord_2292352).sum := by decide
  have hdescent : baseEnd_2292352 < baseStart_2292352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292356 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_2292356 : Nat := 118140960795 + 2292356 * 2 ^ 59
def prefixEnd_2292356 : Nat := 4983230072969 + 3 ^ 40 * 2292356 * 2
def baseEnd_2292356 : Nat := 1177080459218138380307653

theorem tailTrace_2292356 : CollatzResearch.WordTrace tailWord_2292356 prefixEnd_2292356 1177080459218138380307653 := by
  unfold tailWord_2292356
  simp only [CollatzResearch.WordTrace]
  refine ⟨41804546041596595040372461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55739394722128793387163281 41804546041596595040372461)
  ·
    refine ⟨15676704765598723140139673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41804546041596595040372461 15676704765598723140139673)
    ·
      refine ⟨11757528574199042355104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15676704765598723140139673 11757528574199042355104755)
      ·
        refine ⟨17636292861298563532657133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11757528574199042355104755 17636292861298563532657133)
        ·
          refine ⟨6613609822986961324746425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17636292861298563532657133 6613609822986961324746425)
          ·
            refine ⟨4960207367240220993559819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6613609822986961324746425 4960207367240220993559819)
            ·
              refine ⟨7440311050860331490339729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960207367240220993559819 7440311050860331490339729)
              ·
                refine ⟨5580233288145248617754797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7440311050860331490339729 5580233288145248617754797)
                ·
                  refine ⟨2092587483054468231658049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5580233288145248617754797 2092587483054468231658049)
                  ·
                    refine ⟨1569440612290851173743537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092587483054468231658049 1569440612290851173743537)
                    ·
                      refine ⟨1177080459218138380307653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569440612290851173743537 1177080459218138380307653)
                      ·
                        rfl

theorem cell23_2292356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_2292356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292356 prefixEnd_2292356 := by exact prefixLift 2292356
  have htrace : WordTrace (prefixWord ++ tailWord_2292356) baseStart_2292356 baseEnd_2292356 := by
    simpa [prefixWord, tailWord_2292356, baseEnd_2292356] using wordTrace_append hprefix tailTrace_2292356
  have hstable : (prefixWord ++ tailWord_2292356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292356).length < 2 ^ (prefixWord ++ tailWord_2292356).sum := by decide
  have hdescent : baseEnd_2292356 < baseStart_2292356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292416 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2]
def baseStart_2292416 : Nat := 118140960795 + 2292416 * 2 ^ 59
def prefixEnd_2292416 : Nat := 4983230072969 + 3 ^ 40 * 2292416 * 2
def baseEnd_2292416 : Nat := 1177111268057408145557377

theorem tailTrace_2292416 : CollatzResearch.WordTrace tailWord_2292416 prefixEnd_2292416 1177111268057408145557377 := by
  unfold tailWord_2292416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41805640231487910163964551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55740853641983880218619401 41805640231487910163964551)
  ·
    refine ⟨62708460347231865245946827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41805640231487910163964551 62708460347231865245946827)
    ·
      refine ⟨94062690520847797868920241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62708460347231865245946827 94062690520847797868920241)
      ·
        refine ⟨70547017890635848401690181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94062690520847797868920241 70547017890635848401690181)
        ·
          refine ⟨13227565854494221575316909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70547017890635848401690181 13227565854494221575316909)
          ·
            refine ⟨4960337195435333090743841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13227565854494221575316909 4960337195435333090743841)
            ·
              refine ⟨3720252896576499818057881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960337195435333090743841 3720252896576499818057881)
              ·
                refine ⟨2790189672432374863543411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720252896576499818057881 2790189672432374863543411)
                ·
                  refine ⟨4185284508648562295315117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790189672432374863543411 4185284508648562295315117)
                  ·
                    refine ⟨1569481690743210860743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4185284508648562295315117 1569481690743210860743169)
                    ·
                      refine ⟨1177111268057408145557377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569481690743210860743169 1177111268057408145557377)
                      ·
                        rfl

theorem cell23_2292416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_2292416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292416 prefixEnd_2292416 := by exact prefixLift 2292416
  have htrace : WordTrace (prefixWord ++ tailWord_2292416) baseStart_2292416 baseEnd_2292416 := by
    simpa [prefixWord, tailWord_2292416, baseEnd_2292416] using wordTrace_append hprefix tailTrace_2292416
  have hstable : (prefixWord ++ tailWord_2292416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292416).length < 2 ^ (prefixWord ++ tailWord_2292416).sum := by decide
  have hdescent : baseEnd_2292416 < baseStart_2292416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292452 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 7]
def baseStart_2292452 : Nat := 118140960795 + 2292452 * 2 ^ 59
def prefixEnd_2292452 : Nat := 4983230072969 + 3 ^ 40 * 2292452 * 2
def baseEnd_2292452 : Nat := 130792194817885556078579

theorem tailTrace_2292452 : CollatzResearch.WordTrace tailWord_2292452 prefixEnd_2292452 130792194817885556078579 := by
  unfold tailWord_2292452
  simp only [CollatzResearch.WordTrace]
  refine ⟨41806296745422699238119805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55741728993896932317493073 41806296745422699238119805)
  ·
    refine ⟨15677361279533512214294927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41806296745422699238119805 15677361279533512214294927)
    ·
      refine ⟨23516041919300268321442391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15677361279533512214294927 23516041919300268321442391)
      ·
        refine ⟨35274062878950402482163587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23516041919300268321442391 35274062878950402482163587)
        ·
          refine ⟨52911094318425603723245381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35274062878950402482163587 52911094318425603723245381)
          ·
            refine ⟨9920830184704800698108509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52911094318425603723245381 9920830184704800698108509)
            ·
              refine ⟨3720311319264300261790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9920830184704800698108509 3720311319264300261790691)
              ·
                refine ⟨5580466978896450392686037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720311319264300261790691 5580466978896450392686037)
                ·
                  refine ⟨130792194817885556078579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5580466978896450392686037 130792194817885556078579)
                  ·
                    rfl

theorem cell23_2292452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_2292452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292452 prefixEnd_2292452 := by exact prefixLift 2292452
  have htrace : WordTrace (prefixWord ++ tailWord_2292452) baseStart_2292452 baseEnd_2292452 := by
    simpa [prefixWord, tailWord_2292452, baseEnd_2292452] using wordTrace_append hprefix tailTrace_2292452
  have hstable : (prefixWord ++ tailWord_2292452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292452).length < 2 ^ (prefixWord ++ tailWord_2292452).sum := by decide
  have hdescent : baseEnd_2292452 < baseStart_2292452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292463 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 2, 2, 2]
def baseStart_2292463 : Nat := 118140960795 + 2292463 * 2 ^ 59
def prefixEnd_2292463 : Nat := 4983230072969 + 3 ^ 40 * 2292463 * 2
def baseEnd_2292463 : Nat := 1177135401648169461669661

theorem tailTrace_2292463 : CollatzResearch.WordTrace tailWord_2292463 prefixEnd_2292463 1177135401648169461669661 := by
  unfold tailWord_2292463
  simp only [CollatzResearch.WordTrace]
  refine ⟨83612994693805547354890043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55741996462537031569926695 83612994693805547354890043)
  ·
    refine ⟨125419492040708321032335065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83612994693805547354890043 125419492040708321032335065)
    ·
      refine ⟨94064619030531240774251299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125419492040708321032335065 94064619030531240774251299)
      ·
        refine ⟨141096928545796861161376949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94064619030531240774251299 141096928545796861161376949)
        ·
          refine ⟨13227837051168455733879089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141096928545796861161376949 13227837051168455733879089)
          ·
            refine ⟨9920877788376341800409317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13227837051168455733879089 9920877788376341800409317)
            ·
              refine ⟨1860164585320564087576747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9920877788376341800409317 1860164585320564087576747)
              ·
                refine ⟨2790246877980846131365121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860164585320564087576747 2790246877980846131365121)
                ·
                  refine ⟨2092685158485634598523841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790246877980846131365121 2092685158485634598523841)
                  ·
                    refine ⟨1569513868864225948892881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092685158485634598523841 1569513868864225948892881)
                    ·
                      refine ⟨1177135401648169461669661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569513868864225948892881 1177135401648169461669661)
                      ·
                        rfl

theorem cell23_2292463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 2, 2].length) (baseStart_2292463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292463 prefixEnd_2292463 := by exact prefixLift 2292463
  have htrace : WordTrace (prefixWord ++ tailWord_2292463) baseStart_2292463 baseEnd_2292463 := by
    simpa [prefixWord, tailWord_2292463, baseEnd_2292463] using wordTrace_append hprefix tailTrace_2292463
  have hstable : (prefixWord ++ tailWord_2292463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292463).length < 2 ^ (prefixWord ++ tailWord_2292463).sum := by decide
  have hdescent : baseEnd_2292463 < baseStart_2292463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292503 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 5]
def baseStart_2292503 : Nat := 118140960795 + 2292503 * 2 ^ 59
def prefixEnd_2292503 : Nat := 4983230072969 + 3 ^ 40 * 2292503 * 2
def baseEnd_2292503 : Nat := 130795104541594367241053

theorem tailTrace_2292503 : CollatzResearch.WordTrace tailWord_2292503 prefixEnd_2292503 130795104541594367241053 := by
  unfold tailWord_2292503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83614453613660634186346163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55742969075773756124230775 83614453613660634186346163)
  ·
    refine ⟨125421680420490951279519245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83614453613660634186346163 125421680420490951279519245)
    ·
      refine ⟨47033130157684106729819717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125421680420490951279519245 47033130157684106729819717)
      ·
        refine ⟨8818711904565770011841197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47033130157684106729819717 8818711904565770011841197)
        ·
          refine ⟨3307016964212163754440449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8818711904565770011841197 3307016964212163754440449)
          ·
            refine ⟨2480262723159122815830337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3307016964212163754440449 2480262723159122815830337)
            ·
              refine ⟨1860197042369342111872753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480262723159122815830337 1860197042369342111872753)
              ·
                refine ⟨1395147781777006583904565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860197042369342111872753 1395147781777006583904565)
                ·
                  refine ⟨130795104541594367241053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1395147781777006583904565 130795104541594367241053)
                  ·
                    rfl

theorem cell23_2292503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 5].length) (baseStart_2292503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292503 prefixEnd_2292503 := by exact prefixLift 2292503
  have htrace : WordTrace (prefixWord ++ tailWord_2292503) baseStart_2292503 baseEnd_2292503 := by
    simpa [prefixWord, tailWord_2292503, baseEnd_2292503] using wordTrace_append hprefix tailTrace_2292503
  have hstable : (prefixWord ++ tailWord_2292503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292503).length < 2 ^ (prefixWord ++ tailWord_2292503).sum := by decide
  have hdescent : baseEnd_2292503 < baseStart_2292503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292529 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_2292529 : Nat := 118140960795 + 2292529 * 2 ^ 59
def prefixEnd_2292529 : Nat := 4983230072969 + 3 ^ 40 * 2292529 * 2
def baseEnd_2292529 : Nat := 392389763790455401148119

theorem tailTrace_2292529 : CollatzResearch.WordTrace tailWord_2292529 prefixEnd_2292529 392389763790455401148119 := by
  unfold tailWord_2292529
  simp only [CollatzResearch.WordTrace]
  refine ⟨83615401911566440626792641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55743601274377627084528427 83615401911566440626792641)
  ·
    refine ⟨62711551433674830470094481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83615401911566440626792641 62711551433674830470094481)
    ·
      refine ⟨47033663575256122852570861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62711551433674830470094481 47033663575256122852570861)
      ·
        refine ⟨17637623840721046069714073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47033663575256122852570861 17637623840721046069714073)
        ·
          refine ⟨13228217880540784552285555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17637623840721046069714073 13228217880540784552285555)
          ·
            refine ⟨19842326820811176828428333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13228217880540784552285555 19842326820811176828428333)
            ·
              refine ⟨7440872557804191310660625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19842326820811176828428333 7440872557804191310660625)
              ·
                refine ⟨5580654418353143482995469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7440872557804191310660625 5580654418353143482995469)
                ·
                  refine ⟨2092745406882428806123301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5580654418353143482995469 2092745406882428806123301)
                  ·
                    refine ⟨392389763790455401148119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092745406882428806123301 392389763790455401148119)
                    ·
                      rfl

theorem cell23_2292529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_2292529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292529 prefixEnd_2292529 := by exact prefixLift 2292529
  have htrace : WordTrace (prefixWord ++ tailWord_2292529) baseStart_2292529 baseEnd_2292529 := by
    simpa [prefixWord, tailWord_2292529, baseEnd_2292529] using wordTrace_append hprefix tailTrace_2292529
  have hstable : (prefixWord ++ tailWord_2292529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292529).length < 2 ^ (prefixWord ++ tailWord_2292529).sum := by decide
  have hdescent : baseEnd_2292529 < baseStart_2292529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292562 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2292562 : Nat := 118140960795 + 2292562 * 2 ^ 59
def prefixEnd_2292562 : Nat := 4983230072969 + 3 ^ 40 * 2292562 * 2
def baseEnd_2292562 : Nat := 1177186236232964574331705

theorem tailTrace_2292562 : CollatzResearch.WordTrace tailWord_2292562 prefixEnd_2292562 1177186236232964574331705 := by
  unfold tailWord_2292562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904151380111721815685985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55744403680297924841829293 20904151380111721815685985)
  ·
    refine ⟨15678113535083791361764489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20904151380111721815685985 15678113535083791361764489)
    ·
      refine ⟨11758585151312843521323367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15678113535083791361764489 11758585151312843521323367)
      ·
        refine ⟨17637877726969265281985051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11758585151312843521323367 17637877726969265281985051)
        ·
          refine ⟨26456816590453897922977577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17637877726969265281985051 26456816590453897922977577)
          ·
            refine ⟨19842612442840423442233183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26456816590453897922977577 19842612442840423442233183)
            ·
              refine ⟨29763918664260635163349775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19842612442840423442233183 29763918664260635163349775)
              ·
                refine ⟨44645877996390952745024663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29763918664260635163349775 44645877996390952745024663)
                ·
                  refine ⟨66968816994586429117536995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44645877996390952745024663 66968816994586429117536995)
                  ·
                    refine ⟨100453225491879643676305493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66968816994586429117536995 100453225491879643676305493)
                    ·
                      refine ⟨1177186236232964574331705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100453225491879643676305493 1177186236232964574331705)
                      ·
                        rfl

theorem cell23_2292562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2292562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292562 prefixEnd_2292562 := by exact prefixLift 2292562
  have htrace : WordTrace (prefixWord ++ tailWord_2292562) baseStart_2292562 baseEnd_2292562 := by
    simpa [prefixWord, tailWord_2292562, baseEnd_2292562] using wordTrace_append hprefix tailTrace_2292562
  have hstable : (prefixWord ++ tailWord_2292562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292562).length < 2 ^ (prefixWord ++ tailWord_2292562).sum := by decide
  have hdescent : baseEnd_2292562 < baseStart_2292562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292602 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_2292602 : Nat := 118140960795 + 2292602 * 2 ^ 59
def prefixEnd_2292602 : Nat := 4983230072969 + 3 ^ 40 * 2292602 * 2
def baseEnd_2292602 : Nat := 392402258486381472610507

theorem tailTrace_2292602 : CollatzResearch.WordTrace tailWord_2292602 prefixEnd_2292602 392402258486381472610507 := by
  unfold tailWord_2292602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904516110075493523550015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55745376293534649396133373 20904516110075493523550015)
  ·
    refine ⟨31356774165113240285325023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20904516110075493523550015 31356774165113240285325023)
    ·
      refine ⟨47035161247669860427987535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31356774165113240285325023 47035161247669860427987535)
      ·
        refine ⟨70552741871504790641981303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47035161247669860427987535 70552741871504790641981303)
        ·
          refine ⟨105829112807257185962971955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70552741871504790641981303 105829112807257185962971955)
          ·
            refine ⟨158743669210885778944457933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105829112807257185962971955 158743669210885778944457933)
            ·
              refine ⟨59528875954082167104171725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158743669210885778944457933 59528875954082167104171725)
              ·
                refine ⟨22323328482780812664064397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59528875954082167104171725 22323328482780812664064397)
                ·
                  refine ⟨8371248181042804749024149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22323328482780812664064397 8371248181042804749024149)
                  ·
                    refine ⟨392402258486381472610507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8371248181042804749024149 392402258486381472610507)
                    ·
                      rfl

theorem cell23_2292602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_2292602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292602 prefixEnd_2292602 := by exact prefixLift 2292602
  have htrace : WordTrace (prefixWord ++ tailWord_2292602) baseStart_2292602 baseEnd_2292602 := by
    simpa [prefixWord, tailWord_2292602, baseEnd_2292602] using wordTrace_append hprefix tailTrace_2292602
  have hstable : (prefixWord ++ tailWord_2292602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292602).length < 2 ^ (prefixWord ++ tailWord_2292602).sum := by decide
  have hdescent : baseEnd_2292602 < baseStart_2292602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292603 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 1, 1, 3]
def baseStart_2292603 : Nat := 118140960795 + 2292603 * 2 ^ 59
def prefixEnd_2292603 : Nat := 4983230072969 + 3 ^ 40 * 2292603 * 2
def baseEnd_2292603 : Nat := 1177207288939798913919017

theorem tailTrace_2292603 : CollatzResearch.WordTrace tailWord_2292603 prefixEnd_2292603 1177207288939798913919017 := by
  unfold tailWord_2292603
  simp only [CollatzResearch.WordTrace]
  refine ⟨83618100913298351264986463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55745400608865567509990975 83618100913298351264986463)
  ·
    refine ⟨125427151369947526897479695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83618100913298351264986463 125427151369947526897479695)
    ·
      refine ⟨188140727054921290346219543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125427151369947526897479695 188140727054921290346219543)
      ·
        refine ⟨282211090582381935519329315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188140727054921290346219543 282211090582381935519329315)
        ·
          refine ⟨423316635873572903278993973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282211090582381935519329315 423316635873572903278993973)
          ·
            refine ⟨39685934613147459682405685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 423316635873572903278993973 39685934613147459682405685)
            ·
              refine ⟨3720556369982574345225533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39685934613147459682405685 3720556369982574345225533)
              ·
                refine ⟨1395208638743465379459575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3720556369982574345225533 1395208638743465379459575)
                ·
                  refine ⟨2092812958115198069189363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395208638743465379459575 2092812958115198069189363)
                  ·
                    refine ⟨3139219437172797103784045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2092812958115198069189363 3139219437172797103784045)
                    ·
                      refine ⟨1177207288939798913919017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3139219437172797103784045 1177207288939798913919017)
                      ·
                        rfl

theorem cell23_2292603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 1, 3].length) (baseStart_2292603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292603 prefixEnd_2292603 := by exact prefixLift 2292603
  have htrace : WordTrace (prefixWord ++ tailWord_2292603) baseStart_2292603 baseEnd_2292603 := by
    simpa [prefixWord, tailWord_2292603, baseEnd_2292603] using wordTrace_append hprefix tailTrace_2292603
  have hstable : (prefixWord ++ tailWord_2292603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292603).length < 2 ^ (prefixWord ++ tailWord_2292603).sum := by decide
  have hdescent : baseEnd_2292603 < baseStart_2292603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292619 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 4, 4]
def baseStart_2292619 : Nat := 118140960795 + 2292619 * 2 ^ 59
def prefixEnd_2292619 : Nat := 4983230072969 + 3 ^ 40 * 2292619 * 2
def baseEnd_2292619 : Nat := 392405168210090283772981

theorem tailTrace_2292619 : CollatzResearch.WordTrace tailWord_2292619 prefixEnd_2292619 392405168210090283772981 := by
  unfold tailWord_2292619
  simp only [CollatzResearch.WordTrace]
  refine ⟨83618684481240385997568911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55745789654160257331712607 83618684481240385997568911)
  ·
    refine ⟨125428026721860578996353367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83618684481240385997568911 125428026721860578996353367)
    ·
      refine ⟨188142040082790868494530051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125428026721860578996353367 188142040082790868494530051)
      ·
        refine ⟨282213060124186302741795077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188142040082790868494530051 282213060124186302741795077)
        ·
          refine ⟨52914948773284931764086577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282213060124186302741795077 52914948773284931764086577)
          ·
            refine ⟨39686211579963698823064933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52914948773284931764086577 39686211579963698823064933)
            ·
              refine ⟨7441164671243193529324675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39686211579963698823064933 7441164671243193529324675)
              ·
                refine ⟨11161747006864790293987013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441164671243193529324675 11161747006864790293987013)
                ·
                  refine ⟨2092827563787148180122565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11161747006864790293987013 2092827563787148180122565)
                  ·
                    refine ⟨392405168210090283772981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2092827563787148180122565 392405168210090283772981)
                    ·
                      rfl

theorem cell23_2292619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 4].length) (baseStart_2292619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292619 prefixEnd_2292619 := by exact prefixLift 2292619
  have htrace : WordTrace (prefixWord ++ tailWord_2292619) baseStart_2292619 baseEnd_2292619 := by
    simpa [prefixWord, tailWord_2292619, baseEnd_2292619] using wordTrace_append hprefix tailTrace_2292619
  have hstable : (prefixWord ++ tailWord_2292619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292619).length < 2 ^ (prefixWord ++ tailWord_2292619).sum := by decide
  have hdescent : baseEnd_2292619 < baseStart_2292619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292629 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2292629 : Nat := 118140960795 + 2292629 * 2 ^ 59
def prefixEnd_2292629 : Nat := 4983230072969 + 3 ^ 40 * 2292629 * 2
def baseEnd_2292629 : Nat := 1177220639436815812193897

theorem tailTrace_2292629 : CollatzResearch.WordTrace tailWord_2292629 prefixEnd_2292629 1177220639436815812193897 := by
  unfold tailWord_2292629
  simp only [CollatzResearch.WordTrace]
  refine ⟨83619049211204157705432941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55746032807469438470288627 83619049211204157705432941)
  ·
    refine ⟨31357143454201559139537353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83619049211204157705432941 31357143454201559139537353)
    ·
      refine ⟨23517857590651169354653015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31357143454201559139537353 23517857590651169354653015)
      ·
        refine ⟨35276786385976754031979523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23517857590651169354653015 35276786385976754031979523)
        ·
          refine ⟨52915179578965131047969285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35276786385976754031979523 52915179578965131047969285)
          ·
            refine ⟨9921596171055962071494241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52915179578965131047969285 9921596171055962071494241)
            ·
              refine ⟨7441197128291971553620681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921596171055962071494241 7441197128291971553620681)
              ·
                refine ⟨5580897846218978665215511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441197128291971553620681 5580897846218978665215511)
                ·
                  refine ⟨8371346769328467997823267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580897846218978665215511 8371346769328467997823267)
                  ·
                    refine ⟨12557020153992701996734901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8371346769328467997823267 12557020153992701996734901)
                    ·
                      refine ⟨1177220639436815812193897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12557020153992701996734901 1177220639436815812193897)
                      ·
                        rfl

theorem cell23_2292629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2292629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292629 prefixEnd_2292629 := by exact prefixLift 2292629
  have htrace : WordTrace (prefixWord ++ tailWord_2292629) baseStart_2292629 baseEnd_2292629 := by
    simpa [prefixWord, tailWord_2292629, baseEnd_2292629] using wordTrace_append hprefix tailTrace_2292629
  have hstable : (prefixWord ++ tailWord_2292629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292629).length < 2 ^ (prefixWord ++ tailWord_2292629).sum := by decide
  have hdescent : baseEnd_2292629 < baseStart_2292629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292639 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2292639 : Nat := 118140960795 + 2292639 * 2 ^ 59
def prefixEnd_2292639 : Nat := 4983230072969 + 3 ^ 40 * 2292639 * 2
def baseEnd_2292639 : Nat := 1177225774243360773068851

theorem tailTrace_2292639 : CollatzResearch.WordTrace tailWord_2292639 prefixEnd_2292639 1177225774243360773068851 := by
  unfold tailWord_2292639
  simp only [CollatzResearch.WordTrace]
  refine ⟨83619413941167929413296971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55746275960778619608864647 83619413941167929413296971)
  ·
    refine ⟨125429120911751894119945457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83619413941167929413296971 125429120911751894119945457)
    ·
      refine ⟨94071840683813920589959093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125429120911751894119945457 94071840683813920589959093)
      ·
        refine ⟨8819235064107555055308665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94071840683813920589959093 8819235064107555055308665)
        ·
          refine ⟨6614426298080666291481499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8819235064107555055308665 6614426298080666291481499)
          ·
            refine ⟨9921639447120999437222249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614426298080666291481499 9921639447120999437222249)
            ·
              refine ⟨7441229585340749577916687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921639447120999437222249 7441229585340749577916687)
              ·
                refine ⟨11161844378011124366875031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441229585340749577916687 11161844378011124366875031)
                ·
                  refine ⟨16742766567016686550312547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161844378011124366875031 16742766567016686550312547)
                  ·
                    refine ⟨25114149850525029825468821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16742766567016686550312547 25114149850525029825468821)
                    ·
                      refine ⟨1177225774243360773068851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25114149850525029825468821 1177225774243360773068851)
                      ·
                        rfl

theorem cell23_2292639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2292639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292639 prefixEnd_2292639 := by exact prefixLift 2292639
  have htrace : WordTrace (prefixWord ++ tailWord_2292639) baseStart_2292639 baseEnd_2292639 := by
    simpa [prefixWord, tailWord_2292639, baseEnd_2292639] using wordTrace_append hprefix tailTrace_2292639
  have hstable : (prefixWord ++ tailWord_2292639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292639).length < 2 ^ (prefixWord ++ tailWord_2292639).sum := by decide
  have hdescent : baseEnd_2292639 < baseStart_2292639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2292652 : Nat := 118140960795 + 2292652 * 2 ^ 59
def prefixEnd_2292652 : Nat := 4983230072969 + 3 ^ 40 * 2292652 * 2
def baseEnd_2292652 : Nat := 1177232449491869222206291

theorem tailTrace_2292652 : CollatzResearch.WordTrace tailWord_2292652 prefixEnd_2292652 1177232449491869222206291 := by
  unfold tailWord_2292652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41809944045060416316760105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55746592060080555089013473 41809944045060416316760105)
  ·
    refine ⟨31357458033795312237570079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41809944045060416316760105 31357458033795312237570079)
    ·
      refine ⟨47036187050692968356355119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31357458033795312237570079 47036187050692968356355119)
      ·
        refine ⟨70554280576039452534532679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47036187050692968356355119 70554280576039452534532679)
        ·
          refine ⟨105831420864059178801799019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70554280576039452534532679 105831420864059178801799019)
          ·
            refine ⟨158747131296088768202698529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105831420864059178801799019 158747131296088768202698529)
            ·
              refine ⟨119060348472066576152023897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158747131296088768202698529 119060348472066576152023897)
              ·
                refine ⟨89295261354049932114017923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119060348472066576152023897 89295261354049932114017923)
                ·
                  refine ⟨133942892031074898171026885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89295261354049932114017923 133942892031074898171026885)
                  ·
                    refine ⟨25114292255826543407067541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133942892031074898171026885 25114292255826543407067541)
                    ·
                      refine ⟨1177232449491869222206291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25114292255826543407067541 1177232449491869222206291)
                      ·
                        rfl

theorem cell23_2292652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2292652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292652 prefixEnd_2292652 := by exact prefixLift 2292652
  have htrace : WordTrace (prefixWord ++ tailWord_2292652) baseStart_2292652 baseEnd_2292652 := by
    simpa [prefixWord, tailWord_2292652, baseEnd_2292652] using wordTrace_append hprefix tailTrace_2292652
  have hstable : (prefixWord ++ tailWord_2292652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292652).length < 2 ^ (prefixWord ++ tailWord_2292652).sum := by decide
  have hdescent : baseEnd_2292652 < baseStart_2292652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292653 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2292653 : Nat := 118140960795 + 2292653 * 2 ^ 59
def prefixEnd_2292653 : Nat := 4983230072969 + 3 ^ 40 * 2292653 * 2
def baseEnd_2292653 : Nat := 392410987657507906097929

theorem tailTrace_2292653 : CollatzResearch.WordTrace tailWord_2292653 prefixEnd_2292653 392410987657507906097929 := by
  unfold tailWord_2292653
  simp only [CollatzResearch.WordTrace]
  refine ⟨83619924563117209804306613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55746616375411473202871075 83619924563117209804306613)
  ·
    refine ⟨7839367927792238419153745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83619924563117209804306613 7839367927792238419153745)
    ·
      refine ⟨5879525945844178814365309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7839367927792238419153745 5879525945844178814365309)
      ·
        refine ⟨2204822229691567055386991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5879525945844178814365309 2204822229691567055386991)
        ·
          refine ⟨3307233344537350583080487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204822229691567055386991 3307233344537350583080487)
          ·
            refine ⟨4960850016806025874620731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307233344537350583080487 4960850016806025874620731)
            ·
              refine ⟨7441275025209038811931097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960850016806025874620731 7441275025209038811931097)
              ·
                refine ⟨5580956268906779108948323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441275025209038811931097 5580956268906779108948323)
                ·
                  refine ⟨8371434403360168663422485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580956268906779108948323 8371434403360168663422485)
                  ·
                    refine ⟨392410987657507906097929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8371434403360168663422485 392410987657507906097929)
                    ·
                      rfl

theorem cell23_2292653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2292653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292653 prefixEnd_2292653 := by exact prefixLift 2292653
  have htrace : WordTrace (prefixWord ++ tailWord_2292653) baseStart_2292653 baseEnd_2292653 := by
    simpa [prefixWord, tailWord_2292653, baseEnd_2292653] using wordTrace_append hprefix tailTrace_2292653
  have hstable : (prefixWord ++ tailWord_2292653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292653).length < 2 ^ (prefixWord ++ tailWord_2292653).sum := by decide
  have hdescent : baseEnd_2292653 < baseStart_2292653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292693 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2292693 : Nat := 118140960795 + 2292693 * 2 ^ 59
def prefixEnd_2292693 : Nat := 4983230072969 + 3 ^ 40 * 2292693 * 2
def baseEnd_2292693 : Nat := 1177253502198703561793603

theorem tailTrace_2292693 : CollatzResearch.WordTrace tailWord_2292693 prefixEnd_2292693 1177253502198703561793603 := by
  unfold tailWord_2292693
  simp only [CollatzResearch.WordTrace]
  refine ⟨83621383482972296635762733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55747588988648197757175155 83621383482972296635762733)
  ·
    refine ⟨31358018806114611238411025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83621383482972296635762733 31358018806114611238411025)
    ·
      refine ⟨23518514104585958428808269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31358018806114611238411025 23518514104585958428808269)
      ·
        refine ⟨8819442789219734410803101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23518514104585958428808269 8819442789219734410803101)
        ·
          refine ⟨3307291045957400404051163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8819442789219734410803101 3307291045957400404051163)
          ·
            refine ⟨4960936568936100606076745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307291045957400404051163 4960936568936100606076745)
            ·
              refine ⟨3720702426702075454557559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960936568936100606076745 3720702426702075454557559)
              ·
                refine ⟨5581053640053113181836339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720702426702075454557559 5581053640053113181836339)
                ·
                  refine ⟨8371580460079669772754509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5581053640053113181836339 8371580460079669772754509)
                  ·
                    refine ⟨3139342672529876164782941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8371580460079669772754509 3139342672529876164782941)
                    ·
                      refine ⟨1177253502198703561793603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3139342672529876164782941 1177253502198703561793603)
                      ·
                        rfl

theorem cell23_2292693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2292693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292693 prefixEnd_2292693 := by exact prefixLift 2292693
  have htrace : WordTrace (prefixWord ++ tailWord_2292693) baseStart_2292693 baseEnd_2292693 := by
    simpa [prefixWord, tailWord_2292693, baseEnd_2292693] using wordTrace_append hprefix tailTrace_2292693
  have hstable : (prefixWord ++ tailWord_2292693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292693).length < 2 ^ (prefixWord ++ tailWord_2292693).sum := by decide
  have hdescent : baseEnd_2292693 < baseStart_2292693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292726 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2292726 : Nat := 118140960795 + 2292726 * 2 ^ 59
def prefixEnd_2292726 : Nat := 4983230072969 + 3 ^ 40 * 2292726 * 2
def baseEnd_2292726 : Nat := 392423482353433977560317

theorem tailTrace_2292726 : CollatzResearch.WordTrace tailWord_2292726 prefixEnd_2292726 392423482353433977560317 := by
  unfold tailWord_2292726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226411693240796454482127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55748391394568495514476021 5226411693240796454482127)
  ·
    refine ⟨7839617539861194681723191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5226411693240796454482127 7839617539861194681723191)
    ·
      refine ⟨11759426309791792022584787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7839617539861194681723191 11759426309791792022584787)
      ·
        refine ⟨17639139464687688033877181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11759426309791792022584787 17639139464687688033877181)
        ·
          refine ⟨6614677299257883012703943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17639139464687688033877181 6614677299257883012703943)
          ·
            refine ⟨9922015948886824519055915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614677299257883012703943 9922015948886824519055915)
            ·
              refine ⟨14883023923330236778583873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922015948886824519055915 14883023923330236778583873)
              ·
                refine ⟨11162267942497677583937905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883023923330236778583873 11162267942497677583937905)
                ·
                  refine ⟨8371700956873258187953429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11162267942497677583937905 8371700956873258187953429)
                  ·
                    refine ⟨392423482353433977560317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8371700956873258187953429 392423482353433977560317)
                    ·
                      rfl

theorem cell23_2292726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2292726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292726 prefixEnd_2292726 := by exact prefixLift 2292726
  have htrace : WordTrace (prefixWord ++ tailWord_2292726) baseStart_2292726 baseEnd_2292726 := by
    simpa [prefixWord, tailWord_2292726, baseEnd_2292726] using wordTrace_append hprefix tailTrace_2292726
  have hstable : (prefixWord ++ tailWord_2292726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292726).length < 2 ^ (prefixWord ++ tailWord_2292726).sum := by decide
  have hdescent : baseEnd_2292726 < baseStart_2292726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292729 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2292729 : Nat := 118140960795 + 2292729 * 2 ^ 59
def prefixEnd_2292729 : Nat := 4983230072969 + 3 ^ 40 * 2292729 * 2
def baseEnd_2292729 : Nat := 1177271987502265420943437

theorem tailTrace_2292729 : CollatzResearch.WordTrace tailWord_2292729 prefixEnd_2292729 1177271987502265420943437 := by
  unfold tailWord_2292729
  simp only [CollatzResearch.WordTrace]
  refine ⟨83622696510841874784073241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55748464340561249856048827 83622696510841874784073241)
  ·
    refine ⟨62717022383131406088054931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83622696510841874784073241 62717022383131406088054931)
    ·
      refine ⟨94075533574697109132082397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62717022383131406088054931 94075533574697109132082397)
      ·
        refine ⟨35278325090511415924530899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94075533574697109132082397 35278325090511415924530899)
        ·
          refine ⟨52917487635767123886796349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35278325090511415924530899 52917487635767123886796349)
          ·
            refine ⟨19844057863412671457548631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52917487635767123886796349 19844057863412671457548631)
            ·
              refine ⟨29766086795119007186322947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19844057863412671457548631 29766086795119007186322947)
              ·
                refine ⟨44649130192678510779484421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29766086795119007186322947 44649130192678510779484421)
                ·
                  refine ⟨8371711911127220771153329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44649130192678510779484421 8371711911127220771153329)
                  ·
                    refine ⟨6278783933345415578364997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8371711911127220771153329 6278783933345415578364997)
                    ·
                      refine ⟨1177271987502265420943437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6278783933345415578364997 1177271987502265420943437)
                      ·
                        rfl

theorem cell23_2292729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2292729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292729 prefixEnd_2292729 := by exact prefixLift 2292729
  have htrace : WordTrace (prefixWord ++ tailWord_2292729) baseStart_2292729 baseEnd_2292729 := by
    simpa [prefixWord, tailWord_2292729, baseEnd_2292729] using wordTrace_append hprefix tailTrace_2292729
  have hstable : (prefixWord ++ tailWord_2292729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292729).length < 2 ^ (prefixWord ++ tailWord_2292729).sum := by decide
  have hdescent : baseEnd_2292729 < baseStart_2292729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292746 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2292746 : Nat := 118140960795 + 2292746 * 2 ^ 59
def prefixEnd_2292746 : Nat := 4983230072969 + 3 ^ 40 * 2292746 * 2
def baseEnd_2292746 : Nat := 1177280716673391854430859

theorem tailTrace_2292746 : CollatzResearch.WordTrace tailWord_2292746 prefixEnd_2292746 1177280716673391854430859 := by
  unfold tailWord_2292746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20905829137945071671860523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55748877701186857791628061 20905829137945071671860523)
  ·
    refine ⟨31358743706917607507790785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20905829137945071671860523 31358743706917607507790785)
    ·
      refine ⟨23519057780188205630843089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31358743706917607507790785 23519057780188205630843089)
      ·
        refine ⟨17639293335141154223132317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23519057780188205630843089 17639293335141154223132317)
        ·
          refine ⟨6614735000677932833674619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17639293335141154223132317 6614735000677932833674619)
          ·
            refine ⟨9922102501016899250511929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614735000677932833674619 9922102501016899250511929)
            ·
              refine ⟨7441576875762674437883947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9922102501016899250511929 7441576875762674437883947)
              ·
                refine ⟨11162365313644011656825921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441576875762674437883947 11162365313644011656825921)
                ·
                  refine ⟨8371773985233008742619441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11162365313644011656825921 8371773985233008742619441)
                  ·
                    refine ⟨6278830488924756556964581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8371773985233008742619441 6278830488924756556964581)
                    ·
                      refine ⟨1177280716673391854430859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6278830488924756556964581 1177280716673391854430859)
                      ·
                        rfl

theorem cell23_2292746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2292746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292746 prefixEnd_2292746 := by exact prefixLift 2292746
  have htrace : WordTrace (prefixWord ++ tailWord_2292746) baseStart_2292746 baseEnd_2292746 := by
    simpa [prefixWord, tailWord_2292746, baseEnd_2292746] using wordTrace_append hprefix tailTrace_2292746
  have hstable : (prefixWord ++ tailWord_2292746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292746).length < 2 ^ (prefixWord ++ tailWord_2292746).sum := by decide
  have hdescent : baseEnd_2292746 < baseStart_2292746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292750 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2292750 : Nat := 118140960795 + 2292750 * 2 ^ 59
def prefixEnd_2292750 : Nat := 4983230072969 + 3 ^ 40 * 2292750 * 2
def baseEnd_2292750 : Nat := 1177282770596009838780841

theorem tailTrace_2292750 : CollatzResearch.WordTrace tailWord_2292750 prefixEnd_2292750 1177282770596009838780841 := by
  unfold tailWord_2292750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452932805470724421323463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55748974962510530247058469 10452932805470724421323463)
  ·
    refine ⟨15679399208206086631985195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452932805470724421323463 15679399208206086631985195)
    ·
      refine ⟨23519098812309129947977793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15679399208206086631985195 23519098812309129947977793)
      ·
        refine ⟨17639324109231847460983345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23519098812309129947977793 17639324109231847460983345)
        ·
          refine ⟨13229493081923885595737509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17639324109231847460983345 13229493081923885595737509)
          ·
            refine ⟨2480529952860728549200783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13229493081923885595737509 2480529952860728549200783)
            ·
              refine ⟨3720794929291092823801175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480529952860728549200783 3720794929291092823801175)
              ·
                refine ⟨5581192393936639235701763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720794929291092823801175 5581192393936639235701763)
                ·
                  refine ⟨8371788590904958853552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5581192393936639235701763 8371788590904958853552645)
                  ·
                    refine ⟨1569710360794679785041121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8371788590904958853552645 1569710360794679785041121)
                    ·
                      refine ⟨1177282770596009838780841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569710360794679785041121 1177282770596009838780841)
                      ·
                        rfl

theorem cell23_2292750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2292750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292750 prefixEnd_2292750 := by exact prefixLift 2292750
  have htrace : WordTrace (prefixWord ++ tailWord_2292750) baseStart_2292750 baseEnd_2292750 := by
    simpa [prefixWord, tailWord_2292750, baseEnd_2292750] using wordTrace_append hprefix tailTrace_2292750
  have hstable : (prefixWord ++ tailWord_2292750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292750).length < 2 ^ (prefixWord ++ tailWord_2292750).sum := by decide
  have hdescent : baseEnd_2292750 < baseStart_2292750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292779 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_2292779 : Nat := 118140960795 + 2292779 * 2 ^ 59
def prefixEnd_2292779 : Nat := 4983230072969 + 3 ^ 40 * 2292779 * 2
def baseEnd_2292779 : Nat := 1177297661534990225318207

theorem tailTrace_2292779 : CollatzResearch.WordTrace tailWord_2292779 prefixEnd_2292779 1177297661534990225318207 := by
  unfold tailWord_2292779
  simp only [CollatzResearch.WordTrace]
  refine ⟨83624520160660733323393391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55749680107107155548928927 83624520160660733323393391)
  ·
    refine ⟨125436780240991099985090087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83624520160660733323393391 125436780240991099985090087)
    ·
      refine ⟨188155170361486649977635131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125436780240991099985090087 188155170361486649977635131)
      ·
        refine ⟨282232755542229974966452697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188155170361486649977635131 282232755542229974966452697)
        ·
          refine ⟨211674566656672481224839523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282232755542229974966452697 211674566656672481224839523)
          ·
            refine ⟨317511849985008721837259285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211674566656672481224839523 317511849985008721837259285)
            ·
              refine ⟨14883367968047283836121529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 317511849985008721837259285 14883367968047283836121529)
              ·
                refine ⟨11162525976035462877091147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883367968047283836121529 11162525976035462877091147)
                ·
                  refine ⟨16743788964053194315636721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162525976035462877091147 16743788964053194315636721)
                  ·
                    refine ⟨12557841723039895736727541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16743788964053194315636721 12557841723039895736727541)
                    ·
                      refine ⟨1177297661534990225318207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12557841723039895736727541 1177297661534990225318207)
                      ·
                        rfl

theorem cell23_2292779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_2292779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292779 prefixEnd_2292779 := by exact prefixLift 2292779
  have htrace : WordTrace (prefixWord ++ tailWord_2292779) baseStart_2292779 baseEnd_2292779 := by
    simpa [prefixWord, tailWord_2292779, baseEnd_2292779] using wordTrace_append hprefix tailTrace_2292779
  have hstable : (prefixWord ++ tailWord_2292779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292779).length < 2 ^ (prefixWord ++ tailWord_2292779).sum := by decide
  have hdescent : baseEnd_2292779 < baseStart_2292779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292786 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2292786 : Nat := 118140960795 + 2292786 * 2 ^ 59
def prefixEnd_2292786 : Nat := 4983230072969 + 3 ^ 40 * 2292786 * 2
def baseEnd_2292786 : Nat := 392433751966523899310225

theorem tailTrace_2292786 : CollatzResearch.WordTrace tailWord_2292786 prefixEnd_2292786 392433751966523899310225 := by
  unfold tailWord_2292786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906193867908843379724553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55749850314423582345932141 20906193867908843379724553)
  ·
    refine ⟨15679645400931632534793415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20906193867908843379724553 15679645400931632534793415)
    ·
      refine ⟨23519468101397448802190123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15679645400931632534793415 23519468101397448802190123)
      ·
        refine ⟨35279202152096173203285185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23519468101397448802190123 35279202152096173203285185)
        ·
          refine ⟨26459401614072129902463889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35279202152096173203285185 26459401614072129902463889)
          ·
            refine ⟨19844551210554097426847917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26459401614072129902463889 19844551210554097426847917)
            ·
              refine ⟨7441706703957786535067969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19844551210554097426847917 7441706703957786535067969)
              ·
                refine ⟨5581280027968339901300977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441706703957786535067969 5581280027968339901300977)
                ·
                  refine ⟨4185960020976254925975733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5581280027968339901300977 4185960020976254925975733)
                  ·
                    refine ⟨392433751966523899310225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4185960020976254925975733 392433751966523899310225)
                    ·
                      rfl

theorem cell23_2292786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2292786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292786 prefixEnd_2292786 := by exact prefixLift 2292786
  have htrace : WordTrace (prefixWord ++ tailWord_2292786) baseStart_2292786 baseEnd_2292786 := by
    simpa [prefixWord, tailWord_2292786, baseEnd_2292786] using wordTrace_append hprefix tailTrace_2292786
  have hstable : (prefixWord ++ tailWord_2292786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292786).length < 2 ^ (prefixWord ++ tailWord_2292786).sum := by decide
  have hdescent : baseEnd_2292786 < baseStart_2292786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292796 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2292796 : Nat := 118140960795 + 2292796 * 2 ^ 59
def prefixEnd_2292796 : Nat := 4983230072969 + 3 ^ 40 * 2292796 * 2
def baseEnd_2292796 : Nat := 1177306390706116658805629

theorem tailTrace_2292796 : CollatzResearch.WordTrace tailWord_2292796 prefixEnd_2292796 1177306390706116658805629 := by
  unfold tailWord_2292796
  simp only [CollatzResearch.WordTrace]
  refine ⟨41812570100799572613381121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55750093467732763484508161 41812570100799572613381121)
  ·
    refine ⟨31359427575599679460035841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41812570100799572613381121 31359427575599679460035841)
    ·
      refine ⟨23519570681699759595026881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31359427575599679460035841 23519570681699759595026881)
      ·
        refine ⟨17639678011274819696270161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23519570681699759595026881 17639678011274819696270161)
        ·
          refine ⟨13229758508456114772202621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17639678011274819696270161 13229758508456114772202621)
          ·
            refine ⟨4961159440671043039575983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13229758508456114772202621 4961159440671043039575983)
            ·
              refine ⟨7441739161006564559363975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961159440671043039575983 7441739161006564559363975)
              ·
                refine ⟨11162608741509846839045963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441739161006564559363975 11162608741509846839045963)
                ·
                  refine ⟨16743913112264770258568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162608741509846839045963 16743913112264770258568945)
                  ·
                    refine ⟨12557934834198577693926709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16743913112264770258568945 12557934834198577693926709)
                    ·
                      refine ⟨1177306390706116658805629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12557934834198577693926709 1177306390706116658805629)
                      ·
                        rfl

theorem cell23_2292796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2292796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292796 prefixEnd_2292796 := by exact prefixLift 2292796
  have htrace : WordTrace (prefixWord ++ tailWord_2292796) baseStart_2292796 baseEnd_2292796 := by
    simpa [prefixWord, tailWord_2292796, baseEnd_2292796] using wordTrace_append hprefix tailTrace_2292796
  have hstable : (prefixWord ++ tailWord_2292796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292796).length < 2 ^ (prefixWord ++ tailWord_2292796).sum := by decide
  have hdescent : baseEnd_2292796 < baseStart_2292796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292801 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2292801 : Nat := 118140960795 + 2292801 * 2 ^ 59
def prefixEnd_2292801 : Nat := 4983230072969 + 3 ^ 40 * 2292801 * 2
def baseEnd_2292801 : Nat := 1177308958109389139243107

theorem tailTrace_2292801 : CollatzResearch.WordTrace tailWord_2292801 prefixEnd_2292801 1177308958109389139243107 := by
  unfold tailWord_2292801
  simp only [CollatzResearch.WordTrace]
  refine ⟨83625322566581031080694257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55750215044387354053796171 83625322566581031080694257)
  ·
    refine ⟨62718991924935773310520693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83625322566581031080694257 62718991924935773310520693)
    ·
      refine ⟨5879905492962728747861315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62718991924935773310520693 5879905492962728747861315)
      ·
        refine ⟨8819858239444093121791973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5879905492962728747861315 8819858239444093121791973)
        ·
          refine ⟨1653723419895767460335995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8819858239444093121791973 1653723419895767460335995)
          ·
            refine ⟨2480585129843651190503993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653723419895767460335995 2480585129843651190503993)
            ·
              refine ⟨1860438847382738392877995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480585129843651190503993 1860438847382738392877995)
              ·
                refine ⟨2790658271074107589316993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860438847382738392877995 2790658271074107589316993)
                ·
                  refine ⟨2092993703305580691987745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790658271074107589316993 2092993703305580691987745)
                  ·
                    refine ⟨1569745277479185518990809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092993703305580691987745 1569745277479185518990809)
                    ·
                      refine ⟨1177308958109389139243107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1569745277479185518990809 1177308958109389139243107)
                      ·
                        rfl

theorem cell23_2292801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2292801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292801 prefixEnd_2292801 := by exact prefixLift 2292801
  have htrace : WordTrace (prefixWord ++ tailWord_2292801) baseStart_2292801 baseEnd_2292801 := by
    simpa [prefixWord, tailWord_2292801, baseEnd_2292801] using wordTrace_append hprefix tailTrace_2292801
  have hstable : (prefixWord ++ tailWord_2292801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292801).length < 2 ^ (prefixWord ++ tailWord_2292801).sum := by decide
  have hdescent : baseEnd_2292801 < baseStart_2292801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292816 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_2292816 : Nat := 118140960795 + 2292816 * 2 ^ 59
def prefixEnd_2292816 : Nat := 4983230072969 + 3 ^ 40 * 2292816 * 2
def baseEnd_2292816 : Nat := 392438886773068860185179

theorem tailTrace_2292816 : CollatzResearch.WordTrace tailWord_2292816 prefixEnd_2292816 392438886773068860185179 := by
  unfold tailWord_2292816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41812934830763344321245151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55750579774351125761660201 41812934830763344321245151)
  ·
    refine ⟨62719402246145016481867727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41812934830763344321245151 62719402246145016481867727)
    ·
      refine ⟨94079103369217524722801591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62719402246145016481867727 94079103369217524722801591)
      ·
        refine ⟨141118655053826287084202387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94079103369217524722801591 141118655053826287084202387)
        ·
          refine ⟨211677982580739430626303581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141118655053826287084202387 211677982580739430626303581)
          ·
            refine ⟨79379243467777286484863843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211677982580739430626303581 79379243467777286484863843)
            ·
              refine ⟨119068865201665929727295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79379243467777286484863843 119068865201665929727295765)
              ·
                refine ⟨5581353056328090455966989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119068865201665929727295765 5581353056328090455966989)
                ·
                  refine ⟨2093007396123033920987621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5581353056328090455966989 2093007396123033920987621)
                  ·
                    refine ⟨392438886773068860185179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093007396123033920987621 392438886773068860185179)
                    ·
                      rfl

theorem cell23_2292816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_2292816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292816 prefixEnd_2292816 := by exact prefixLift 2292816
  have htrace : WordTrace (prefixWord ++ tailWord_2292816) baseStart_2292816 baseEnd_2292816 := by
    simpa [prefixWord, tailWord_2292816, baseEnd_2292816] using wordTrace_append hprefix tailTrace_2292816
  have hstable : (prefixWord ++ tailWord_2292816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292816).length < 2 ^ (prefixWord ++ tailWord_2292816).sum := by decide
  have hdescent : baseEnd_2292816 < baseStart_2292816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292819 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_2292819 : Nat := 118140960795 + 2292819 * 2 ^ 59
def prefixEnd_2292819 : Nat := 4983230072969 + 3 ^ 40 * 2292819 * 2
def baseEnd_2292819 : Nat := 1177318200761170068818023

theorem tailTrace_2292819 : CollatzResearch.WordTrace tailWord_2292819 prefixEnd_2292819 1177318200761170068818023 := by
  unfold tailWord_2292819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83625979080515820154849511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55750652720343880103233007 83625979080515820154849511)
  ·
    refine ⟨125438968620773730232274267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83625979080515820154849511 125438968620773730232274267)
    ·
      refine ⟨188158452931160595348411401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125438968620773730232274267 188158452931160595348411401)
      ·
        refine ⟨141118839698370446511308551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188158452931160595348411401 141118839698370446511308551)
        ·
          refine ⟨211678259547555669766962827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141118839698370446511308551 211678259547555669766962827)
          ·
            refine ⟨317517389321333504650444241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211678259547555669766962827 317517389321333504650444241)
            ·
              refine ⟨238138041991000128487833181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317517389321333504650444241 238138041991000128487833181)
              ·
                refine ⟨89301765746625048182937443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238138041991000128487833181 89301765746625048182937443)
                ·
                  refine ⟨133952648619937572274406165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89301765746625048182937443 133952648619937572274406165)
                  ·
                    refine ⟨6279030404059573700362789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133952648619937572274406165 6279030404059573700362789)
                    ·
                      refine ⟨1177318200761170068818023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6279030404059573700362789 1177318200761170068818023)
                      ·
                        rfl

theorem cell23_2292819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_2292819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292819 prefixEnd_2292819 := by exact prefixLift 2292819
  have htrace : WordTrace (prefixWord ++ tailWord_2292819) baseStart_2292819 baseEnd_2292819 := by
    simpa [prefixWord, tailWord_2292819, baseEnd_2292819] using wordTrace_append hprefix tailTrace_2292819
  have hstable : (prefixWord ++ tailWord_2292819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292819).length < 2 ^ (prefixWord ++ tailWord_2292819).sum := by decide
  have hdescent : baseEnd_2292819 < baseStart_2292819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292830 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2292830 : Nat := 118140960795 + 2292830 * 2 ^ 59
def prefixEnd_2292830 : Nat := 4983230072969 + 3 ^ 40 * 2292830 * 2
def baseEnd_2292830 : Nat := 1177323849048369525780473

theorem tailTrace_2292830 : CollatzResearch.WordTrace tailWord_2292830 prefixEnd_2292830 1177323849048369525780473 := by
  unfold tailWord_2292830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10453297535434496129187493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55750920188983979355666629 10453297535434496129187493)
  ·
    refine ⟨1959993287893968024222655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10453297535434496129187493 1959993287893968024222655)
    ·
      refine ⟨2939989931840952036333983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959993287893968024222655 2939989931840952036333983)
      ·
        refine ⟨4409984897761428054500975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939989931840952036333983 4409984897761428054500975)
        ·
          refine ⟨6614977346642142081751463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409984897761428054500975 6614977346642142081751463)
          ·
            refine ⟨9922466019963213122627195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614977346642142081751463 9922466019963213122627195)
            ·
              refine ⟨14883699029944819683940793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922466019963213122627195 14883699029944819683940793)
              ·
                refine ⟨11162774272458614762955595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883699029944819683940793 11162774272458614762955595)
                ·
                  refine ⟨16744161408687922144433393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162774272458614762955595 16744161408687922144433393)
                  ·
                    refine ⟨12558121056515941608325045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16744161408687922144433393 12558121056515941608325045)
                    ·
                      refine ⟨1177323849048369525780473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12558121056515941608325045 1177323849048369525780473)
                      ·
                        rfl

theorem cell23_2292830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2292830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292830 prefixEnd_2292830 := by exact prefixLift 2292830
  have htrace : WordTrace (prefixWord ++ tailWord_2292830) baseStart_2292830 baseEnd_2292830 := by
    simpa [prefixWord, tailWord_2292830, baseEnd_2292830] using wordTrace_append hprefix tailTrace_2292830
  have hstable : (prefixWord ++ tailWord_2292830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292830).length < 2 ^ (prefixWord ++ tailWord_2292830).sum := by decide
  have hdescent : baseEnd_2292830 < baseStart_2292830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
