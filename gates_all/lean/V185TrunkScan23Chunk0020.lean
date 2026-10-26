import V185TrunkScan23Chunk0019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_118389 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_118389 : Nat := 118140960795 + 118389 * 2 ^ 59
def prefixEnd_118389 : Nat := 4983230072969 + 3 ^ 40 * 118389 * 2
def baseEnd_118389 : Nat := 20263487068414178731015

theorem tailTrace_118389 : CollatzResearch.WordTrace tailWord_118389 prefixEnd_118389 20263487068414178731015 := by
  unfold tailWord_118389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318001568104347076574221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878667712069564717716147 4318001568104347076574221)
  ·
    refine ⟨1619250588039130153715333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4318001568104347076574221 1619250588039130153715333)
    ·
      refine ⟨303609485257336903821625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1619250588039130153715333 303609485257336903821625)
      ·
        refine ⟨227707113943002677866219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303609485257336903821625 227707113943002677866219)
        ·
          refine ⟨341560670914504016799329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227707113943002677866219 341560670914504016799329)
          ·
            refine ⟨256170503185878012599497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341560670914504016799329 256170503185878012599497)
            ·
              refine ⟨192127877389408509449623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256170503185878012599497 192127877389408509449623)
              ·
                refine ⟨288191816084112764174435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192127877389408509449623 288191816084112764174435)
                ·
                  refine ⟨432287724126169146261653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288191816084112764174435 432287724126169146261653)
                  ·
                    refine ⟨20263487068414178731015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 432287724126169146261653 20263487068414178731015)
                    ·
                      rfl

theorem cell23_118389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_118389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118389 prefixEnd_118389 := by exact prefixLift 118389
  have htrace : WordTrace (prefixWord ++ tailWord_118389) baseStart_118389 baseEnd_118389 := by
    simpa [prefixWord, tailWord_118389, baseEnd_118389] using wordTrace_append hprefix tailTrace_118389
  have hstable : (prefixWord ++ tailWord_118389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118389).length < 2 ^ (prefixWord ++ tailWord_118389).sum := by decide
  have hdescent : baseEnd_118389 < baseStart_118389 := by decide
  rcases family_descends (prefixWord ++ tailWord_118389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118412 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_118412 : Nat := 118140960795 + 118412 * 2 ^ 59
def prefixEnd_118412 : Nat := 4983230072969 + 3 ^ 40 * 118412 * 2
def baseEnd_118412 : Nat := 60802271260295946205439

theorem tailTrace_118412 : CollatzResearch.WordTrace tailWord_118412 prefixEnd_118412 60802271260295946205439 := by
  unfold tailWord_118412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159420223510511002330745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2879226964680681336440993 2159420223510511002330745)
  ·
    refine ⟨1619565167632883251748059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2159420223510511002330745 1619565167632883251748059)
    ·
      refine ⟨2429347751449324877622089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619565167632883251748059 2429347751449324877622089)
      ·
        refine ⟨1822010813586993658216567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429347751449324877622089 1822010813586993658216567)
        ·
          refine ⟨2733016220380490487324851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822010813586993658216567 2733016220380490487324851)
          ·
            refine ⟨4099524330570735730987277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733016220380490487324851 4099524330570735730987277)
            ·
              refine ⟨1537321623964025899120229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4099524330570735730987277 1537321623964025899120229)
              ·
                refine ⟨288247804493254856085043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1537321623964025899120229 288247804493254856085043)
                ·
                  refine ⟨432371706739882284127565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288247804493254856085043 432371706739882284127565)
                  ·
                    refine ⟨162139390027455856547837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432371706739882284127565 162139390027455856547837)
                    ·
                      refine ⟨60802271260295946205439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162139390027455856547837 60802271260295946205439)
                      ·
                        rfl

theorem cell23_118412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_118412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118412 prefixEnd_118412 := by exact prefixLift 118412
  have htrace : WordTrace (prefixWord ++ tailWord_118412) baseStart_118412 baseEnd_118412 := by
    simpa [prefixWord, tailWord_118412, baseEnd_118412] using wordTrace_append hprefix tailTrace_118412
  have hstable : (prefixWord ++ tailWord_118412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118412).length < 2 ^ (prefixWord ++ tailWord_118412).sum := by decide
  have hdescent : baseEnd_118412 < baseStart_118412 := by decide
  rcases family_descends (prefixWord ++ tailWord_118412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118425 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_118425 : Nat := 118140960795 + 118425 * 2 ^ 59
def prefixEnd_118425 : Nat := 4983230072969 + 3 ^ 40 * 118425 * 2
def baseEnd_118425 : Nat := 60808946508804395342879

theorem tailTrace_118425 : CollatzResearch.WordTrace tailWord_118425 prefixEnd_118425 60808946508804395342879 := by
  unfold tailWord_118425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319314595973925224884729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879543063982616816589819 4319314595973925224884729)
  ·
    refine ⟨3239485946980443918663547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4319314595973925224884729 3239485946980443918663547)
    ·
      refine ⟨4859228920470665877995321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3239485946980443918663547 4859228920470665877995321)
      ·
        refine ⟨3644421690352999408496491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4859228920470665877995321 3644421690352999408496491)
        ·
          refine ⟨5466632535529499112744737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644421690352999408496491 5466632535529499112744737)
          ·
            refine ⟨4099974401647124334558553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5466632535529499112744737 4099974401647124334558553)
            ·
              refine ⟨3074980801235343250918915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099974401647124334558553 3074980801235343250918915)
              ·
                refine ⟨4612471201853014876378373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074980801235343250918915 4612471201853014876378373)
                ·
                  refine ⟨864838350347440289320945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4612471201853014876378373 864838350347440289320945)
                  ·
                    refine ⟨648628762760580216990709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864838350347440289320945 648628762760580216990709)
                    ·
                      refine ⟨60808946508804395342879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 648628762760580216990709 60808946508804395342879)
                      ·
                        rfl

theorem cell23_118425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_118425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118425 prefixEnd_118425 := by exact prefixLift 118425
  have htrace : WordTrace (prefixWord ++ tailWord_118425) baseStart_118425 baseEnd_118425 := by
    simpa [prefixWord, tailWord_118425, baseEnd_118425] using wordTrace_append hprefix tailTrace_118425
  have hstable : (prefixWord ++ tailWord_118425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118425).length < 2 ^ (prefixWord ++ tailWord_118425).sum := by decide
  have hdescent : baseEnd_118425 < baseStart_118425 := by decide
  rcases family_descends (prefixWord ++ tailWord_118425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118430 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_118430 : Nat := 118140960795 + 118430 * 2 ^ 59
def prefixEnd_118430 : Nat := 4983230072969 + 3 ^ 40 * 118430 * 2
def baseEnd_118430 : Nat := 60811513912076875780357

theorem tailTrace_118430 : CollatzResearch.WordTrace tailWord_118430 prefixEnd_118430 60811513912076875780357 := by
  unfold tailWord_118430
  simp only [CollatzResearch.WordTrace]
  refine ⟨539937120119476384852093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2879664640637207385877829 539937120119476384852093)
  ·
    refine ⟨202476420044803644319535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 539937120119476384852093 202476420044803644319535)
    ·
      refine ⟨303714630067205466479303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202476420044803644319535 303714630067205466479303)
      ·
        refine ⟨455571945100808199718955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303714630067205466479303 455571945100808199718955)
        ·
          refine ⟨683357917651212299578433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455571945100808199718955 683357917651212299578433)
          ·
            refine ⟨512518438238409224683825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683357917651212299578433 512518438238409224683825)
            ·
              refine ⟨384388828678806918512869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512518438238409224683825 384388828678806918512869)
              ·
                refine ⟨72072905377276297221163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384388828678806918512869 72072905377276297221163)
                ·
                  refine ⟨108109358065914445831745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72072905377276297221163 108109358065914445831745)
                  ·
                    refine ⟨81082018549435834373809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108109358065914445831745 81082018549435834373809)
                    ·
                      refine ⟨60811513912076875780357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81082018549435834373809 60811513912076875780357)
                      ·
                        rfl

theorem cell23_118430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_118430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118430 prefixEnd_118430 := by exact prefixLift 118430
  have htrace : WordTrace (prefixWord ++ tailWord_118430) baseStart_118430 baseEnd_118430 := by
    simpa [prefixWord, tailWord_118430, baseEnd_118430] using wordTrace_append hprefix tailTrace_118430
  have hstable : (prefixWord ++ tailWord_118430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118430).length < 2 ^ (prefixWord ++ tailWord_118430).sum := by decide
  have hdescent : baseEnd_118430 < baseStart_118430 := by decide
  rcases family_descends (prefixWord ++ tailWord_118430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118440 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 6]
def baseStart_118440 : Nat := 118140960795 + 118440 * 2 ^ 59
def prefixEnd_118440 : Nat := 4983230072969 + 3 ^ 40 * 118440 * 2
def baseEnd_118440 : Nat := 20272216239540612218437

theorem tailTrace_118440 : CollatzResearch.WordTrace tailWord_118440 prefixEnd_118440 20272216239540612218437 := by
  unfold tailWord_118440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159930845459791393340387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2879907793946388524453849 2159930845459791393340387)
  ·
    refine ⟨3239896268189687090010581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2159930845459791393340387 3239896268189687090010581)
    ·
      refine ⟨75935068785695791172123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3239896268189687090010581 75935068785695791172123)
      ·
        refine ⟨113902603178543686758185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75935068785695791172123 113902603178543686758185)
        ·
          refine ⟨85426952383907765068639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113902603178543686758185 85426952383907765068639)
          ·
            refine ⟨128140428575861647602959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85426952383907765068639 128140428575861647602959)
            ·
              refine ⟨192210642863792471404439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128140428575861647602959 192210642863792471404439)
              ·
                refine ⟨288315964295688707106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192210642863792471404439 288315964295688707106659)
                ·
                  refine ⟨432473946443533060659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288315964295688707106659 432473946443533060659989)
                  ·
                    refine ⟨20272216239540612218437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 432473946443533060659989 20272216239540612218437)
                    ·
                      rfl

theorem cell23_118440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_118440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118440 prefixEnd_118440 := by exact prefixLift 118440
  have htrace : WordTrace (prefixWord ++ tailWord_118440) baseStart_118440 baseEnd_118440 := by
    simpa [prefixWord, tailWord_118440, baseEnd_118440] using wordTrace_append hprefix tailTrace_118440
  have hstable : (prefixWord ++ tailWord_118440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118440).length < 2 ^ (prefixWord ++ tailWord_118440).sum := by decide
  have hdescent : baseEnd_118440 < baseStart_118440 := by decide
  rcases family_descends (prefixWord ++ tailWord_118440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118472 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_118472 : Nat := 118140960795 + 118472 * 2 ^ 59
def prefixEnd_118472 : Nat := 4983230072969 + 3 ^ 40 * 118472 * 2
def baseEnd_118472 : Nat := 60833080099565711455163

theorem tailTrace_118472 : CollatzResearch.WordTrace tailWord_118472 prefixEnd_118472 60833080099565711455163 := by
  unfold tailWord_118472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160514413401826125922835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2880685884535768167897113 2160514413401826125922835)
  ·
    refine ⟨3240771620102739188884253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160514413401826125922835 3240771620102739188884253)
    ·
      refine ⟨1215289357538527195831595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3240771620102739188884253 1215289357538527195831595)
      ·
        refine ⟨1822934036307790793747393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215289357538527195831595 1822934036307790793747393)
        ·
          refine ⟨1367200527230843095310545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822934036307790793747393 1367200527230843095310545)
          ·
            refine ⟨1025400395423132321482909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367200527230843095310545 1025400395423132321482909)
            ·
              refine ⟨384525148283674620556091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025400395423132321482909 384525148283674620556091)
              ·
                refine ⟨576787722425511930834137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384525148283674620556091 576787722425511930834137)
                ·
                  refine ⟨432590791819133948125603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576787722425511930834137 432590791819133948125603)
                  ·
                    refine ⟨648886187728700922188405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432590791819133948125603 648886187728700922188405)
                    ·
                      refine ⟨60833080099565711455163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 648886187728700922188405 60833080099565711455163)
                      ·
                        rfl

theorem cell23_118472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_118472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118472 prefixEnd_118472 := by exact prefixLift 118472
  have htrace : WordTrace (prefixWord ++ tailWord_118472) baseStart_118472 baseEnd_118472 := by
    simpa [prefixWord, tailWord_118472, baseEnd_118472] using wordTrace_append hprefix tailTrace_118472
  have hstable : (prefixWord ++ tailWord_118472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118472).length < 2 ^ (prefixWord ++ tailWord_118472).sum := by decide
  have hdescent : baseEnd_118472 < baseStart_118472 := by decide
  rcases family_descends (prefixWord ++ tailWord_118472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118475 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 9]
def baseStart_118475 : Nat := 118140960795 + 118475 * 2 ^ 59
def prefixEnd_118475 : Nat := 4983230072969 + 3 ^ 40 * 118475 * 2
def baseEnd_118475 : Nat := 6759402282392133301961

theorem tailTrace_118475 : CollatzResearch.WordTrace tailWord_118475 prefixEnd_118475 6759402282392133301961 := by
  unfold tailWord_118475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321138245792783764204879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2880758830528522509469919 4321138245792783764204879)
  ·
    refine ⟨6481707368689175646307319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321138245792783764204879 6481707368689175646307319)
    ·
      refine ⟨9722561053033763469460979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481707368689175646307319 9722561053033763469460979)
      ·
        refine ⟨14583841579550645204191469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722561053033763469460979 14583841579550645204191469)
        ·
          refine ⟨5468940592331491951571801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14583841579550645204191469 5468940592331491951571801)
          ·
            refine ⟨4101705444248618963678851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468940592331491951571801 4101705444248618963678851)
            ·
              refine ⟨6152558166372928445518277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101705444248618963678851 6152558166372928445518277)
              ·
                refine ⟨1153604656194924083534677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6152558166372928445518277 1153604656194924083534677)
                ·
                  refine ⟨6759402282392133301961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1153604656194924083534677 6759402282392133301961)
                  ·
                    rfl

theorem cell23_118475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_118475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118475 prefixEnd_118475 := by exact prefixLift 118475
  have htrace : WordTrace (prefixWord ++ tailWord_118475) baseStart_118475 baseEnd_118475 := by
    simpa [prefixWord, tailWord_118475, baseEnd_118475] using wordTrace_append hprefix tailTrace_118475
  have hstable : (prefixWord ++ tailWord_118475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118475).length < 2 ^ (prefixWord ++ tailWord_118475).sum := by decide
  have hdescent : baseEnd_118475 < baseStart_118475 := by decide
  rcases family_descends (prefixWord ++ tailWord_118475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118589 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_118589 : Nat := 118140960795 + 118589 * 2 ^ 59
def prefixEnd_118589 : Nat := 4983230072969 + 3 ^ 40 * 118589 * 2
def baseEnd_118589 : Nat := 60893157336141753692125

theorem tailTrace_118589 : CollatzResearch.WordTrace tailWord_118589 prefixEnd_118589 60893157336141753692125 := by
  unfold tailWord_118589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325296167379781233854821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2883530778253187489236547 4325296167379781233854821)
  ·
    refine ⟨810993031383708981347779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4325296167379781233854821 810993031383708981347779)
    ·
      refine ⟨1216489547075563472021669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810993031383708981347779 1216489547075563472021669)
      ·
        refine ⟨228091790076668151004063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1216489547075563472021669 228091790076668151004063)
        ·
          refine ⟨342137685115002226506095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228091790076668151004063 342137685115002226506095)
          ·
            refine ⟨513206527672503339759143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342137685115002226506095 513206527672503339759143)
            ·
              refine ⟨769809791508755009638715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513206527672503339759143 769809791508755009638715)
              ·
                refine ⟨1154714687263132514458073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769809791508755009638715 1154714687263132514458073)
                ·
                  refine ⟨866036015447349385843555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154714687263132514458073 866036015447349385843555)
                  ·
                    refine ⟨1299054023171024078765333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 866036015447349385843555 1299054023171024078765333)
                    ·
                      refine ⟨60893157336141753692125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1299054023171024078765333 60893157336141753692125)
                      ·
                        rfl

theorem cell23_118589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_118589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118589 prefixEnd_118589 := by exact prefixLift 118589
  have htrace : WordTrace (prefixWord ++ tailWord_118589) baseStart_118589 baseEnd_118589 := by
    simpa [prefixWord, tailWord_118589, baseEnd_118589] using wordTrace_append hprefix tailTrace_118589
  have hstable : (prefixWord ++ tailWord_118589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118589).length < 2 ^ (prefixWord ++ tailWord_118589).sum := by decide
  have hdescent : baseEnd_118589 < baseStart_118589 := by decide
  rcases family_descends (prefixWord ++ tailWord_118589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118599 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 6]
def baseStart_118599 : Nat := 118140960795 + 118599 * 2 ^ 59
def prefixEnd_118599 : Nat := 4983230072969 + 3 ^ 40 * 118599 * 2
def baseEnd_118599 : Nat := 6766476904742968285231

theorem tailTrace_118599 : CollatzResearch.WordTrace tailWord_118599 prefixEnd_118599 6766476904742968285231 := by
  unfold tailWord_118599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325660897343552941718851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2883773931562368627812567 4325660897343552941718851)
  ·
    refine ⟨6488491346015329412578277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325660897343552941718851 6488491346015329412578277)
    ·
      refine ⟨1216592127377874264858427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6488491346015329412578277 1216592127377874264858427)
      ·
        refine ⟨1824888191066811397287641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216592127377874264858427 1824888191066811397287641)
        ·
          refine ⟨1368666143300108547965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824888191066811397287641 1368666143300108547965731)
          ·
            refine ⟨2052999214950162821948597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368666143300108547965731 2052999214950162821948597)
            ·
              refine ⟨192468676401577764557681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2052999214950162821948597 192468676401577764557681)
              ·
                refine ⟨144351507301183323418261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192468676401577764557681 144351507301183323418261)
                ·
                  refine ⟨6766476904742968285231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144351507301183323418261 6766476904742968285231)
                  ·
                    rfl

theorem cell23_118599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 6].length) (baseStart_118599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118599 prefixEnd_118599 := by exact prefixLift 118599
  have htrace : WordTrace (prefixWord ++ tailWord_118599) baseStart_118599 baseEnd_118599 := by
    simpa [prefixWord, tailWord_118599, baseEnd_118599] using wordTrace_append hprefix tailTrace_118599
  have hstable : (prefixWord ++ tailWord_118599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118599).length < 2 ^ (prefixWord ++ tailWord_118599).sum := by decide
  have hdescent : baseEnd_118599 < baseStart_118599 := by decide
  rcases family_descends (prefixWord ++ tailWord_118599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118602 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_118602 : Nat := 118140960795 + 118602 * 2 ^ 59
def prefixEnd_118602 : Nat := 4983230072969 + 3 ^ 40 * 118602 * 2
def baseEnd_118602 : Nat := 60899832584650202829565

theorem tailTrace_118602 : CollatzResearch.WordTrace tailWord_118602 prefixEnd_118602 60899832584650202829565 := by
  unfold tailWord_118602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081442579083171113519515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2883846877555122969385373 1081442579083171113519515)
  ·
    refine ⟨1622163868624756670279273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1081442579083171113519515 1622163868624756670279273)
    ·
      refine ⟨1216622901468567502709455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1622163868624756670279273 1216622901468567502709455)
      ·
        refine ⟨1824934352202851254064183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216622901468567502709455 1824934352202851254064183)
        ·
          refine ⟨2737401528304276881096275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824934352202851254064183 2737401528304276881096275)
          ·
            refine ⟨4106102292456415321644413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737401528304276881096275 4106102292456415321644413)
            ·
              refine ⟨1539788359671155745616655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4106102292456415321644413 1539788359671155745616655)
              ·
                refine ⟨2309682539506733618424983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539788359671155745616655 2309682539506733618424983)
                ·
                  refine ⟨3464523809260100427637475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309682539506733618424983 3464523809260100427637475)
                  ·
                    refine ⟨5196785713890150641456213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464523809260100427637475 5196785713890150641456213)
                    ·
                      refine ⟨60899832584650202829565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 5196785713890150641456213 60899832584650202829565)
                      ·
                        rfl

theorem cell23_118602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_118602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118602 prefixEnd_118602 := by exact prefixLift 118602
  have htrace : WordTrace (prefixWord ++ tailWord_118602) baseStart_118602 baseEnd_118602 := by
    simpa [prefixWord, tailWord_118602, baseEnd_118602] using wordTrace_append hprefix tailTrace_118602
  have hstable : (prefixWord ++ tailWord_118602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118602).length < 2 ^ (prefixWord ++ tailWord_118602).sum := by decide
  have hdescent : baseEnd_118602 < baseStart_118602 := by decide
  rcases family_descends (prefixWord ++ tailWord_118602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118636 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_118636 : Nat := 118140960795 + 118636 * 2 ^ 59
def prefixEnd_118636 : Nat := 4983230072969 + 3 ^ 40 * 118636 * 2
def baseEnd_118636 : Nat := 60917290926903069804409

theorem tailTrace_118636 : CollatzResearch.WordTrace tailWord_118636 prefixEnd_118636 60917290926903069804409 := by
  unfold tailWord_118636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163505199104754130407881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2884673598806338840543841 2163505199104754130407881)
  ·
    refine ⟨1622628899328565597805911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2163505199104754130407881 1622628899328565597805911)
    ·
      refine ⟨2433943348992848396708867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622628899328565597805911 2433943348992848396708867)
      ·
        refine ⟨3650915023489272595063301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433943348992848396708867 3650915023489272595063301)
        ·
          refine ⟨684546566904238611574369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3650915023489272595063301 684546566904238611574369)
          ·
            refine ⟨513409925178178958680777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684546566904238611574369 513409925178178958680777)
            ·
              refine ⟨385057443883634219010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513409925178178958680777 385057443883634219010583)
              ·
                refine ⟨577586165825451328515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385057443883634219010583 577586165825451328515875)
                ·
                  refine ⟨866379248738176992773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577586165825451328515875 866379248738176992773813)
                  ·
                    refine ⟨81223054569204093072545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 866379248738176992773813 81223054569204093072545)
                    ·
                      refine ⟨60917290926903069804409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81223054569204093072545 60917290926903069804409)
                      ·
                        rfl

theorem cell23_118636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_118636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118636 prefixEnd_118636 := by exact prefixLift 118636
  have htrace : WordTrace (prefixWord ++ tailWord_118636) baseStart_118636 baseEnd_118636 := by
    simpa [prefixWord, tailWord_118636, baseEnd_118636] using wordTrace_append hprefix tailTrace_118636
  have hstable : (prefixWord ++ tailWord_118636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118636).length < 2 ^ (prefixWord ++ tailWord_118636).sum := by decide
  have hdescent : baseEnd_118636 < baseStart_118636 := by decide
  rcases family_descends (prefixWord ++ tailWord_118636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118672 : List Nat := [2, 1, 1, 1, 1, 1, 2, 14]
def baseStart_118672 : Nat := 118140960795 + 118672 * 2 ^ 59
def prefixEnd_118672 : Nat := 4983230072969 + 3 ^ 40 * 118672 * 2
def baseEnd_118672 : Nat := 2256880601128330702009

theorem tailTrace_118672 : CollatzResearch.WordTrace tailWord_118672 prefixEnd_118672 2256880601128330702009 := by
  unfold tailWord_118672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164161713039543204563135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2885548950719390939417513 2164161713039543204563135)
  ·
    refine ⟨3246242569559314806844703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164161713039543204563135 3246242569559314806844703)
    ·
      refine ⟨4869363854338972210267055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246242569559314806844703 4869363854338972210267055)
      ·
        refine ⟨7304045781508458315400583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869363854338972210267055 7304045781508458315400583)
        ·
          refine ⟨10956068672262687473100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304045781508458315400583 10956068672262687473100875)
          ·
            refine ⟨16434103008394031209651313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956068672262687473100875 16434103008394031209651313)
            ·
              refine ⟨12325577256295523407238485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16434103008394031209651313 12325577256295523407238485)
              ·
                refine ⟨2256880601128330702009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 12325577256295523407238485 2256880601128330702009)
                ·
                  rfl

theorem cell23_118672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_118672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118672 prefixEnd_118672 := by exact prefixLift 118672
  have htrace : WordTrace (prefixWord ++ tailWord_118672) baseStart_118672 baseEnd_118672 := by
    simpa [prefixWord, tailWord_118672, baseEnd_118672] using wordTrace_append hprefix tailTrace_118672
  have hstable : (prefixWord ++ tailWord_118672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118672).length < 2 ^ (prefixWord ++ tailWord_118672).sum := by decide
  have hdescent : baseEnd_118672 < baseStart_118672 := by decide
  rcases family_descends (prefixWord ++ tailWord_118672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118679 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_118679 : Nat := 118140960795 + 118679 * 2 ^ 59
def prefixEnd_118679 : Nat := 4983230072969 + 3 ^ 40 * 118679 * 2
def baseEnd_118679 : Nat := 60939370595046401566711

theorem tailTrace_118679 : CollatzResearch.WordTrace tailWord_118679 prefixEnd_118679 60939370595046401566711 := by
  unfold tailWord_118679
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328578737053726604631091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2885719158035817736420727 4328578737053726604631091)
  ·
    refine ⟨6492868105580589906946637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328578737053726604631091 6492868105580589906946637)
    ·
      refine ⟨2434825539592721215104989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6492868105580589906946637 2434825539592721215104989)
      ·
        refine ⟨913059577347270455664371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2434825539592721215104989 913059577347270455664371)
        ·
          refine ⟨1369589366020905683496557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913059577347270455664371 1369589366020905683496557)
          ·
            refine ⟨513596012257839631311209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1369589366020905683496557 513596012257839631311209)
            ·
              refine ⟨385197009193379723483407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513596012257839631311209 385197009193379723483407)
              ·
                refine ⟨577795513790069585225111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385197009193379723483407 577795513790069585225111)
                ·
                  refine ⟨866693270685104377837667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577795513790069585225111 866693270685104377837667)
                  ·
                    refine ⟨1300039906027656566756501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 866693270685104377837667 1300039906027656566756501)
                    ·
                      refine ⟨60939370595046401566711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1300039906027656566756501 60939370595046401566711)
                      ·
                        rfl

theorem cell23_118679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_118679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118679 prefixEnd_118679 := by exact prefixLift 118679
  have htrace : WordTrace (prefixWord ++ tailWord_118679) baseStart_118679 baseEnd_118679 := by
    simpa [prefixWord, tailWord_118679, baseEnd_118679] using wordTrace_append hprefix tailTrace_118679
  have hstable : (prefixWord ++ tailWord_118679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118679).length < 2 ^ (prefixWord ++ tailWord_118679).sum := by decide
  have hdescent : baseEnd_118679 < baseStart_118679 := by decide
  rcases family_descends (prefixWord ++ tailWord_118679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118680 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_118680 : Nat := 118140960795 + 118680 * 2 ^ 59
def prefixEnd_118680 : Nat := 4983230072969 + 3 ^ 40 * 118680 * 2
def baseEnd_118680 : Nat := 20313294691900299218069

theorem tailTrace_118680 : CollatzResearch.WordTrace tailWord_118680 prefixEnd_118680 20313294691900299218069 := by
  unfold tailWord_118680
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164307605025051887708747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2885743473366735850278329 2164307605025051887708747)
  ·
    refine ⟨3246461407537577831563121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164307605025051887708747 3246461407537577831563121)
    ·
      refine ⟨2434846055653183373672341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246461407537577831563121 2434846055653183373672341)
      ·
        refine ⟨114133408858742970640891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2434846055653183373672341 114133408858742970640891)
        ·
          refine ⟨171200113288114455961337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114133408858742970640891 171200113288114455961337)
          ·
            refine ⟨128400084966085841971003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171200113288114455961337 128400084966085841971003)
            ·
              refine ⟨192600127449128762956505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128400084966085841971003 192600127449128762956505)
              ·
                refine ⟨144450095586846572217379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192600127449128762956505 144450095586846572217379)
                ·
                  refine ⟨216675143380269858326069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144450095586846572217379 216675143380269858326069)
                  ·
                    refine ⟨20313294691900299218069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216675143380269858326069 20313294691900299218069)
                    ·
                      rfl

theorem cell23_118680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_118680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118680 prefixEnd_118680 := by exact prefixLift 118680
  have htrace : WordTrace (prefixWord ++ tailWord_118680) baseStart_118680 baseEnd_118680 := by
    simpa [prefixWord, tailWord_118680, baseEnd_118680] using wordTrace_append hprefix tailTrace_118680
  have hstable : (prefixWord ++ tailWord_118680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118680).length < 2 ^ (prefixWord ++ tailWord_118680).sum := by decide
  have hdescent : baseEnd_118680 < baseStart_118680 := by decide
  rcases family_descends (prefixWord ++ tailWord_118680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118703 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 1, 2, 3]
def baseStart_118703 : Nat := 118140960795 + 118703 * 2 ^ 59
def prefixEnd_118703 : Nat := 4983230072969 + 3 ^ 40 * 118703 * 2
def baseEnd_118703 : Nat := 60951694130754307666601

theorem tailTrace_118703 : CollatzResearch.WordTrace tailWord_118703 prefixEnd_118703 60951694130754307666601 := by
  unfold tailWord_118703
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329454088966778703504763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2886302725977852469003175 4329454088966778703504763)
  ·
    refine ⟨6494181133450168055257145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329454088966778703504763 6494181133450168055257145)
    ·
      refine ⟨4870635850087626041442859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6494181133450168055257145 4870635850087626041442859)
      ·
        refine ⟨7305953775131439062164289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870635850087626041442859 7305953775131439062164289)
        ·
          refine ⟨5479465331348579296623217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7305953775131439062164289 5479465331348579296623217)
          ·
            refine ⟨4109598998511434472467413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479465331348579296623217 4109598998511434472467413)
            ·
              refine ⟨96318726527611745448455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4109598998511434472467413 96318726527611745448455)
              ·
                refine ⟨144478089791417618172683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96318726527611745448455 144478089791417618172683)
                ·
                  refine ⟨216717134687126427259025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144478089791417618172683 216717134687126427259025)
                  ·
                    refine ⟨162537851015344820444269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216717134687126427259025 162537851015344820444269)
                    ·
                      refine ⟨60951694130754307666601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162537851015344820444269 60951694130754307666601)
                      ·
                        rfl

theorem cell23_118703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 2, 3].length) (baseStart_118703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118703 prefixEnd_118703 := by exact prefixLift 118703
  have htrace : WordTrace (prefixWord ++ tailWord_118703) baseStart_118703 baseEnd_118703 := by
    simpa [prefixWord, tailWord_118703, baseEnd_118703] using wordTrace_append hprefix tailTrace_118703
  have hstable : (prefixWord ++ tailWord_118703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118703).length < 2 ^ (prefixWord ++ tailWord_118703).sum := by decide
  have hdescent : baseEnd_118703 < baseStart_118703 := by decide
  rcases family_descends (prefixWord ++ tailWord_118703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118717 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_118717 : Nat := 118140960795 + 118717 * 2 ^ 59
def prefixEnd_118717 : Nat := 4983230072969 + 3 ^ 40 * 118717 * 2
def baseEnd_118717 : Nat := 60958882859917252891537

theorem tailTrace_118717 : CollatzResearch.WordTrace tailWord_118717 prefixEnd_118717 60958882859917252891537 := by
  unfold tailWord_118717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329964710916059094514405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2886643140610706063009603 4329964710916059094514405)
  ·
    refine ⟨811868383296761080221451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4329964710916059094514405 811868383296761080221451)
    ·
      refine ⟨1217802574945141620332177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811868383296761080221451 1217802574945141620332177)
      ·
        refine ⟨913351931208856215249133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217802574945141620332177 913351931208856215249133)
        ·
          refine ⟨342506974203321080718425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 913351931208856215249133 342506974203321080718425)
          ·
            refine ⟨256880230652490810538819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342506974203321080718425 256880230652490810538819)
            ·
              refine ⟨385320345978736215808229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256880230652490810538819 385320345978736215808229)
              ·
                refine ⟨72247564871013040464043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385320345978736215808229 72247564871013040464043)
                ·
                  refine ⟨108371347306519560696065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72247564871013040464043 108371347306519560696065)
                  ·
                    refine ⟨81278510479889670522049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108371347306519560696065 81278510479889670522049)
                    ·
                      refine ⟨60958882859917252891537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81278510479889670522049 60958882859917252891537)
                      ·
                        rfl

theorem cell23_118717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_118717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118717 prefixEnd_118717 := by exact prefixLift 118717
  have htrace : WordTrace (prefixWord ++ tailWord_118717) baseStart_118717 baseEnd_118717 := by
    simpa [prefixWord, tailWord_118717, baseEnd_118717] using wordTrace_append hprefix tailTrace_118717
  have hstable : (prefixWord ++ tailWord_118717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118717).length < 2 ^ (prefixWord ++ tailWord_118717).sum := by decide
  have hdescent : baseEnd_118717 < baseStart_118717 := by decide
  rcases family_descends (prefixWord ++ tailWord_118717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118743 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_118743 : Nat := 118140960795 + 118743 * 2 ^ 59
def prefixEnd_118743 : Nat := 4983230072969 + 3 ^ 40 * 118743 * 2
def baseEnd_118743 : Nat := 60972233356934151166417

theorem tailTrace_118743 : CollatzResearch.WordTrace tailWord_118743 prefixEnd_118743 60972233356934151166417 := by
  unfold tailWord_118743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330913008821865534960883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2887275339214577023307255 4330913008821865534960883)
  ·
    refine ⟨6496369513232798302441325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330913008821865534960883 6496369513232798302441325)
    ·
      refine ⟨2436138567462299363415497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6496369513232798302441325 2436138567462299363415497)
      ·
        refine ⟨1827103925596724522561623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436138567462299363415497 1827103925596724522561623)
        ·
          refine ⟨2740655888395086783842435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827103925596724522561623 2740655888395086783842435)
          ·
            refine ⟨4110983832592630175763653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740655888395086783842435 4110983832592630175763653)
            ·
              refine ⟨770809468611118157955685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4110983832592630175763653 770809468611118157955685)
              ·
                refine ⟨144526775364584654616691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770809468611118157955685 144526775364584654616691)
                ·
                  refine ⟨216790163046876981925037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144526775364584654616691 216790163046876981925037)
                  ·
                    refine ⟨81296311142578868221889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216790163046876981925037 81296311142578868221889)
                    ·
                      refine ⟨60972233356934151166417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81296311142578868221889 60972233356934151166417)
                      ·
                        rfl

theorem cell23_118743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_118743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118743 prefixEnd_118743 := by exact prefixLift 118743
  have htrace : WordTrace (prefixWord ++ tailWord_118743) baseStart_118743 baseEnd_118743 := by
    simpa [prefixWord, tailWord_118743, baseEnd_118743] using wordTrace_append hprefix tailTrace_118743
  have hstable : (prefixWord ++ tailWord_118743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118743).length < 2 ^ (prefixWord ++ tailWord_118743).sum := by decide
  have hdescent : baseEnd_118743 < baseStart_118743 := by decide
  rcases family_descends (prefixWord ++ tailWord_118743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118754 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_118754 : Nat := 118140960795 + 118754 * 2 ^ 59
def prefixEnd_118754 : Nat := 4983230072969 + 3 ^ 40 * 118754 * 2
def baseEnd_118754 : Nat := 60977881644133608128867

theorem tailTrace_118754 : CollatzResearch.WordTrace tailWord_118754 prefixEnd_118754 60977881644133608128867 := by
  unfold tailWord_118754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082828552945503603402829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2887542807854676275740877 1082828552945503603402829)
  ·
    refine ⟨406060707354563851276061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1082828552945503603402829 406060707354563851276061)
    ·
      refine ⟨152272765257961444228523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406060707354563851276061 152272765257961444228523)
      ·
        refine ⟨228409147886942166342785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152272765257961444228523 228409147886942166342785)
        ·
          refine ⟨171306860915206624757089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228409147886942166342785 171306860915206624757089)
          ·
            refine ⟨128480145686404968567817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171306860915206624757089 128480145686404968567817)
            ·
              refine ⟨96360109264803726425863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128480145686404968567817 96360109264803726425863)
              ·
                refine ⟨144540163897205589638795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96360109264803726425863 144540163897205589638795)
                ·
                  refine ⟨216810245845808384458193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144540163897205589638795 216810245845808384458193)
                  ·
                    refine ⟨162607684384356288343645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216810245845808384458193 162607684384356288343645)
                    ·
                      refine ⟨60977881644133608128867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162607684384356288343645 60977881644133608128867)
                      ·
                        rfl

theorem cell23_118754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_118754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118754 prefixEnd_118754 := by exact prefixLift 118754
  have htrace : WordTrace (prefixWord ++ tailWord_118754) baseStart_118754 baseEnd_118754 := by
    simpa [prefixWord, tailWord_118754, baseEnd_118754] using wordTrace_append hprefix tailTrace_118754
  have hstable : (prefixWord ++ tailWord_118754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118754).length < 2 ^ (prefixWord ++ tailWord_118754).sum := by decide
  have hdescent : baseEnd_118754 < baseStart_118754 := by decide
  rcases family_descends (prefixWord ++ tailWord_118754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118766 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_118766 : Nat := 118140960795 + 118766 * 2 ^ 59
def prefixEnd_118766 : Nat := 4983230072969 + 3 ^ 40 * 118766 * 2
def baseEnd_118766 : Nat := 20328014470662520392937

theorem tailTrace_118766 : CollatzResearch.WordTrace tailWord_118766 prefixEnd_118766 20328014470662520392937 := by
  unfold tailWord_118766
  simp only [CollatzResearch.WordTrace]
  refine ⟨541468985967317557881019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2887834591825693642032101 541468985967317557881019)
  ·
    refine ⟨812203478950976336821529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541468985967317557881019 812203478950976336821529)
    ·
      refine ⟨609152609213232252616147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 812203478950976336821529 609152609213232252616147)
      ·
        refine ⟨913728913819848378924221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609152609213232252616147 913728913819848378924221)
        ·
          refine ⟨342648342682443142096583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 913728913819848378924221 342648342682443142096583)
          ·
            refine ⟨513972514023664713144875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342648342682443142096583 513972514023664713144875)
            ·
              refine ⟨770958771035497069717313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513972514023664713144875 770958771035497069717313)
              ·
                refine ⟨578219078276622802287985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770958771035497069717313 578219078276622802287985)
                ·
                  refine ⟨433664308707467101715989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578219078276622802287985 433664308707467101715989)
                  ·
                    refine ⟨20328014470662520392937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 433664308707467101715989 20328014470662520392937)
                    ·
                      rfl

theorem cell23_118766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_118766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118766 prefixEnd_118766 := by exact prefixLift 118766
  have htrace : WordTrace (prefixWord ++ tailWord_118766) baseStart_118766 baseEnd_118766 := by
    simpa [prefixWord, tailWord_118766, baseEnd_118766] using wordTrace_append hprefix tailTrace_118766
  have hstable : (prefixWord ++ tailWord_118766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118766).length < 2 ^ (prefixWord ++ tailWord_118766).sum := by decide
  have hdescent : baseEnd_118766 < baseStart_118766 := by decide
  rcases family_descends (prefixWord ++ tailWord_118766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118779 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 7]
def baseStart_118779 : Nat := 118140960795 + 118779 * 2 ^ 59
def prefixEnd_118779 : Nat := 4983230072969 + 3 ^ 40 * 118779 * 2
def baseEnd_118779 : Nat := 6776746517832890035139

theorem tailTrace_118779 : CollatzResearch.WordTrace tailWord_118779 prefixEnd_118779 6776746517832890035139 := by
  unfold tailWord_118779
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332226036691443683271391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2888150691127629122180927 4332226036691443683271391)
  ·
    refine ⟨6498339055037165524907087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332226036691443683271391 6498339055037165524907087)
    ·
      refine ⟨9747508582555748287360631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498339055037165524907087 9747508582555748287360631)
      ·
        refine ⟨14621262873833622431040947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747508582555748287360631 14621262873833622431040947)
        ·
          refine ⟨21931894310750433646561421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14621262873833622431040947 21931894310750433646561421)
          ·
            refine ⟨8224460366531412617460533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21931894310750433646561421 8224460366531412617460533)
            ·
              refine ⟨771043159362319932886925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8224460366531412617460533 771043159362319932886925)
              ·
                refine ⟨289141184760869974832597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771043159362319932886925 289141184760869974832597)
                ·
                  refine ⟨6776746517832890035139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 289141184760869974832597 6776746517832890035139)
                  ·
                    rfl

theorem cell23_118779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 7].length) (baseStart_118779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118779 prefixEnd_118779 := by exact prefixLift 118779
  have htrace : WordTrace (prefixWord ++ tailWord_118779) baseStart_118779 baseEnd_118779 := by
    simpa [prefixWord, tailWord_118779, baseEnd_118779] using wordTrace_append hprefix tailTrace_118779
  have hstable : (prefixWord ++ tailWord_118779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118779).length < 2 ^ (prefixWord ++ tailWord_118779).sum := by decide
  have hdescent : baseEnd_118779 < baseStart_118779 := by decide
  rcases family_descends (prefixWord ++ tailWord_118779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118841 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 2, 2, 2]
def baseStart_118841 : Nat := 118140960795 + 118841 * 2 ^ 59
def prefixEnd_118841 : Nat := 4983230072969 + 3 ^ 40 * 118841 * 2
def baseEnd_118841 : Nat := 61022554461074767740967

theorem tailTrace_118841 : CollatzResearch.WordTrace tailWord_118841 prefixEnd_118841 61022554461074767740967 := by
  unfold tailWord_118841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334487362466828272028377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2889658241644552181352251 4334487362466828272028377)
  ·
    refine ⟨3250865521850121204021283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4334487362466828272028377 3250865521850121204021283)
    ·
      refine ⟨4876298282775181806031925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250865521850121204021283 4876298282775181806031925)
      ·
        refine ⟨457152964010173294315493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4876298282775181806031925 457152964010173294315493)
        ·
          refine ⟨85716180751907492684155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457152964010173294315493 85716180751907492684155)
          ·
            refine ⟨128574271127861239026233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85716180751907492684155 128574271127861239026233)
            ·
              refine ⟨96430703345895929269675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128574271127861239026233 96430703345895929269675)
              ·
                refine ⟨144646055018843893904513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96430703345895929269675 144646055018843893904513)
                ·
                  refine ⟨108484541264132920428385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144646055018843893904513 108484541264132920428385)
                  ·
                    refine ⟨81363405948099690321289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108484541264132920428385 81363405948099690321289)
                    ·
                      refine ⟨61022554461074767740967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81363405948099690321289 61022554461074767740967)
                      ·
                        rfl

theorem cell23_118841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_118841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118841 prefixEnd_118841 := by exact prefixLift 118841
  have htrace : WordTrace (prefixWord ++ tailWord_118841) baseStart_118841 baseEnd_118841 := by
    simpa [prefixWord, tailWord_118841, baseEnd_118841] using wordTrace_append hprefix tailTrace_118841
  have hstable : (prefixWord ++ tailWord_118841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118841).length < 2 ^ (prefixWord ++ tailWord_118841).sum := by decide
  have hdescent : baseEnd_118841 < baseStart_118841 := by decide
  rcases family_descends (prefixWord ++ tailWord_118841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118870 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_118870 : Nat := 118140960795 + 118870 * 2 ^ 59
def prefixEnd_118870 : Nat := 4983230072969 + 3 ^ 40 * 118870 * 2
def baseEnd_118870 : Nat := 61037445400055154278333

theorem tailTrace_118870 : CollatzResearch.WordTrace tailWord_118870 prefixEnd_118870 61037445400055154278333 := by
  unfold tailWord_118870
  simp only [CollatzResearch.WordTrace]
  refine ⟨270971567460110389052129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2890363386241177483222709 270971567460110389052129)
  ·
    refine ⟨203228675595082791789097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270971567460110389052129 203228675595082791789097)
    ·
      refine ⟨152421506696312093841823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203228675595082791789097 152421506696312093841823)
      ·
        refine ⟨228632260044468140762735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152421506696312093841823 228632260044468140762735)
        ·
          refine ⟨342948390066702211144103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228632260044468140762735 342948390066702211144103)
          ·
            refine ⟨514422585100053316716155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342948390066702211144103 514422585100053316716155)
            ·
              refine ⟨771633877650079975074233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514422585100053316716155 771633877650079975074233)
              ·
                refine ⟨578725408237559981305675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771633877650079975074233 578725408237559981305675)
                ·
                  refine ⟨868088112356339971958513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578725408237559981305675 868088112356339971958513)
                  ·
                    refine ⟨651066084267254978968885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868088112356339971958513 651066084267254978968885)
                    ·
                      refine ⟨61037445400055154278333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 651066084267254978968885 61037445400055154278333)
                      ·
                        rfl

theorem cell23_118870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_118870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118870 prefixEnd_118870 := by exact prefixLift 118870
  have htrace : WordTrace (prefixWord ++ tailWord_118870) baseStart_118870 baseEnd_118870 := by
    simpa [prefixWord, tailWord_118870, baseEnd_118870] using wordTrace_append hprefix tailTrace_118870
  have hstable : (prefixWord ++ tailWord_118870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118870).length < 2 ^ (prefixWord ++ tailWord_118870).sum := by decide
  have hdescent : baseEnd_118870 < baseStart_118870 := by decide
  rcases family_descends (prefixWord ++ tailWord_118870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118883 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3]
def baseStart_118883 : Nat := 118140960795 + 118883 * 2 ^ 59
def prefixEnd_118883 : Nat := 4983230072969 + 3 ^ 40 * 118883 * 2
def baseEnd_118883 : Nat := 61044120648563603415773

theorem tailTrace_118883 : CollatzResearch.WordTrace tailWord_118883 prefixEnd_118883 61044120648563603415773 := by
  unfold tailWord_118883
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336019228314669445057303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2890679485543112963371535 4336019228314669445057303)
  ·
    refine ⟨6504028842472004167585955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4336019228314669445057303 6504028842472004167585955)
    ·
      refine ⟨9756043263708006251378933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504028842472004167585955 9756043263708006251378933)
      ·
        refine ⟨914629055972625586066775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9756043263708006251378933 914629055972625586066775)
        ·
          refine ⟨1371943583958938379100163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914629055972625586066775 1371943583958938379100163)
          ·
            refine ⟨2057915375938407568650245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371943583958938379100163 2057915375938407568650245)
            ·
              refine ⟨385859132988451419121921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2057915375938407568650245 385859132988451419121921)
              ·
                refine ⟨289394349741338564341441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385859132988451419121921 289394349741338564341441)
                ·
                  refine ⟨217045762306003923256081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289394349741338564341441 217045762306003923256081)
                  ·
                    refine ⟨162784321729502942442061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217045762306003923256081 162784321729502942442061)
                    ·
                      refine ⟨61044120648563603415773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162784321729502942442061 61044120648563603415773)
                      ·
                        rfl

theorem cell23_118883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_118883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118883 prefixEnd_118883 := by exact prefixLift 118883
  have htrace : WordTrace (prefixWord ++ tailWord_118883) baseStart_118883 baseEnd_118883 := by
    simpa [prefixWord, tailWord_118883, baseEnd_118883] using wordTrace_append hprefix tailTrace_118883
  have hstable : (prefixWord ++ tailWord_118883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118883).length < 2 ^ (prefixWord ++ tailWord_118883).sum := by decide
  have hdescent : baseEnd_118883 < baseStart_118883 := by decide
  rcases family_descends (prefixWord ++ tailWord_118883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118930 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_118930 : Nat := 118140960795 + 118930 * 2 ^ 59
def prefixEnd_118930 : Nat := 4983230072969 + 3 ^ 40 * 118930 * 2
def baseEnd_118930 : Nat := 61068254239324919528057

theorem tailTrace_118930 : CollatzResearch.WordTrace tailWord_118930 prefixEnd_118930 61068254239324919528057 := by
  unfold tailWord_118930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084433364786099118004561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2891822306096264314678829 1084433364786099118004561)
  ·
    refine ⟨813325023589574338503421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1084433364786099118004561 813325023589574338503421)
    ·
      refine ⟨304996883846090376938783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 813325023589574338503421 304996883846090376938783)
      ·
        refine ⟨457495325769135565408175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304996883846090376938783 457495325769135565408175)
        ·
          refine ⟨686242988653703348112263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457495325769135565408175 686242988653703348112263)
          ·
            refine ⟨1029364482980555022168395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686242988653703348112263 1029364482980555022168395)
            ·
              refine ⟨1544046724470832533252593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029364482980555022168395 1544046724470832533252593)
              ·
                refine ⟨1158035043353124399939445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544046724470832533252593 1158035043353124399939445)
                ·
                  refine ⟨108565785314355412494323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158035043353124399939445 108565785314355412494323)
                  ·
                    refine ⟨162848677971533118741485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108565785314355412494323 162848677971533118741485)
                    ·
                      refine ⟨61068254239324919528057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162848677971533118741485 61068254239324919528057)
                      ·
                        rfl

theorem cell23_118930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_118930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118930 prefixEnd_118930 := by exact prefixLift 118930
  have htrace : WordTrace (prefixWord ++ tailWord_118930) baseStart_118930 baseEnd_118930 := by
    simpa [prefixWord, tailWord_118930, baseEnd_118930] using wordTrace_append hprefix tailTrace_118930
  have hstable : (prefixWord ++ tailWord_118930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118930).length < 2 ^ (prefixWord ++ tailWord_118930).sum := by decide
  have hdescent : baseEnd_118930 < baseStart_118930 := by decide
  rcases family_descends (prefixWord ++ tailWord_118930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118933 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_118933 : Nat := 118140960795 + 118933 * 2 ^ 59
def prefixEnd_118933 : Nat := 4983230072969 + 3 ^ 40 * 118933 * 2
def baseEnd_118933 : Nat := 20356598227096135930181

theorem tailTrace_118933 : CollatzResearch.WordTrace tailWord_118933 prefixEnd_118933 20356598227096135930181 := by
  unfold tailWord_118933
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337842878133527984377453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2891895252089018656251635 4337842878133527984377453)
  ·
    refine ⟨1626691079300072994141545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4337842878133527984377453 1626691079300072994141545)
    ·
      refine ⟨1220018309475054745606159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1626691079300072994141545 1220018309475054745606159)
      ·
        refine ⟨1830027464212582118409239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220018309475054745606159 1830027464212582118409239)
        ·
          refine ⟨2745041196318873177613859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830027464212582118409239 2745041196318873177613859)
          ·
            refine ⟨4117561794478309766420789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745041196318873177613859 4117561794478309766420789)
            ·
              refine ⟨386021418232341540601949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4117561794478309766420789 386021418232341540601949)
              ·
                refine ⟨144758031837128077725731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386021418232341540601949 144758031837128077725731)
                ·
                  refine ⟨217137047755692116588597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144758031837128077725731 217137047755692116588597)
                  ·
                    refine ⟨20356598227096135930181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217137047755692116588597 20356598227096135930181)
                    ·
                      rfl

theorem cell23_118933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_118933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118933 prefixEnd_118933 := by exact prefixLift 118933
  have htrace : WordTrace (prefixWord ++ tailWord_118933) baseStart_118933 baseEnd_118933 := by
    simpa [prefixWord, tailWord_118933, baseEnd_118933] using wordTrace_append hprefix tailTrace_118933
  have hstable : (prefixWord ++ tailWord_118933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118933).length < 2 ^ (prefixWord ++ tailWord_118933).sum := by decide
  have hdescent : baseEnd_118933 < baseStart_118933 := by decide
  rcases family_descends (prefixWord ++ tailWord_118933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118940 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_118940 : Nat := 118140960795 + 118940 * 2 ^ 59
def prefixEnd_118940 : Nat := 4983230072969 + 3 ^ 40 * 118940 * 2
def baseEnd_118940 : Nat := 61073389045869880403011

theorem tailTrace_118940 : CollatzResearch.WordTrace tailWord_118940 prefixEnd_118940 61073389045869880403011 := by
  unfold tailWord_118940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169049094554084089941137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2892065459405445453254849 2169049094554084089941137)
  ·
    refine ⟨1626786820915563067455853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169049094554084089941137 1626786820915563067455853)
    ·
      refine ⟨610045057843336150295945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1626786820915563067455853 610045057843336150295945)
      ·
        refine ⟨457533793382502112721959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610045057843336150295945 457533793382502112721959)
        ·
          refine ⟨686300690073753169082939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457533793382502112721959 686300690073753169082939)
          ·
            refine ⟨1029451035110629753624409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686300690073753169082939 1029451035110629753624409)
            ·
              refine ⟨772088276332972315218307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029451035110629753624409 772088276332972315218307)
              ·
                refine ⟨1158132414499458472827461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772088276332972315218307 1158132414499458472827461)
                ·
                  refine ⟨217149827718648463655149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158132414499458472827461 217149827718648463655149)
                  ·
                    refine ⟨81431185394493173870681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217149827718648463655149 81431185394493173870681)
                    ·
                      refine ⟨61073389045869880403011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81431185394493173870681 61073389045869880403011)
                      ·
                        rfl

theorem cell23_118940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_118940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118940 prefixEnd_118940 := by exact prefixLift 118940
  have htrace : WordTrace (prefixWord ++ tailWord_118940) baseStart_118940 baseEnd_118940 := by
    simpa [prefixWord, tailWord_118940, baseEnd_118940] using wordTrace_append hprefix tailTrace_118940
  have hstable : (prefixWord ++ tailWord_118940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118940).length < 2 ^ (prefixWord ++ tailWord_118940).sum := by decide
  have hdescent : baseEnd_118940 < baseStart_118940 := by decide
  rcases family_descends (prefixWord ++ tailWord_118940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118980 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_118980 : Nat := 118140960795 + 118980 * 2 ^ 59
def prefixEnd_118980 : Nat := 4983230072969 + 3 ^ 40 * 118980 * 2
def baseEnd_118980 : Nat := 20364642757349907967609

theorem tailTrace_118980 : CollatzResearch.WordTrace tailWord_118980 prefixEnd_118980 20364642757349907967609 := by
  unfold tailWord_118980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169778554481627505669197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2893038072642170007558929 2169778554481627505669197)
  ·
    refine ⟨813666957930610314625949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2169778554481627505669197 813666957930610314625949)
    ·
      refine ⟨305125109223978867984731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 813666957930610314625949 305125109223978867984731)
      ·
        refine ⟨457687663835968301977097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305125109223978867984731 457687663835968301977097)
        ·
          refine ⟨343265747876976226482823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457687663835968301977097 343265747876976226482823)
          ·
            refine ⟨514898621815464339724235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343265747876976226482823 514898621815464339724235)
            ·
              refine ⟨772347932723196509586353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514898621815464339724235 772347932723196509586353)
              ·
                refine ⟨579260949542397382189765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772347932723196509586353 579260949542397382189765)
                ·
                  refine ⟨108611428039199509160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579260949542397382189765 108611428039199509160581)
                  ·
                    refine ⟨20364642757349907967609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108611428039199509160581 20364642757349907967609)
                    ·
                      rfl

theorem cell23_118980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_118980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118980 prefixEnd_118980 := by exact prefixLift 118980
  have htrace : WordTrace (prefixWord ++ tailWord_118980) baseStart_118980 baseEnd_118980 := by
    simpa [prefixWord, tailWord_118980, baseEnd_118980] using wordTrace_append hprefix tailTrace_118980
  have hstable : (prefixWord ++ tailWord_118980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118980).length < 2 ^ (prefixWord ++ tailWord_118980).sum := by decide
  have hdescent : baseEnd_118980 < baseStart_118980 := by decide
  rcases family_descends (prefixWord ++ tailWord_118980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118990 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_118990 : Nat := 118140960795 + 118990 * 2 ^ 59
def prefixEnd_118990 : Nat := 4983230072969 + 3 ^ 40 * 118990 * 2
def baseEnd_118990 : Nat := 61099063078594684777781

theorem tailTrace_118990 : CollatzResearch.WordTrace tailWord_118990 prefixEnd_118990 61099063078594684777781 := by
  unfold tailWord_118990
  simp only [CollatzResearch.WordTrace]
  refine ⟨542490229865878339900303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2893281225951351146134949 542490229865878339900303)
  ·
    refine ⟨813735344798817509850455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542490229865878339900303 813735344798817509850455)
    ·
      refine ⟨1220603017198226264775683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813735344798817509850455 1220603017198226264775683)
      ·
        refine ⟨1830904525797339397163525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220603017198226264775683 1830904525797339397163525)
        ·
          refine ⟨343294598587001136968161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1830904525797339397163525 343294598587001136968161)
          ·
            refine ⟨257470948940250852726121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343294598587001136968161 257470948940250852726121)
            ·
              refine ⟨193103211705188139544591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257470948940250852726121 193103211705188139544591)
              ·
                refine ⟨289654817557782209316887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193103211705188139544591 289654817557782209316887)
                ·
                  refine ⟨434482226336673313975331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289654817557782209316887 434482226336673313975331)
                  ·
                    refine ⟨651723339505009970962997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434482226336673313975331 651723339505009970962997)
                    ·
                      refine ⟨61099063078594684777781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 651723339505009970962997 61099063078594684777781)
                      ·
                        rfl

theorem cell23_118990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_118990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118990 prefixEnd_118990 := by exact prefixLift 118990
  have htrace : WordTrace (prefixWord ++ tailWord_118990) baseStart_118990 baseEnd_118990 := by
    simpa [prefixWord, tailWord_118990, baseEnd_118990] using wordTrace_append hprefix tailTrace_118990
  have hstable : (prefixWord ++ tailWord_118990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118990).length < 2 ^ (prefixWord ++ tailWord_118990).sum := by decide
  have hdescent : baseEnd_118990 < baseStart_118990 := by decide
  rcases family_descends (prefixWord ++ tailWord_118990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118998 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_118998 : Nat := 118140960795 + 118998 * 2 ^ 59
def prefixEnd_118998 : Nat := 4983230072969 + 3 ^ 40 * 118998 * 2
def baseEnd_118998 : Nat := 61103170923830653477745

theorem tailTrace_118998 : CollatzResearch.WordTrace tailWord_118998 prefixEnd_118998 61103170923830653477745 := by
  unfold tailWord_118998
  simp only [CollatzResearch.WordTrace]
  refine ⟨271263351431127755343353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2893475748598696056995765 271263351431127755343353)
  ·
    refine ⟨203447513573345816507515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271263351431127755343353 203447513573345816507515)
    ·
      refine ⟨305171270360018724761273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203447513573345816507515 305171270360018724761273)
      ·
        refine ⟨228878452770014043570955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305171270360018724761273 228878452770014043570955)
        ·
          refine ⟨343317679155021065356433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228878452770014043570955 343317679155021065356433)
          ·
            refine ⟨257488259366265799017325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343317679155021065356433 257488259366265799017325)
            ·
              refine ⟨96558097262349674631497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257488259366265799017325 96558097262349674631497)
              ·
                refine ⟨72418572946762255973623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96558097262349674631497 72418572946762255973623)
                ·
                  refine ⟨108627859420143383960435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72418572946762255973623 108627859420143383960435)
                  ·
                    refine ⟨162941789130215075940653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108627859420143383960435 162941789130215075940653)
                    ·
                      refine ⟨61103170923830653477745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162941789130215075940653 61103170923830653477745)
                      ·
                        rfl

theorem cell23_118998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_118998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118998 prefixEnd_118998 := by exact prefixLift 118998
  have htrace : WordTrace (prefixWord ++ tailWord_118998) baseStart_118998 baseEnd_118998 := by
    simpa [prefixWord, tailWord_118998, baseEnd_118998] using wordTrace_append hprefix tailTrace_118998
  have hstable : (prefixWord ++ tailWord_118998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118998).length < 2 ^ (prefixWord ++ tailWord_118998).sum := by decide
  have hdescent : baseEnd_118998 < baseStart_118998 := by decide
  rcases family_descends (prefixWord ++ tailWord_118998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119073 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_119073 : Nat := 118140960795 + 119073 * 2 ^ 59
def prefixEnd_119073 : Nat := 4983230072969 + 3 ^ 40 * 119073 * 2
def baseEnd_119073 : Nat := 61141681972917860039899

theorem tailTrace_119073 : CollatzResearch.WordTrace tailWord_119073 prefixEnd_119073 61141681972917860039899 := by
  unfold tailWord_119073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342949097626331894473873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2895299398417554596315915 4342949097626331894473873)
  ·
    refine ⟨3257211823219748920855405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4342949097626331894473873 3257211823219748920855405)
    ·
      refine ⟨1221454433707405845320777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3257211823219748920855405 1221454433707405845320777)
      ·
        refine ⟨916090825280554383990583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1221454433707405845320777 916090825280554383990583)
        ·
          refine ⟨1374136237920831575985875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916090825280554383990583 1374136237920831575985875)
          ·
            refine ⟨2061204356881247363978813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374136237920831575985875 2061204356881247363978813)
            ·
              refine ⟨772951633830467761492055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061204356881247363978813 772951633830467761492055)
              ·
                refine ⟨1159427450745701642238083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772951633830467761492055 1159427450745701642238083)
                ·
                  refine ⟨1739141176118552463357125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159427450745701642238083 1739141176118552463357125)
                  ·
                    refine ⟨326088970522228586879461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739141176118552463357125 326088970522228586879461)
                    ·
                      refine ⟨61141681972917860039899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 326088970522228586879461 61141681972917860039899)
                      ·
                        rfl

theorem cell23_119073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_119073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119073 prefixEnd_119073 := by exact prefixLift 119073
  have htrace : WordTrace (prefixWord ++ tailWord_119073) baseStart_119073 baseEnd_119073 := by
    simpa [prefixWord, tailWord_119073, baseEnd_119073] using wordTrace_append hprefix tailTrace_119073
  have hstable : (prefixWord ++ tailWord_119073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119073).length < 2 ^ (prefixWord ++ tailWord_119073).sum := by decide
  have hdescent : baseEnd_119073 < baseStart_119073 := by decide
  rcases family_descends (prefixWord ++ tailWord_119073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119113 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_119113 : Nat := 118140960795 + 119113 * 2 ^ 59
def prefixEnd_119113 : Nat := 4983230072969 + 3 ^ 40 * 119113 * 2
def baseEnd_119113 : Nat := 20387407066365901179905

theorem tailTrace_119113 : CollatzResearch.WordTrace tailWord_119113 prefixEnd_119113 20387407066365901179905 := by
  unfold tailWord_119113
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344408017481418725929993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2896272011654279150619995 4344408017481418725929993)
  ·
    refine ⟨3258306013111064044447495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4344408017481418725929993 3258306013111064044447495)
    ·
      refine ⟨4887459019666596066671243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258306013111064044447495 4887459019666596066671243)
      ·
        refine ⟨7331188529499894100006865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887459019666596066671243 7331188529499894100006865)
        ·
          refine ⟨5498391397124920575005149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7331188529499894100006865 5498391397124920575005149)
          ·
            refine ⟨2061896773921845215626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5498391397124920575005149 2061896773921845215626931)
            ·
              refine ⟨3092845160882767823440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061896773921845215626931 3092845160882767823440397)
              ·
                refine ⟨1159816935331037933790149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092845160882767823440397 1159816935331037933790149)
                ·
                  refine ⟨217465675374569612585653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159816935331037933790149 217465675374569612585653)
                  ·
                    refine ⟨20387407066365901179905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217465675374569612585653 20387407066365901179905)
                    ·
                      rfl

theorem cell23_119113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_119113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119113 prefixEnd_119113 := by exact prefixLift 119113
  have htrace : WordTrace (prefixWord ++ tailWord_119113) baseStart_119113 baseEnd_119113 := by
    simpa [prefixWord, tailWord_119113, baseEnd_119113] using wordTrace_append hprefix tailTrace_119113
  have hstable : (prefixWord ++ tailWord_119113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119113).length < 2 ^ (prefixWord ++ tailWord_119113).sum := by decide
  have hdescent : baseEnd_119113 < baseStart_119113 := by decide
  rcases family_descends (prefixWord ++ tailWord_119113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119153 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_119153 : Nat := 118140960795 + 119153 * 2 ^ 59
def prefixEnd_119153 : Nat := 4983230072969 + 3 ^ 40 * 119153 * 2
def baseEnd_119153 : Nat := 61182760425277547039531

theorem tailTrace_119153 : CollatzResearch.WordTrace tailWord_119153 prefixEnd_119153 61182760425277547039531 := by
  unfold tailWord_119153
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345866937336505557386113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2897244624891003704924075 4345866937336505557386113)
  ·
    refine ⟨3259400203002379168039585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4345866937336505557386113 3259400203002379168039585)
    ·
      refine ⟨2444550152251784376029689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3259400203002379168039585 2444550152251784376029689)
      ·
        refine ⟨1833412614188838282022267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444550152251784376029689 1833412614188838282022267)
        ·
          refine ⟨2750118921283257423033401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833412614188838282022267 2750118921283257423033401)
          ·
            refine ⟨2062589190962443067275051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750118921283257423033401 2062589190962443067275051)
            ·
              refine ⟨3093883786443664600912577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062589190962443067275051 3093883786443664600912577)
              ·
                refine ⟨2320412839832748450684433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093883786443664600912577 2320412839832748450684433)
                ·
                  refine ⟨1740309629874561338013325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2320412839832748450684433 1740309629874561338013325)
                  ·
                    refine ⟨652616111202960501754997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740309629874561338013325 652616111202960501754997)
                    ·
                      refine ⟨61182760425277547039531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 652616111202960501754997 61182760425277547039531)
                      ·
                        rfl

theorem cell23_119153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_119153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119153 prefixEnd_119153 := by exact prefixLift 119153
  have htrace : WordTrace (prefixWord ++ tailWord_119153) baseStart_119153 baseEnd_119153 := by
    simpa [prefixWord, tailWord_119153, baseEnd_119153] using wordTrace_append hprefix tailTrace_119153
  have hstable : (prefixWord ++ tailWord_119153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119153).length < 2 ^ (prefixWord ++ tailWord_119153).sum := by decide
  have hdescent : baseEnd_119153 < baseStart_119153 := by decide
  rcases family_descends (prefixWord ++ tailWord_119153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119177 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_119177 : Nat := 118140960795 + 119177 * 2 ^ 59
def prefixEnd_119177 : Nat := 4983230072969 + 3 ^ 40 * 119177 * 2
def baseEnd_119177 : Nat := 20398361320328484379807

theorem tailTrace_119177 : CollatzResearch.WordTrace tailWord_119177 prefixEnd_119177 20398361320328484379807 := by
  unfold tailWord_119177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346742289249557656259785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2897828192833038437506523 4346742289249557656259785)
  ·
    refine ⟨3260056716937168242194839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4346742289249557656259785 3260056716937168242194839)
    ·
      refine ⟨4890085075405752363292259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260056716937168242194839 4890085075405752363292259)
      ·
        refine ⟨7335127613108628544938389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890085075405752363292259 7335127613108628544938389)
        ·
          refine ⟨343834106864466963043987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7335127613108628544938389 343834106864466963043987)
          ·
            refine ⟨515751160296700444565981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343834106864466963043987 515751160296700444565981)
            ·
              refine ⟨193406685111262666712243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515751160296700444565981 193406685111262666712243)
              ·
                refine ⟨290110027666894000068365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193406685111262666712243 290110027666894000068365)
                ·
                  refine ⟨108791260375085250025637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290110027666894000068365 108791260375085250025637)
                  ·
                    refine ⟨20398361320328484379807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108791260375085250025637 20398361320328484379807)
                    ·
                      rfl

theorem cell23_119177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_119177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119177 prefixEnd_119177 := by exact prefixLift 119177
  have htrace : WordTrace (prefixWord ++ tailWord_119177) baseStart_119177 baseEnd_119177 := by
    simpa [prefixWord, tailWord_119177, baseEnd_119177] using wordTrace_append hprefix tailTrace_119177
  have hstable : (prefixWord ++ tailWord_119177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119177).length < 2 ^ (prefixWord ++ tailWord_119177).sum := by decide
  have hdescent : baseEnd_119177 < baseStart_119177 := by decide
  rcases family_descends (prefixWord ++ tailWord_119177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119228 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_119228 : Nat := 118140960795 + 119228 * 2 ^ 59
def prefixEnd_119228 : Nat := 4983230072969 + 3 ^ 40 * 119228 * 2
def baseEnd_119228 : Nat := 20407090491454917867229

theorem tailTrace_119228 : CollatzResearch.WordTrace tailWord_119228 prefixEnd_119228 20407090491454917867229 := by
  unfold tailWord_119228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174301206032396683183169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2899068274709862244244225 2174301206032396683183169)
  ·
    refine ⟨1630725904524297512387377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2174301206032396683183169 1630725904524297512387377)
    ·
      refine ⟨1223044428393223134290533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1630725904524297512387377 1223044428393223134290533)
      ·
        refine ⟨229320830323729337679475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1223044428393223134290533 229320830323729337679475)
        ·
          refine ⟨343981245485594006519213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229320830323729337679475 343981245485594006519213)
          ·
            refine ⟨128992967057097752444705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343981245485594006519213 128992967057097752444705)
            ·
              refine ⟨96744725292823314333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128992967057097752444705 96744725292823314333529)
              ·
                refine ⟨72558543969617485750147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96744725292823314333529 72558543969617485750147)
                ·
                  refine ⟨108837815954426228625221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72558543969617485750147 108837815954426228625221)
                  ·
                    refine ⟨20407090491454917867229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108837815954426228625221 20407090491454917867229)
                    ·
                      rfl

theorem cell23_119228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_119228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119228 prefixEnd_119228 := by exact prefixLift 119228
  have htrace : WordTrace (prefixWord ++ tailWord_119228) baseStart_119228 baseEnd_119228 := by
    simpa [prefixWord, tailWord_119228, baseEnd_119228] using wordTrace_append hprefix tailTrace_119228
  have hstable : (prefixWord ++ tailWord_119228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119228).length < 2 ^ (prefixWord ++ tailWord_119228).sum := by decide
  have hdescent : baseEnd_119228 < baseStart_119228 := by decide
  rcases family_descends (prefixWord ++ tailWord_119228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119254 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_119254 : Nat := 118140960795 + 119254 * 2 ^ 59
def prefixEnd_119254 : Nat := 4983230072969 + 3 ^ 40 * 119254 * 2
def baseEnd_119254 : Nat := 20411540657127217292189

theorem tailTrace_119254 : CollatzResearch.WordTrace tailWord_119254 prefixEnd_119254 20411540657127217292189 := by
  unfold tailWord_119254
  simp only [CollatzResearch.WordTrace]
  refine ⟨271846919373162487925801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2899700473313733204541877 271846919373162487925801)
  ·
    refine ⟨203885189529871865944351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271846919373162487925801 203885189529871865944351)
    ·
      refine ⟨305827784294807798916527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203885189529871865944351 305827784294807798916527)
      ·
        refine ⟨458741676442211698374791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305827784294807798916527 458741676442211698374791)
        ·
          refine ⟨688112514663317547562187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458741676442211698374791 688112514663317547562187)
          ·
            refine ⟨1032168771994976321343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688112514663317547562187 1032168771994976321343281)
            ·
              refine ⟨774126578996232241007461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032168771994976321343281 774126578996232241007461)
              ·
                refine ⟨145148733561793545188899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774126578996232241007461 145148733561793545188899)
                ·
                  refine ⟨217723100342690317783349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145148733561793545188899 217723100342690317783349)
                  ·
                    refine ⟨20411540657127217292189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217723100342690317783349 20411540657127217292189)
                    ·
                      rfl

theorem cell23_119254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_119254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119254 prefixEnd_119254 := by exact prefixLift 119254
  have htrace : WordTrace (prefixWord ++ tailWord_119254) baseStart_119254 baseEnd_119254 := by
    simpa [prefixWord, tailWord_119254, baseEnd_119254] using wordTrace_append hprefix tailTrace_119254
  have hstable : (prefixWord ++ tailWord_119254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119254).length < 2 ^ (prefixWord ++ tailWord_119254).sum := by decide
  have hdescent : baseEnd_119254 < baseStart_119254 := by decide
  rcases family_descends (prefixWord ++ tailWord_119254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119257 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_119257 : Nat := 118140960795 + 119257 * 2 ^ 59
def prefixEnd_119257 : Nat := 4983230072969 + 3 ^ 40 * 119257 * 2
def baseEnd_119257 : Nat := 61236162413345140139053

theorem tailTrace_119257 : CollatzResearch.WordTrace tailWord_119257 prefixEnd_119257 61236162413345140139053 := by
  unfold tailWord_119257
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349660128959731319172025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2899773419306487546114683 4349660128959731319172025)
  ·
    refine ⟨3262245096719798489379019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4349660128959731319172025 3262245096719798489379019)
    ·
      refine ⟨4893367645079697734068529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262245096719798489379019 4893367645079697734068529)
      ·
        refine ⟨3670025733809773300551397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4893367645079697734068529 3670025733809773300551397)
        ·
          refine ⟨688129825089332493853387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3670025733809773300551397 688129825089332493853387)
          ·
            refine ⟨1032194737633998740780081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688129825089332493853387 1032194737633998740780081)
            ·
              refine ⟨774146053225499055585061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032194737633998740780081 774146053225499055585061)
              ·
                refine ⟨145152384979781072922199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774146053225499055585061 145152384979781072922199)
                ·
                  refine ⟨217728577469671609383299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145152384979781072922199 217728577469671609383299)
                  ·
                    refine ⟨326592866204507414074949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217728577469671609383299 326592866204507414074949)
                    ·
                      refine ⟨61236162413345140139053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 326592866204507414074949 61236162413345140139053)
                      ·
                        rfl

theorem cell23_119257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_119257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119257 prefixEnd_119257 := by exact prefixLift 119257
  have htrace : WordTrace (prefixWord ++ tailWord_119257) baseStart_119257 baseEnd_119257 := by
    simpa [prefixWord, tailWord_119257, baseEnd_119257] using wordTrace_append hprefix tailTrace_119257
  have hstable : (prefixWord ++ tailWord_119257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119257).length < 2 ^ (prefixWord ++ tailWord_119257).sum := by decide
  have hdescent : baseEnd_119257 < baseStart_119257 := by decide
  rcases family_descends (prefixWord ++ tailWord_119257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119274 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_119274 : Nat := 118140960795 + 119274 * 2 ^ 59
def prefixEnd_119274 : Nat := 4983230072969 + 3 ^ 40 * 119274 * 2
def baseEnd_119274 : Nat := 61244891584471573626475

theorem tailTrace_119274 : CollatzResearch.WordTrace tailWord_119274 prefixEnd_119274 61244891584471573626475 := by
  unfold tailWord_119274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087570042474535805635219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2900186779932095481693917 1087570042474535805635219)
  ·
    refine ⟨1631355063711803708452829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1087570042474535805635219 1631355063711803708452829)
    ·
      refine ⟨611758148891926390669811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1631355063711803708452829 611758148891926390669811)
      ·
        refine ⟨917637223337889586004717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611758148891926390669811 917637223337889586004717)
        ·
          refine ⟨344113958751708594751769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917637223337889586004717 344113958751708594751769)
          ·
            refine ⟨258085469063781446063827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344113958751708594751769 258085469063781446063827)
            ·
              refine ⟨387128203595672169095741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258085469063781446063827 387128203595672169095741)
              ·
                refine ⟨145173076348377063410903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387128203595672169095741 145173076348377063410903)
                ·
                  refine ⟨217759614522565595116355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145173076348377063410903 217759614522565595116355)
                  ·
                    refine ⟨326639421783848392674533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217759614522565595116355 326639421783848392674533)
                    ·
                      refine ⟨61244891584471573626475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 326639421783848392674533 61244891584471573626475)
                      ·
                        rfl

theorem cell23_119274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_119274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119274 prefixEnd_119274 := by exact prefixLift 119274
  have htrace : WordTrace (prefixWord ++ tailWord_119274) baseStart_119274 baseEnd_119274 := by
    simpa [prefixWord, tailWord_119274, baseEnd_119274] using wordTrace_append hprefix tailTrace_119274
  have hstable : (prefixWord ++ tailWord_119274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119274).length < 2 ^ (prefixWord ++ tailWord_119274).sum := by decide
  have hdescent : baseEnd_119274 < baseStart_119274 := by decide
  rcases family_descends (prefixWord ++ tailWord_119274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119324 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_119324 : Nat := 118140960795 + 119324 * 2 ^ 59
def prefixEnd_119324 : Nat := 4983230072969 + 3 ^ 40 * 119324 * 2
def baseEnd_119324 : Nat := 61270565617196378001245

theorem tailTrace_119324 : CollatzResearch.WordTrace tailWord_119324 prefixEnd_119324 61270565617196378001245 := by
  unfold tailWord_119324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176051909858500880930513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2901402546478001174574017 2176051909858500880930513)
  ·
    refine ⟨1632038932393875660697885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176051909858500880930513 1632038932393875660697885)
    ·
      refine ⟨612014599647703372761707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1632038932393875660697885 612014599647703372761707)
      ·
        refine ⟨918021899471555059142561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612014599647703372761707 918021899471555059142561)
        ·
          refine ⟨688516424603666294356921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918021899471555059142561 688516424603666294356921)
          ·
            refine ⟨516387318452749720767691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688516424603666294356921 516387318452749720767691)
            ·
              refine ⟨774580977679124581151537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516387318452749720767691 774580977679124581151537)
              ·
                refine ⟨580935733259343435863653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774580977679124581151537 580935733259343435863653)
                ·
                  refine ⟨108925449986126894224435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580935733259343435863653 108925449986126894224435)
                  ·
                    refine ⟨163388174979190341336653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108925449986126894224435 163388174979190341336653)
                    ·
                      refine ⟨61270565617196378001245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163388174979190341336653 61270565617196378001245)
                      ·
                        rfl

theorem cell23_119324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_119324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119324 prefixEnd_119324 := by exact prefixLift 119324
  have htrace : WordTrace (prefixWord ++ tailWord_119324) baseStart_119324 baseEnd_119324 := by
    simpa [prefixWord, tailWord_119324, baseEnd_119324] using wordTrace_append hprefix tailTrace_119324
  have hstable : (prefixWord ++ tailWord_119324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119324).length < 2 ^ (prefixWord ++ tailWord_119324).sum := by decide
  have hdescent : baseEnd_119324 < baseStart_119324 := by decide
  rcases family_descends (prefixWord ++ tailWord_119324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119325 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_119325 : Nat := 118140960795 + 119325 * 2 ^ 59
def prefixEnd_119325 : Nat := 4983230072969 + 3 ^ 40 * 119325 * 2
def baseEnd_119325 : Nat := 61271079097850874088741

theorem tailTrace_119325 : CollatzResearch.WordTrace tailWord_119325 prefixEnd_119325 61271079097850874088741 := by
  unfold tailWord_119325
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352140292713378932647429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2901426861808919288431619 4352140292713378932647429)
  ·
    refine ⟨816026304883758549871393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4352140292713378932647429 816026304883758549871393)
    ·
      refine ⟨612019728662818912403545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 816026304883758549871393 612019728662818912403545)
      ·
        refine ⟨459014796497114184302659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612019728662818912403545 459014796497114184302659)
        ·
          refine ⟨688522194745671276453989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459014796497114184302659 688522194745671276453989)
          ·
            refine ⟨129097911514813364335123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 688522194745671276453989 129097911514813364335123)
            ·
              refine ⟨193646867272220046502685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129097911514813364335123 193646867272220046502685)
              ·
                refine ⟨72617575227082517438507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193646867272220046502685 72617575227082517438507)
                ·
                  refine ⟨108926362840623776157761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72617575227082517438507 108926362840623776157761)
                  ·
                    refine ⟨81694772130467832118321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108926362840623776157761 81694772130467832118321)
                    ·
                      refine ⟨61271079097850874088741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81694772130467832118321 61271079097850874088741)
                      ·
                        rfl

theorem cell23_119325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_119325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119325 prefixEnd_119325 := by exact prefixLift 119325
  have htrace : WordTrace (prefixWord ++ tailWord_119325) baseStart_119325 baseEnd_119325 := by
    simpa [prefixWord, tailWord_119325, baseEnd_119325] using wordTrace_append hprefix tailTrace_119325
  have hstable : (prefixWord ++ tailWord_119325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119325).length < 2 ^ (prefixWord ++ tailWord_119325).sum := by decide
  have hdescent : baseEnd_119325 < baseStart_119325 := by decide
  rcases family_descends (prefixWord ++ tailWord_119325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119340 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_119340 : Nat := 118140960795 + 119340 * 2 ^ 59
def prefixEnd_119340 : Nat := 4983230072969 + 3 ^ 40 * 119340 * 2
def baseEnd_119340 : Nat := 20426260435889438467057

theorem tailTrace_119340 : CollatzResearch.WordTrace tailWord_119340 prefixEnd_119340 20426260435889438467057 := by
  unfold tailWord_119340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176343693829518247221737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2901791591772690996295649 2176343693829518247221737)
  ·
    refine ⟨1632257770372138685416303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176343693829518247221737 1632257770372138685416303)
    ·
      refine ⟨2448386655558208028124455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632257770372138685416303 2448386655558208028124455)
      ·
        refine ⟨3672579983337312042186683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448386655558208028124455 3672579983337312042186683)
        ·
          refine ⟨5508869975005968063280025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672579983337312042186683 5508869975005968063280025)
          ·
            refine ⟨4131652481254476047460019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508869975005968063280025 4131652481254476047460019)
            ·
              refine ⟨6197478721881714071190029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131652481254476047460019 6197478721881714071190029)
              ·
                refine ⟨2324054520705642776696261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6197478721881714071190029 2324054520705642776696261)
                ·
                  refine ⟨435760222632308020630549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324054520705642776696261 435760222632308020630549)
                  ·
                    refine ⟨20426260435889438467057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 435760222632308020630549 20426260435889438467057)
                    ·
                      rfl

theorem cell23_119340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_119340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119340 prefixEnd_119340 := by exact prefixLift 119340
  have htrace : WordTrace (prefixWord ++ tailWord_119340) baseStart_119340 baseEnd_119340 := by
    simpa [prefixWord, tailWord_119340, baseEnd_119340] using wordTrace_append hprefix tailTrace_119340
  have hstable : (prefixWord ++ tailWord_119340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119340).length < 2 ^ (prefixWord ++ tailWord_119340).sum := by decide
  have hdescent : baseEnd_119340 < baseStart_119340 := by decide
  rcases family_descends (prefixWord ++ tailWord_119340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119342 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_119342 : Nat := 118140960795 + 119342 * 2 ^ 59
def prefixEnd_119342 : Nat := 4983230072969 + 3 ^ 40 * 119342 * 2
def baseEnd_119342 : Nat := 61279808268977307576163

theorem tailTrace_119342 : CollatzResearch.WordTrace tailWord_119342 prefixEnd_119342 61279808268977307576163 := by
  unfold tailWord_119342
  simp only [CollatzResearch.WordTrace]
  refine ⟨544095041706473854502035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2901840222434527224010853 544095041706473854502035)
  ·
    refine ⟨816142562559710781753053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 544095041706473854502035 816142562559710781753053)
    ·
      refine ⟨306053460959891543157395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 816142562559710781753053 306053460959891543157395)
      ·
        refine ⟨459080191439837314736093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306053460959891543157395 459080191439837314736093)
        ·
          refine ⟨172155071789938993026035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459080191439837314736093 172155071789938993026035)
          ·
            refine ⟨258232607684908489539053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172155071789938993026035 258232607684908489539053)
            ·
              refine ⟨96837227881840683577145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258232607684908489539053 96837227881840683577145)
              ·
                refine ⟨72627920911380512682859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96837227881840683577145 72627920911380512682859)
                ·
                  refine ⟨108941881367070769024289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72627920911380512682859 108941881367070769024289)
                  ·
                    refine ⟨81706411025303076768217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108941881367070769024289 81706411025303076768217)
                    ·
                      refine ⟨61279808268977307576163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81706411025303076768217 61279808268977307576163)
                      ·
                        rfl

theorem cell23_119342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_119342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119342 prefixEnd_119342 := by exact prefixLift 119342
  have htrace : WordTrace (prefixWord ++ tailWord_119342) baseStart_119342 baseEnd_119342 := by
    simpa [prefixWord, tailWord_119342, baseEnd_119342] using wordTrace_append hprefix tailTrace_119342
  have hstable : (prefixWord ++ tailWord_119342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119342).length < 2 ^ (prefixWord ++ tailWord_119342).sum := by decide
  have hdescent : baseEnd_119342 < baseStart_119342 := by decide
  rcases family_descends (prefixWord ++ tailWord_119342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119367 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_119367 : Nat := 118140960795 + 119367 * 2 ^ 59
def prefixEnd_119367 : Nat := 4983230072969 + 3 ^ 40 * 119367 * 2
def baseEnd_119367 : Nat := 61292645285339709763547

theorem tailTrace_119367 : CollatzResearch.WordTrace tailWord_119367 prefixEnd_119367 61292645285339709763547 := by
  unfold tailWord_119367
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353672158561220105676355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2902448105707480070450903 4353672158561220105676355)
  ·
    refine ⟨6530508237841830158514533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4353672158561220105676355 6530508237841830158514533)
    ·
      refine ⟨1224470294595343154721475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6530508237841830158514533 1224470294595343154721475)
      ·
        refine ⟨1836705441893014732082213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224470294595343154721475 1836705441893014732082213)
        ·
          refine ⟨344382270354940262265415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1836705441893014732082213 344382270354940262265415)
          ·
            refine ⟨516573405532410393398123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344382270354940262265415 516573405532410393398123)
            ·
              refine ⟨774860108298615590097185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516573405532410393398123 774860108298615590097185)
              ·
                refine ⟨581145081223961692572889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774860108298615590097185 581145081223961692572889)
                ·
                  refine ⟨435858810917971269429667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581145081223961692572889 435858810917971269429667)
                  ·
                    refine ⟨653788216376956904144501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435858810917971269429667 653788216376956904144501)
                    ·
                      refine ⟨61292645285339709763547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 653788216376956904144501 61292645285339709763547)
                      ·
                        rfl

theorem cell23_119367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_119367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119367 prefixEnd_119367 := by exact prefixLift 119367
  have htrace : WordTrace (prefixWord ++ tailWord_119367) baseStart_119367 baseEnd_119367 := by
    simpa [prefixWord, tailWord_119367, baseEnd_119367] using wordTrace_append hprefix tailTrace_119367
  have hstable : (prefixWord ++ tailWord_119367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119367).length < 2 ^ (prefixWord ++ tailWord_119367).sum := by decide
  have hdescent : baseEnd_119367 < baseStart_119367 := by decide
  rcases family_descends (prefixWord ++ tailWord_119367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119434 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_119434 : Nat := 118140960795 + 119434 * 2 ^ 59
def prefixEnd_119434 : Nat := 4983230072969 + 3 ^ 40 * 119434 * 2
def baseEnd_119434 : Nat := 20442349496396982541913

theorem tailTrace_119434 : CollatzResearch.WordTrace tailWord_119434 prefixEnd_119434 20442349496396982541913 := by
  unfold tailWord_119434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089028962329622637091339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2904077232878993698910237 1089028962329622637091339)
  ·
    refine ⟨1633543443494433955637009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089028962329622637091339 1633543443494433955637009)
    ·
      refine ⟨1225157582620825466727757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1633543443494433955637009 1225157582620825466727757)
      ·
        refine ⟨459434093482809550022909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1225157582620825466727757 459434093482809550022909)
        ·
          refine ⟨172287785056053581258591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459434093482809550022909 172287785056053581258591)
          ·
            refine ⟨258431677584080371887887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172287785056053581258591 258431677584080371887887)
            ·
              refine ⟨387647516376120557831831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258431677584080371887887 387647516376120557831831)
              ·
                refine ⟨581471274564180836747747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387647516376120557831831 581471274564180836747747)
                ·
                  refine ⟨872206911846271255121621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581471274564180836747747 872206911846271255121621)
                  ·
                    refine ⟨20442349496396982541913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 872206911846271255121621 20442349496396982541913)
                    ·
                      rfl

theorem cell23_119434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_119434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119434 prefixEnd_119434 := by exact prefixLift 119434
  have htrace : WordTrace (prefixWord ++ tailWord_119434) baseStart_119434 baseEnd_119434 := by
    simpa [prefixWord, tailWord_119434, baseEnd_119434] using wordTrace_append hprefix tailTrace_119434
  have hstable : (prefixWord ++ tailWord_119434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119434).length < 2 ^ (prefixWord ++ tailWord_119434).sum := by decide
  have hdescent : baseEnd_119434 < baseStart_119434 := by decide
  rcases family_descends (prefixWord ++ tailWord_119434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119498 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_119498 : Nat := 118140960795 + 119498 * 2 ^ 59
def prefixEnd_119498 : Nat := 4983230072969 + 3 ^ 40 * 119498 * 2
def baseEnd_119498 : Nat := 20453303750359565741815

theorem tailTrace_119498 : CollatzResearch.WordTrace tailWord_119498 prefixEnd_119498 20453303750359565741815 := by
  unfold tailWord_119498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089612530271657369673787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2905633414057752985796765 1089612530271657369673787)
  ·
    refine ⟨1634418795407486054510681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089612530271657369673787 1634418795407486054510681)
    ·
      refine ⟨1225814096555614540883011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1634418795407486054510681 1225814096555614540883011)
      ·
        refine ⟨1838721144833421811324517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225814096555614540883011 1838721144833421811324517)
        ·
          refine ⟨344760214656266589623347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1838721144833421811324517 344760214656266589623347)
          ·
            refine ⟨517140321984399884435021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344760214656266589623347 517140321984399884435021)
            ·
              refine ⟨193927620744149956663133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517140321984399884435021 193927620744149956663133)
              ·
                refine ⟨72722857779056233748675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193927620744149956663133 72722857779056233748675)
                ·
                  refine ⟨109084286668584350623013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72722857779056233748675 109084286668584350623013)
                  ·
                    refine ⟨20453303750359565741815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109084286668584350623013 20453303750359565741815)
                    ·
                      rfl

theorem cell23_119498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_119498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119498 prefixEnd_119498 := by exact prefixLift 119498
  have htrace : WordTrace (prefixWord ++ tailWord_119498) baseStart_119498 baseEnd_119498 := by
    simpa [prefixWord, tailWord_119498, baseEnd_119498] using wordTrace_append hprefix tailTrace_119498
  have hstable : (prefixWord ++ tailWord_119498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119498).length < 2 ^ (prefixWord ++ tailWord_119498).sum := by decide
  have hdescent : baseEnd_119498 < baseStart_119498 := by decide
  rcases family_descends (prefixWord ++ tailWord_119498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119508 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_119508 : Nat := 118140960795 + 119508 * 2 ^ 59
def prefixEnd_119508 : Nat := 4983230072969 + 3 ^ 40 * 119508 * 2
def baseEnd_119508 : Nat := 61365046057623658100399

theorem tailTrace_119508 : CollatzResearch.WordTrace tailWord_119508 prefixEnd_119508 61365046057623658100399 := by
  unfold tailWord_119508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179407425525200593279589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2905876567366934124372785 2179407425525200593279589)
  ·
    refine ⟨408638892285975111239923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2179407425525200593279589 408638892285975111239923)
    ·
      refine ⟨612958338428962666859885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408638892285975111239923 612958338428962666859885)
      ·
        refine ⟨229859376910861000072457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612958338428962666859885 229859376910861000072457)
        ·
          refine ⟨172394532683145750054343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229859376910861000072457 172394532683145750054343)
          ·
            refine ⟨258591799024718625081515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172394532683145750054343 258591799024718625081515)
            ·
              refine ⟨387887698537077937622273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258591799024718625081515 387887698537077937622273)
              ·
                refine ⟨290915773902808453216705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387887698537077937622273 290915773902808453216705)
                ·
                  refine ⟨218186830427106339912529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290915773902808453216705 218186830427106339912529)
                  ·
                    refine ⟨163640122820329754934397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218186830427106339912529 163640122820329754934397)
                    ·
                      refine ⟨61365046057623658100399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163640122820329754934397 61365046057623658100399)
                      ·
                        rfl

theorem cell23_119508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_119508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119508 prefixEnd_119508 := by exact prefixLift 119508
  have htrace : WordTrace (prefixWord ++ tailWord_119508) baseStart_119508 baseEnd_119508 := by
    simpa [prefixWord, tailWord_119508, baseEnd_119508] using wordTrace_append hprefix tailTrace_119508
  have hstable : (prefixWord ++ tailWord_119508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119508).length < 2 ^ (prefixWord ++ tailWord_119508).sum := by decide
  have hdescent : baseEnd_119508 < baseStart_119508 := by decide
  rcases family_descends (prefixWord ++ tailWord_119508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119528 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 6]
def baseStart_119528 : Nat := 118140960795 + 119528 * 2 ^ 59
def prefixEnd_119528 : Nat := 4983230072969 + 3 ^ 40 * 119528 * 2
def baseEnd_119528 : Nat := 6819479518968175538923

theorem tailTrace_119528 : CollatzResearch.WordTrace tailWord_119528 prefixEnd_119528 6819479518968175538923 := by
  unfold tailWord_119528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179772155488972301143619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2906362873985296401524825 2179772155488972301143619)
  ·
    refine ⟨3269658233233458451715429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179772155488972301143619 3269658233233458451715429)
    ·
      refine ⟨613060918731273459696643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3269658233233458451715429 613060918731273459696643)
      ·
        refine ⟨919591378096910189544965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613060918731273459696643 919591378096910189544965)
        ·
          refine ⟨172423383393170660539681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 919591378096910189544965 172423383393170660539681)
          ·
            refine ⟨129317537544877995404761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172423383393170660539681 129317537544877995404761)
            ·
              refine ⟨96988153158658496553571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129317537544877995404761 96988153158658496553571)
              ·
                refine ⟨145482229737987744830357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96988153158658496553571 145482229737987744830357)
                ·
                  refine ⟨6819479518968175538923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145482229737987744830357 6819479518968175538923)
                  ·
                    rfl

theorem cell23_119528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_119528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119528 prefixEnd_119528 := by exact prefixLift 119528
  have htrace : WordTrace (prefixWord ++ tailWord_119528) baseStart_119528 baseEnd_119528 := by
    simpa [prefixWord, tailWord_119528, baseEnd_119528] using wordTrace_append hprefix tailTrace_119528
  have hstable : (prefixWord ++ tailWord_119528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119528).length < 2 ^ (prefixWord ++ tailWord_119528).sum := by decide
  have hdescent : baseEnd_119528 < baseStart_119528 := by decide
  rcases family_descends (prefixWord ++ tailWord_119528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119544 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_119544 : Nat := 118140960795 + 119544 * 2 ^ 59
def prefixEnd_119544 : Nat := 4983230072969 + 3 ^ 40 * 119544 * 2
def baseEnd_119544 : Nat := 61383531361185517250233

theorem tailTrace_119544 : CollatzResearch.WordTrace tailWord_119544 prefixEnd_119544 61383531361185517250233 := by
  unfold tailWord_119544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180063939459989667434843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2906751919279986223246457 2180063939459989667434843)
  ·
    refine ⟨3270095909189984501152265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180063939459989667434843 3270095909189984501152265)
    ·
      refine ⟨2452571931892488375864199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270095909189984501152265 2452571931892488375864199)
      ·
        refine ⟨3678857897838732563796299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452571931892488375864199 3678857897838732563796299)
        ·
          refine ⟨5518286846758098845694449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678857897838732563796299 5518286846758098845694449)
          ·
            refine ⟨4138715135068574134270837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5518286846758098845694449 4138715135068574134270837)
            ·
              refine ⟨388004543912678825087891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4138715135068574134270837 388004543912678825087891)
              ·
                refine ⟨582006815869018237631837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388004543912678825087891 582006815869018237631837)
                ·
                  refine ⟨218252555950881839111939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582006815869018237631837 218252555950881839111939)
                  ·
                    refine ⟨327378833926322758667909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218252555950881839111939 327378833926322758667909)
                    ·
                      refine ⟨61383531361185517250233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 327378833926322758667909 61383531361185517250233)
                      ·
                        rfl

theorem cell23_119544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_119544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119544 prefixEnd_119544 := by exact prefixLift 119544
  have htrace : WordTrace (prefixWord ++ tailWord_119544) baseStart_119544 baseEnd_119544 := by
    simpa [prefixWord, tailWord_119544, baseEnd_119544] using wordTrace_append hprefix tailTrace_119544
  have hstable : (prefixWord ++ tailWord_119544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119544).length < 2 ^ (prefixWord ++ tailWord_119544).sum := by decide
  have hdescent : baseEnd_119544 < baseStart_119544 := by decide
  rcases family_descends (prefixWord ++ tailWord_119544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119548 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_119548 : Nat := 118140960795 + 119548 * 2 ^ 59
def prefixEnd_119548 : Nat := 4983230072969 + 3 ^ 40 * 119548 * 2
def baseEnd_119548 : Nat := 61385585283803501600215

theorem tailTrace_119548 : CollatzResearch.WordTrace tailWord_119548 prefixEnd_119548 61385585283803501600215 := by
  unfold tailWord_119548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180136885452744009007649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2906849180603658678676865 2180136885452744009007649)
  ·
    refine ⟨1635102664089558006755737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2180136885452744009007649 1635102664089558006755737)
    ·
      refine ⟨1226326998067168505066803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1635102664089558006755737 1226326998067168505066803)
      ·
        refine ⟨1839490497100752757600205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226326998067168505066803 1839490497100752757600205)
        ·
          refine ⟨689808936412782284100077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1839490497100752757600205 689808936412782284100077)
          ·
            refine ⟨258678351154793356537529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689808936412782284100077 258678351154793356537529)
            ·
              refine ⟨194008763366095017403147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258678351154793356537529 194008763366095017403147)
              ·
                refine ⟨291013145049142526104721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194008763366095017403147 291013145049142526104721)
                ·
                  refine ⟨218259858786856894578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291013145049142526104721 218259858786856894578541)
                  ·
                    refine ⟨81847447045071335466953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218259858786856894578541 81847447045071335466953)
                    ·
                      refine ⟨61385585283803501600215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81847447045071335466953 61385585283803501600215)
                      ·
                        rfl

theorem cell23_119548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_119548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119548 prefixEnd_119548 := by exact prefixLift 119548
  have htrace : WordTrace (prefixWord ++ tailWord_119548) baseStart_119548 baseEnd_119548 := by
    simpa [prefixWord, tailWord_119548, baseEnd_119548] using wordTrace_append hprefix tailTrace_119548
  have hstable : (prefixWord ++ tailWord_119548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119548).length < 2 ^ (prefixWord ++ tailWord_119548).sum := by decide
  have hdescent : baseEnd_119548 < baseStart_119548 := by decide
  rcases family_descends (prefixWord ++ tailWord_119548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119571 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 2, 4]
def baseStart_119571 : Nat := 118140960795 + 119571 * 2 ^ 59
def prefixEnd_119571 : Nat := 4983230072969 + 3 ^ 40 * 119571 * 2
def baseEnd_119571 : Nat := 20465798446285637204203

theorem tailTrace_119571 : CollatzResearch.WordTrace tailWord_119571 prefixEnd_119571 20465798446285637204203 := by
  unfold tailWord_119571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361112649822162946102567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2907408433214775297401711 4361112649822162946102567)
  ·
    refine ⟨6541668974733244419153851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361112649822162946102567 6541668974733244419153851)
    ·
      refine ⟨9812503462099866628730777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6541668974733244419153851 9812503462099866628730777)
      ·
        refine ⟨7359377596574899971548083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812503462099866628730777 7359377596574899971548083)
        ·
          refine ⟨11039066394862349957322125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359377596574899971548083 11039066394862349957322125)
          ·
            refine ⟨4139649898073381233995797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039066394862349957322125 4139649898073381233995797)
            ·
              refine ⟨194046088972189745343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4139649898073381233995797 194046088972189745343553)
              ·
                refine ⟨145534566729142309007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194046088972189745343553 145534566729142309007665)
                ·
                  refine ⟨109150925046856731755749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145534566729142309007665 109150925046856731755749)
                  ·
                    refine ⟨20465798446285637204203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109150925046856731755749 20465798446285637204203)
                    ·
                      rfl

theorem cell23_119571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 4].length) (baseStart_119571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119571 prefixEnd_119571 := by exact prefixLift 119571
  have htrace : WordTrace (prefixWord ++ tailWord_119571) baseStart_119571 baseEnd_119571 := by
    simpa [prefixWord, tailWord_119571, baseEnd_119571] using wordTrace_append hprefix tailTrace_119571
  have hstable : (prefixWord ++ tailWord_119571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119571).length < 2 ^ (prefixWord ++ tailWord_119571).sum := by decide
  have hdescent : baseEnd_119571 < baseStart_119571 := by decide
  rcases family_descends (prefixWord ++ tailWord_119571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119577 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_119577 : Nat := 118140960795 + 119577 * 2 ^ 59
def prefixEnd_119577 : Nat := 4983230072969 + 3 ^ 40 * 119577 * 2
def baseEnd_119577 : Nat := 61400476222783888137581

theorem tailTrace_119577 : CollatzResearch.WordTrace tailWord_119577 prefixEnd_119577 61400476222783888137581 := by
  unfold tailWord_119577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361331487800425970820985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2907554325200283980547323 4361331487800425970820985)
  ·
    refine ⟨3270998615850319478115739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4361331487800425970820985 3270998615850319478115739)
    ·
      refine ⟨4906497923775479217173609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270998615850319478115739 4906497923775479217173609)
      ·
        refine ⟨3679873442831609412880207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4906497923775479217173609 3679873442831609412880207)
        ·
          refine ⟨5519810164247414119320311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679873442831609412880207 5519810164247414119320311)
          ·
            refine ⟨8279715246371121178980467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519810164247414119320311 8279715246371121178980467)
            ·
              refine ⟨12419572869556681768470701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279715246371121178980467 12419572869556681768470701)
              ·
                refine ⟨4657339826083755663176513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12419572869556681768470701 4657339826083755663176513)
                ·
                  refine ⟨3493004869562816747382385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657339826083755663176513 3493004869562816747382385)
                  ·
                    refine ⟨2619753652172112560536789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493004869562816747382385 2619753652172112560536789)
                    ·
                      refine ⟨61400476222783888137581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2619753652172112560536789 61400476222783888137581)
                      ·
                        rfl

theorem cell23_119577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_119577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119577 prefixEnd_119577 := by exact prefixLift 119577
  have htrace : WordTrace (prefixWord ++ tailWord_119577) baseStart_119577 baseEnd_119577 := by
    simpa [prefixWord, tailWord_119577, baseEnd_119577] using wordTrace_append hprefix tailTrace_119577
  have hstable : (prefixWord ++ tailWord_119577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119577).length < 2 ^ (prefixWord ++ tailWord_119577).sum := by decide
  have hdescent : baseEnd_119577 < baseStart_119577 := by decide
  rcases family_descends (prefixWord ++ tailWord_119577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119578 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_119578 : Nat := 118140960795 + 119578 * 2 ^ 59
def prefixEnd_119578 : Nat := 4983230072969 + 3 ^ 40 * 119578 * 2
def baseEnd_119578 : Nat := 61400989703438384225077

theorem tailTrace_119578 : CollatzResearch.WordTrace tailWord_119578 prefixEnd_119578 61400989703438384225077 := by
  unfold tailWord_119578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090341990199200785401847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2907578640531202094404925 1090341990199200785401847)
  ·
    refine ⟨1635512985298801178102771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1090341990199200785401847 1635512985298801178102771)
    ·
      refine ⟨2453269477948201767154157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635512985298801178102771 2453269477948201767154157)
      ·
        refine ⟨919976054230575662682809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2453269477948201767154157 919976054230575662682809)
        ·
          refine ⟨689982040672931747012107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919976054230575662682809 689982040672931747012107)
          ·
            refine ⟨1034973061009397620518161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689982040672931747012107 1034973061009397620518161)
            ·
              refine ⟨776229795757048215388621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034973061009397620518161 776229795757048215388621)
              ·
                refine ⟨291086173408893080770733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776229795757048215388621 291086173408893080770733)
                ·
                  refine ⟨109157315028334905289025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291086173408893080770733 109157315028334905289025)
                  ·
                    refine ⟨81867986271251178966769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109157315028334905289025 81867986271251178966769)
                    ·
                      refine ⟨61400989703438384225077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81867986271251178966769 61400989703438384225077)
                      ·
                        rfl

theorem cell23_119578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_119578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119578 prefixEnd_119578 := by exact prefixLift 119578
  have htrace : WordTrace (prefixWord ++ tailWord_119578) baseStart_119578 baseEnd_119578 := by
    simpa [prefixWord, tailWord_119578, baseEnd_119578] using wordTrace_append hprefix tailTrace_119578
  have hstable : (prefixWord ++ tailWord_119578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119578).length < 2 ^ (prefixWord ++ tailWord_119578).sum := by decide
  have hdescent : baseEnd_119578 < baseStart_119578 := by decide
  rcases family_descends (prefixWord ++ tailWord_119578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119584 : List Nat := [2, 1, 1, 5, 1, 2, 3, 8]
def baseStart_119584 : Nat := 118140960795 + 119584 * 2 ^ 59
def prefixEnd_119584 : Nat := 4983230072969 + 3 ^ 40 * 119584 * 2
def baseEnd_119584 : Nat := 2274224836569087435187

theorem tailTrace_119584 : CollatzResearch.WordTrace tailWord_119584 prefixEnd_119584 2274224836569087435187 := by
  unfold tailWord_119584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180793399387533083162903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2907724532516710777550537 2180793399387533083162903)
  ·
    refine ⟨3271190099081299624744355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180793399387533083162903 3271190099081299624744355)
    ·
      refine ⟨4906785148621949437116533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271190099081299624744355 4906785148621949437116533)
      ·
        refine ⟨460011107683307759729675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4906785148621949437116533 460011107683307759729675)
        ·
          refine ⟨690016661524961639594513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460011107683307759729675 690016661524961639594513)
          ·
            refine ⟨517512496143721229695885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690016661524961639594513 517512496143721229695885)
            ·
              refine ⟨194067186053895461135957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517512496143721229695885 194067186053895461135957)
              ·
                refine ⟨2274224836569087435187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194067186053895461135957 2274224836569087435187)
                ·
                  rfl

theorem cell23_119584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_119584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119584 prefixEnd_119584 := by exact prefixLift 119584
  have htrace : WordTrace (prefixWord ++ tailWord_119584) baseStart_119584 baseEnd_119584 := by
    simpa [prefixWord, tailWord_119584, baseEnd_119584] using wordTrace_append hprefix tailTrace_119584
  have hstable : (prefixWord ++ tailWord_119584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119584).length < 2 ^ (prefixWord ++ tailWord_119584).sum := by decide
  have hdescent : baseEnd_119584 < baseStart_119584 := by decide
  rcases family_descends (prefixWord ++ tailWord_119584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119598 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_119598 : Nat := 118140960795 + 119598 * 2 ^ 59
def prefixEnd_119598 : Nat := 4983230072969 + 3 ^ 40 * 119598 * 2
def baseEnd_119598 : Nat := 61411259316528305974985

theorem tailTrace_119598 : CollatzResearch.WordTrace tailWord_119598 prefixEnd_119598 61411259316528305974985 := by
  unfold tailWord_119598
  simp only [CollatzResearch.WordTrace]
  refine ⟨545262177590543319666931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2908064947149564371556965 545262177590543319666931)
  ·
    refine ⟨817893266385814979500397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545262177590543319666931 817893266385814979500397)
    ·
      refine ⟨306709974894680617312649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 817893266385814979500397 306709974894680617312649)
      ·
        refine ⟨230032481171010462984487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306709974894680617312649 230032481171010462984487)
        ·
          refine ⟨345048721756515694476731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230032481171010462984487 345048721756515694476731)
          ·
            refine ⟨517573082634773541715097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345048721756515694476731 517573082634773541715097)
            ·
              refine ⟨388179811976080156286323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517573082634773541715097 388179811976080156286323)
              ·
                refine ⟨582269717964120234429485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388179811976080156286323 582269717964120234429485)
                ·
                  refine ⟨218351144236545087911057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582269717964120234429485 218351144236545087911057)
                  ·
                    refine ⟨163763358177408815933293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218351144236545087911057 163763358177408815933293)
                    ·
                      refine ⟨61411259316528305974985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163763358177408815933293 61411259316528305974985)
                      ·
                        rfl

theorem cell23_119598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_119598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119598 prefixEnd_119598 := by exact prefixLift 119598
  have htrace : WordTrace (prefixWord ++ tailWord_119598) baseStart_119598 baseEnd_119598 := by
    simpa [prefixWord, tailWord_119598, baseEnd_119598] using wordTrace_append hprefix tailTrace_119598
  have hstable : (prefixWord ++ tailWord_119598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119598).length < 2 ^ (prefixWord ++ tailWord_119598).sum := by decide
  have hdescent : baseEnd_119598 < baseStart_119598 := by decide
  rcases family_descends (prefixWord ++ tailWord_119598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119615 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 1, 2, 3]
def baseStart_119615 : Nat := 118140960795 + 119615 * 2 ^ 59
def prefixEnd_119615 : Nat := 4983230072969 + 3 ^ 40 * 119615 * 2
def baseEnd_119615 : Nat := 61419988487654739462407

theorem tailTrace_119615 : CollatzResearch.WordTrace tailWord_119615 prefixEnd_119615 61419988487654739462407 := by
  unfold tailWord_119615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362717461662758460704299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2908478307775172307136199 4362717461662758460704299)
  ·
    refine ⟨6544076192494137691056449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4362717461662758460704299 6544076192494137691056449)
    ·
      refine ⟨4908057144370603268292337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6544076192494137691056449 4908057144370603268292337)
      ·
        refine ⟨3681042858277952451219253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4908057144370603268292337 3681042858277952451219253)
        ·
          refine ⟨345097767963558042301805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3681042858277952451219253 345097767963558042301805)
          ·
            refine ⟨129411662986334265863177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345097767963558042301805 129411662986334265863177)
            ·
              refine ⟨97058747239750699397383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129411662986334265863177 97058747239750699397383)
              ·
                refine ⟨145588120859626049096075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97058747239750699397383 145588120859626049096075)
                ·
                  refine ⟨218382181289439073644113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145588120859626049096075 218382181289439073644113)
                  ·
                    refine ⟨163786635967079305233085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218382181289439073644113 163786635967079305233085)
                    ·
                      refine ⟨61419988487654739462407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163786635967079305233085 61419988487654739462407)
                      ·
                        rfl

theorem cell23_119615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_119615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119615 prefixEnd_119615 := by exact prefixLift 119615
  have htrace : WordTrace (prefixWord ++ tailWord_119615) baseStart_119615 baseEnd_119615 := by
    simpa [prefixWord, tailWord_119615, baseEnd_119615] using wordTrace_append hprefix tailTrace_119615
  have hstable : (prefixWord ++ tailWord_119615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119615).length < 2 ^ (prefixWord ++ tailWord_119615).sum := by decide
  have hdescent : baseEnd_119615 < baseStart_119615 := by decide
  rcases family_descends (prefixWord ++ tailWord_119615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119621 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_119621 : Nat := 118140960795 + 119621 * 2 ^ 59
def prefixEnd_119621 : Nat := 4983230072969 + 3 ^ 40 * 119621 * 2
def baseEnd_119621 : Nat := 61423069371581715987379

theorem tailTrace_119621 : CollatzResearch.WordTrace tailWord_119621 prefixEnd_119621 61423069371581715987379 := by
  unfold tailWord_119621
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362936299641021485422717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2908624199760680990281811 4362936299641021485422717)
  ·
    refine ⟨1636101112365383057033519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4362936299641021485422717 1636101112365383057033519)
    ·
      refine ⟨2454151668548074585550279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636101112365383057033519 2454151668548074585550279)
      ·
        refine ⟨3681227502822111878325419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454151668548074585550279 3681227502822111878325419)
        ·
          refine ⟨5521841254233167817488129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681227502822111878325419 5521841254233167817488129)
          ·
            refine ⟨4141380940674875863116097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521841254233167817488129 4141380940674875863116097)
            ·
              refine ⟨3106035705506156897337073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141380940674875863116097 3106035705506156897337073)
              ·
                refine ⟨2329526779129617673002805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106035705506156897337073 2329526779129617673002805)
                ·
                  refine ⟨218393135543401656844013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2329526779129617673002805 218393135543401656844013)
                  ·
                    refine ⟨81897425828775621316505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218393135543401656844013 81897425828775621316505)
                    ·
                      refine ⟨61423069371581715987379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81897425828775621316505 61423069371581715987379)
                      ·
                        rfl

theorem cell23_119621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_119621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119621 prefixEnd_119621 := by exact prefixLift 119621
  have htrace : WordTrace (prefixWord ++ tailWord_119621) baseStart_119621 baseEnd_119621 := by
    simpa [prefixWord, tailWord_119621, baseEnd_119621] using wordTrace_append hprefix tailTrace_119621
  have hstable : (prefixWord ++ tailWord_119621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119621).length < 2 ^ (prefixWord ++ tailWord_119621).sum := by decide
  have hdescent : baseEnd_119621 < baseStart_119621 := by decide
  rcases family_descends (prefixWord ++ tailWord_119621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119628 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_119628 : Nat := 118140960795 + 119628 * 2 ^ 59
def prefixEnd_119628 : Nat := 4983230072969 + 3 ^ 40 * 119628 * 2
def baseEnd_119628 : Nat := 61426663736163188599847

theorem tailTrace_119628 : CollatzResearch.WordTrace tailWord_119628 prefixEnd_119628 61426663736163188599847 := by
  unfold tailWord_119628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181595805307830840463769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2908794407077107787285025 2181595805307830840463769)
  ·
    refine ⟨1636196853980873130347827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181595805307830840463769 1636196853980873130347827)
    ·
      refine ⟨2454295280971309695521741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636196853980873130347827 2454295280971309695521741)
      ·
        refine ⟨920360730364241135820653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454295280971309695521741 920360730364241135820653)
        ·
          refine ⟨345135273886590425932745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920360730364241135820653 345135273886590425932745)
          ·
            refine ⟨258851455414942819449559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345135273886590425932745 258851455414942819449559)
            ·
              refine ⟨388277183122414229174339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258851455414942819449559 388277183122414229174339)
              ·
                refine ⟨582415774683621343761509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388277183122414229174339 582415774683621343761509)
                ·
                  refine ⟨109202957753179001955283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582415774683621343761509 109202957753179001955283)
                  ·
                    refine ⟨163804436629768502932925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109202957753179001955283 163804436629768502932925)
                    ·
                      refine ⟨61426663736163188599847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163804436629768502932925 61426663736163188599847)
                      ·
                        rfl

theorem cell23_119628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_119628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119628 prefixEnd_119628 := by exact prefixLift 119628
  have htrace : WordTrace (prefixWord ++ tailWord_119628) baseStart_119628 baseEnd_119628 := by
    simpa [prefixWord, tailWord_119628, baseEnd_119628] using wordTrace_append hprefix tailTrace_119628
  have hstable : (prefixWord ++ tailWord_119628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119628).length < 2 ^ (prefixWord ++ tailWord_119628).sum := by decide
  have hdescent : baseEnd_119628 < baseStart_119628 := by decide
  rcases family_descends (prefixWord ++ tailWord_119628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119655 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_119655 : Nat := 118140960795 + 119655 * 2 ^ 59
def prefixEnd_119655 : Nat := 4983230072969 + 3 ^ 40 * 119655 * 2
def baseEnd_119655 : Nat := 61440527713834582962223

theorem tailTrace_119655 : CollatzResearch.WordTrace tailWord_119655 prefixEnd_119655 61440527713834582962223 := by
  unfold tailWord_119655
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364176381517845292160419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2909450921011896861440279 4364176381517845292160419)
  ·
    refine ⟨6546264572276767938240629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364176381517845292160419 6546264572276767938240629)
    ·
      refine ⟨613712303650946994210059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6546264572276767938240629 613712303650946994210059)
      ·
        refine ⟨920568455476420491315089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613712303650946994210059 920568455476420491315089)
        ·
          refine ⟨690426341607315368486317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920568455476420491315089 690426341607315368486317)
          ·
            refine ⟨258909878102743263182369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 690426341607315368486317 258909878102743263182369)
            ·
              refine ⟨194182408577057447386777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258909878102743263182369 194182408577057447386777)
              ·
                refine ⟨145636806432793085540083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194182408577057447386777 145636806432793085540083)
                ·
                  refine ⟨218455209649189628310125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145636806432793085540083 218455209649189628310125)
                  ·
                    refine ⟨81920703618446110616297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218455209649189628310125 81920703618446110616297)
                    ·
                      refine ⟨61440527713834582962223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81920703618446110616297 61440527713834582962223)
                      ·
                        rfl

theorem cell23_119655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_119655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119655 prefixEnd_119655 := by exact prefixLift 119655
  have htrace : WordTrace (prefixWord ++ tailWord_119655) baseStart_119655 baseEnd_119655 := by
    simpa [prefixWord, tailWord_119655, baseEnd_119655] using wordTrace_append hprefix tailTrace_119655
  have hstable : (prefixWord ++ tailWord_119655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119655).length < 2 ^ (prefixWord ++ tailWord_119655).sum := by decide
  have hdescent : baseEnd_119655 < baseStart_119655 := by decide
  rcases family_descends (prefixWord ++ tailWord_119655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119664 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_119664 : Nat := 118140960795 + 119664 * 2 ^ 59
def prefixEnd_119664 : Nat := 4983230072969 + 3 ^ 40 * 119664 * 2
def baseEnd_119664 : Nat := 61445149039725047749681

theorem tailTrace_119664 : CollatzResearch.WordTrace tailWord_119664 prefixEnd_119664 61445149039725047749681 := by
  unfold tailWord_119664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182252319242619914619023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2909669758990159886158697 2182252319242619914619023)
  ·
    refine ⟨3273378478863929871928535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182252319242619914619023 3273378478863929871928535)
    ·
      refine ⟨4910067718295894807892803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273378478863929871928535 4910067718295894807892803)
      ·
        refine ⟨7365101577443842211839205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910067718295894807892803 7365101577443842211839205)
        ·
          refine ⟨1380956545770720414719851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7365101577443842211839205 1380956545770720414719851)
          ·
            refine ⟨2071434818656080622079777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380956545770720414719851 2071434818656080622079777)
            ·
              refine ⟨1553576113992060466559833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071434818656080622079777 1553576113992060466559833)
              ·
                refine ⟨1165182085494045349919875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553576113992060466559833 1165182085494045349919875)
                ·
                  refine ⟨1747773128241068024879813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165182085494045349919875 1747773128241068024879813)
                  ·
                    refine ⟨327707461545200254664965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747773128241068024879813 327707461545200254664965)
                    ·
                      refine ⟨61445149039725047749681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 327707461545200254664965 61445149039725047749681)
                      ·
                        rfl

theorem cell23_119664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_119664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119664 prefixEnd_119664 := by exact prefixLift 119664
  have htrace : WordTrace (prefixWord ++ tailWord_119664) baseStart_119664 baseEnd_119664 := by
    simpa [prefixWord, tailWord_119664, baseEnd_119664] using wordTrace_append hprefix tailTrace_119664
  have hstable : (prefixWord ++ tailWord_119664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119664).length < 2 ^ (prefixWord ++ tailWord_119664).sum := by decide
  have hdescent : baseEnd_119664 < baseStart_119664 := by decide
  rcases family_descends (prefixWord ++ tailWord_119664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119684 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_119684 : Nat := 118140960795 + 119684 * 2 ^ 59
def prefixEnd_119684 : Nat := 4983230072969 + 3 ^ 40 * 119684 * 2
def baseEnd_119684 : Nat := 61455418652814969499589

theorem tailTrace_119684 : CollatzResearch.WordTrace tailWord_119684 prefixEnd_119684 61455418652814969499589 := by
  unfold tailWord_119684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182617049206391622483053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2910156065608522163310737 2182617049206391622483053)
  ·
    refine ⟨818481393452396858431145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2182617049206391622483053 818481393452396858431145)
    ·
      refine ⟨613861045089297643823359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818481393452396858431145 613861045089297643823359)
      ·
        refine ⟨920791567633946465735039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613861045089297643823359 920791567633946465735039)
        ·
          refine ⟨1381187351450919698602559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920791567633946465735039 1381187351450919698602559)
          ·
            refine ⟨2071781027176379547903839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381187351450919698602559 2071781027176379547903839)
            ·
              refine ⟨3107671540764569321855759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071781027176379547903839 3107671540764569321855759)
              ·
                refine ⟨4661507311146853982783639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107671540764569321855759 4661507311146853982783639)
                ·
                  refine ⟨6992260966720280974175459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661507311146853982783639 6992260966720280974175459)
                  ·
                    refine ⟨10488391450080421461263189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6992260966720280974175459 10488391450080421461263189)
                    ·
                      refine ⟨61455418652814969499589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 10488391450080421461263189 61455418652814969499589)
                      ·
                        rfl

theorem cell23_119684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_119684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119684 prefixEnd_119684 := by exact prefixLift 119684
  have htrace : WordTrace (prefixWord ++ tailWord_119684) baseStart_119684 baseEnd_119684 := by
    simpa [prefixWord, tailWord_119684, baseEnd_119684] using wordTrace_append hprefix tailTrace_119684
  have hstable : (prefixWord ++ tailWord_119684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119684).length < 2 ^ (prefixWord ++ tailWord_119684).sum := by decide
  have hdescent : baseEnd_119684 < baseStart_119684 := by decide
  rcases family_descends (prefixWord ++ tailWord_119684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119691 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 5]
def baseStart_119691 : Nat := 118140960795 + 119691 * 2 ^ 59
def prefixEnd_119691 : Nat := 4983230072969 + 3 ^ 40 * 119691 * 2
def baseEnd_119691 : Nat := 6828779224155160234673

theorem tailTrace_119691 : CollatzResearch.WordTrace tailWord_119691 prefixEnd_119691 6828779224155160234673 := by
  unfold tailWord_119691
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365489409387423440470927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2910326272924948960313951 4365489409387423440470927)
  ·
    refine ⟨6548234114081135160706391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365489409387423440470927 6548234114081135160706391)
    ·
      refine ⟨9822351171121702741059587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548234114081135160706391 9822351171121702741059587)
      ·
        refine ⟨14733526756682554111589381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822351171121702741059587 14733526756682554111589381)
        ·
          refine ⟨2762536266877978895923009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14733526756682554111589381 2762536266877978895923009)
          ·
            refine ⟨2071902200158484171942257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762536266877978895923009 2071902200158484171942257)
            ·
              refine ⟨1553926650118863128956693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071902200158484171942257 1553926650118863128956693)
              ·
                refine ⟨72840311724321709169845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1553926650118863128956693 72840311724321709169845)
                ·
                  refine ⟨6828779224155160234673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72840311724321709169845 6828779224155160234673)
                  ·
                    rfl

theorem cell23_119691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 5].length) (baseStart_119691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119691 prefixEnd_119691 := by exact prefixLift 119691
  have htrace : WordTrace (prefixWord ++ tailWord_119691) baseStart_119691 baseEnd_119691 := by
    simpa [prefixWord, tailWord_119691, baseEnd_119691] using wordTrace_append hprefix tailTrace_119691
  have hstable : (prefixWord ++ tailWord_119691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119691).length < 2 ^ (prefixWord ++ tailWord_119691).sum := by decide
  have hdescent : baseEnd_119691 < baseStart_119691 := by decide
  rcases family_descends (prefixWord ++ tailWord_119691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119721 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_119721 : Nat := 118140960795 + 119721 * 2 ^ 59
def prefixEnd_119721 : Nat := 4983230072969 + 3 ^ 40 * 119721 * 2
def baseEnd_119721 : Nat := 20491472479010441578973

theorem tailTrace_119721 : CollatzResearch.WordTrace tailWord_119721 prefixEnd_119721 20491472479010441578973 := by
  unfold tailWord_119721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366583599278738564063017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2911055732852492376042011 4366583599278738564063017)
  ·
    refine ⟨3274937699459053923047263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4366583599278738564063017 3274937699459053923047263)
    ·
      refine ⟨4912406549188580884570895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274937699459053923047263 4912406549188580884570895)
      ·
        refine ⟨7368609823782871326856343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912406549188580884570895 7368609823782871326856343)
        ·
          refine ⟨11052914735674306990284515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368609823782871326856343 11052914735674306990284515)
          ·
            refine ⟨16579372103511460485426773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052914735674306990284515 16579372103511460485426773)
            ·
              refine ⟨194289516838024927563595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 16579372103511460485426773 194289516838024927563595)
              ·
                refine ⟨291434275257037391345393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194289516838024927563595 291434275257037391345393)
                ·
                  refine ⟨218575706442778043509045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291434275257037391345393 218575706442778043509045)
                  ·
                    refine ⟨20491472479010441578973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 218575706442778043509045 20491472479010441578973)
                    ·
                      rfl

theorem cell23_119721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_119721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119721 prefixEnd_119721 := by exact prefixLift 119721
  have htrace : WordTrace (prefixWord ++ tailWord_119721) baseStart_119721 baseEnd_119721 := by
    simpa [prefixWord, tailWord_119721, baseEnd_119721] using wordTrace_append hprefix tailTrace_119721
  have hstable : (prefixWord ++ tailWord_119721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119721).length < 2 ^ (prefixWord ++ tailWord_119721).sum := by decide
  have hdescent : baseEnd_119721 < baseStart_119721 := by decide
  rcases family_descends (prefixWord ++ tailWord_119721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119758 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_119758 : Nat := 118140960795 + 119758 * 2 ^ 59
def prefixEnd_119758 : Nat := 4983230072969 + 3 ^ 40 * 119758 * 2
def baseEnd_119758 : Nat := 61493416221247679974249

theorem tailTrace_119758 : CollatzResearch.WordTrace tailWord_119758 prefixEnd_119758 61493416221247679974249 := by
  unfold tailWord_119758
  simp only [CollatzResearch.WordTrace]
  refine ⟨545991637518086735394991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2911955400096462588773285 545991637518086735394991)
  ·
    refine ⟨818987456277130103092487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545991637518086735394991 818987456277130103092487)
    ·
      refine ⟨1228481184415695154638731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818987456277130103092487 1228481184415695154638731)
      ·
        refine ⟨1842721776623542731958097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228481184415695154638731 1842721776623542731958097)
        ·
          refine ⟨1382041332467657048968573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842721776623542731958097 1382041332467657048968573)
          ·
            refine ⟨518265499675371393363215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1382041332467657048968573 518265499675371393363215)
            ·
              refine ⟨777398249513057090044823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518265499675371393363215 777398249513057090044823)
              ·
                refine ⟨1166097374269585635067235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777398249513057090044823 1166097374269585635067235)
                ·
                  refine ⟨1749146061404378452600853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166097374269585635067235 1749146061404378452600853)
                  ·
                    refine ⟨81991221628330239965665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1749146061404378452600853 81991221628330239965665)
                    ·
                      refine ⟨61493416221247679974249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 81991221628330239965665 61493416221247679974249)
                      ·
                        rfl

theorem cell23_119758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_119758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119758 prefixEnd_119758 := by exact prefixLift 119758
  have htrace : WordTrace (prefixWord ++ tailWord_119758) baseStart_119758 baseEnd_119758 := by
    simpa [prefixWord, tailWord_119758, baseEnd_119758] using wordTrace_append hprefix tailTrace_119758
  have hstable : (prefixWord ++ tailWord_119758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119758).length < 2 ^ (prefixWord ++ tailWord_119758).sum := by decide
  have hdescent : baseEnd_119758 < baseStart_119758 := by decide
  rcases family_descends (prefixWord ++ tailWord_119758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119761 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_119761 : Nat := 118140960795 + 119761 * 2 ^ 59
def prefixEnd_119761 : Nat := 4983230072969 + 3 ^ 40 * 119761 * 2
def baseEnd_119761 : Nat := 61494956663211168236735

theorem tailTrace_119761 : CollatzResearch.WordTrace tailWord_119761 prefixEnd_119761 61494956663211168236735 := by
  unfold tailWord_119761
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368042519133825395519137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2912028346089216930346091 4368042519133825395519137)
  ·
    refine ⟨3276031889350369046639353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4368042519133825395519137 3276031889350369046639353)
    ·
      refine ⟨2457023917012776784979515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276031889350369046639353 2457023917012776784979515)
      ·
        refine ⟨3685535875519165177469273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457023917012776784979515 3685535875519165177469273)
        ·
          refine ⟨2764151906639373883101955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3685535875519165177469273 2764151906639373883101955)
          ·
            refine ⟨4146227859959060824652933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764151906639373883101955 4146227859959060824652933)
            ·
              refine ⟨777417723742323904622425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4146227859959060824652933 777417723742323904622425)
              ·
                refine ⟨583063292806742928466819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777417723742323904622425 583063292806742928466819)
                ·
                  refine ⟨874594939210114392700229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583063292806742928466819 874594939210114392700229)
                  ·
                    refine ⟨163986551101896448631293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874594939210114392700229 163986551101896448631293)
                    ·
                      refine ⟨61494956663211168236735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 163986551101896448631293 61494956663211168236735)
                      ·
                        rfl

theorem cell23_119761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_119761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119761 prefixEnd_119761 := by exact prefixLift 119761
  have htrace : WordTrace (prefixWord ++ tailWord_119761) baseStart_119761 baseEnd_119761 := by
    simpa [prefixWord, tailWord_119761, baseEnd_119761] using wordTrace_append hprefix tailTrace_119761
  have hstable : (prefixWord ++ tailWord_119761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119761).length < 2 ^ (prefixWord ++ tailWord_119761).sum := by decide
  have hdescent : baseEnd_119761 < baseStart_119761 := by decide
  rcases family_descends (prefixWord ++ tailWord_119761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119768 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_119768 : Nat := 118140960795 + 119768 * 2 ^ 59
def prefixEnd_119768 : Nat := 4983230072969 + 3 ^ 40 * 119768 * 2
def baseEnd_119768 : Nat := 20499517009264213616401

theorem tailTrace_119768 : CollatzResearch.WordTrace tailWord_119768 prefixEnd_119768 20499517009264213616401 := by
  unfold tailWord_119768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184148915054232795511979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2912198553405643727349305 2184148915054232795511979)
  ·
    refine ⟨3276223372581349193267969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2184148915054232795511979 3276223372581349193267969)
    ·
      refine ⟨2457167529436011894950977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276223372581349193267969 2457167529436011894950977)
      ·
        refine ⟨1842875647077008921213233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2457167529436011894950977 1842875647077008921213233)
        ·
          refine ⟨1382156735307756690909925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842875647077008921213233 1382156735307756690909925)
          ·
            refine ⟨259154387870204379545611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1382156735307756690909925 259154387870204379545611)
            ·
              refine ⟨388731581805306569318417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259154387870204379545611 388731581805306569318417)
              ·
                refine ⟨291548686353979926988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388731581805306569318417 291548686353979926988813)
                ·
                  refine ⟨109330757382742472620805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291548686353979926988813 109330757382742472620805)
                  ·
                    refine ⟨20499517009264213616401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109330757382742472620805 20499517009264213616401)
                    ·
                      rfl

theorem cell23_119768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_119768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119768 prefixEnd_119768 := by exact prefixLift 119768
  have htrace : WordTrace (prefixWord ++ tailWord_119768) baseStart_119768 baseEnd_119768 := by
    simpa [prefixWord, tailWord_119768, baseEnd_119768] using wordTrace_append hprefix tailTrace_119768
  have hstable : (prefixWord ++ tailWord_119768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119768).length < 2 ^ (prefixWord ++ tailWord_119768).sum := by decide
  have hdescent : baseEnd_119768 < baseStart_119768 := by decide
  rcases family_descends (prefixWord ++ tailWord_119768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119775 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_119775 : Nat := 118140960795 + 119775 * 2 ^ 59
def prefixEnd_119775 : Nat := 4983230072969 + 3 ^ 40 * 119775 * 2
def baseEnd_119775 : Nat := 61502145392374113461671

theorem tailTrace_119775 : CollatzResearch.WordTrace tailWord_119775 prefixEnd_119775 61502145392374113461671 := by
  unfold tailWord_119775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368553141083105786528779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2912368760722070524352519 4368553141083105786528779)
  ·
    refine ⟨6552829711624658679793169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368553141083105786528779 6552829711624658679793169)
    ·
      refine ⟨4914622283718494009844877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6552829711624658679793169 4914622283718494009844877)
      ·
        refine ⟨1842983356394435253691829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4914622283718494009844877 1842983356394435253691829)
        ·
          refine ⟨172779689661978305033609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1842983356394435253691829 172779689661978305033609)
          ·
            refine ⟨129584767246483728775207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172779689661978305033609 129584767246483728775207)
            ·
              refine ⟨194377150869725593162811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129584767246483728775207 194377150869725593162811)
              ·
                refine ⟨291565726304588389744217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194377150869725593162811 291565726304588389744217)
                ·
                  refine ⟨218674294728441292308163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291565726304588389744217 218674294728441292308163)
                  ·
                    refine ⟨328011442092661938462245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218674294728441292308163 328011442092661938462245)
                    ·
                      refine ⟨61502145392374113461671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 328011442092661938462245 61502145392374113461671)
                      ·
                        rfl

theorem cell23_119775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_119775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119775 prefixEnd_119775 := by exact prefixLift 119775
  have htrace : WordTrace (prefixWord ++ tailWord_119775) baseStart_119775 baseEnd_119775 := by
    simpa [prefixWord, tailWord_119775, baseEnd_119775] using wordTrace_append hprefix tailTrace_119775
  have hstable : (prefixWord ++ tailWord_119775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119775).length < 2 ^ (prefixWord ++ tailWord_119775).sum := by decide
  have hdescent : baseEnd_119775 < baseStart_119775 := by decide
  rcases family_descends (prefixWord ++ tailWord_119775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119798 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_119798 : Nat := 118140960795 + 119798 * 2 ^ 59
def prefixEnd_119798 : Nat := 4983230072969 + 3 ^ 40 * 119798 * 2
def baseEnd_119798 : Nat := 6834883938603058163785

theorem tailTrace_119798 : CollatzResearch.WordTrace tailWord_119798 prefixEnd_119798 6834883938603058163785 := by
  unfold tailWord_119798
  simp only [CollatzResearch.WordTrace]
  refine ⟨273087001249986294663503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2912928013333187143077365 273087001249986294663503)
  ·
    refine ⟨409630501874979441995255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273087001249986294663503 409630501874979441995255)
    ·
      refine ⟨614445752812469162992883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409630501874979441995255 614445752812469162992883)
      ·
        refine ⟨921668629218703744489325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614445752812469162992883 921668629218703744489325)
        ·
          refine ⟨345625735957013904183497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921668629218703744489325 345625735957013904183497)
          ·
            refine ⟨259219301967760428137623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345625735957013904183497 259219301967760428137623)
            ·
              refine ⟨388828952951640642206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259219301967760428137623 388828952951640642206435)
              ·
                refine ⟨583243429427460963309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388828952951640642206435 583243429427460963309653)
                ·
                  refine ⟨6834883938603058163785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 583243429427460963309653 6834883938603058163785)
                  ·
                    rfl

theorem cell23_119798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_119798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119798 prefixEnd_119798 := by exact prefixLift 119798
  have htrace : WordTrace (prefixWord ++ tailWord_119798) baseStart_119798 baseEnd_119798 := by
    simpa [prefixWord, tailWord_119798, baseEnd_119798] using wordTrace_append hprefix tailTrace_119798
  have hstable : (prefixWord ++ tailWord_119798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119798).length < 2 ^ (prefixWord ++ tailWord_119798).sum := by decide
  have hdescent : baseEnd_119798 < baseStart_119798 := by decide
  rcases family_descends (prefixWord ++ tailWord_119798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119858 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_119858 : Nat := 118140960795 + 119858 * 2 ^ 59
def prefixEnd_119858 : Nat := 4983230072969 + 3 ^ 40 * 119858 * 2
def baseEnd_119858 : Nat := 20514921428899096241263

theorem tailTrace_119858 : CollatzResearch.WordTrace tailWord_119858 prefixEnd_119858 20514921428899096241263 := by
  unfold tailWord_119858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092895099945602740450057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2914386933188273974533485 1092895099945602740450057)
  ·
    refine ⟨819671324959202055337543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092895099945602740450057 819671324959202055337543)
    ·
      refine ⟨1229506987438803083006315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819671324959202055337543 1229506987438803083006315)
      ·
        refine ⟨1844260481158204624509473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229506987438803083006315 1844260481158204624509473)
        ·
          refine ⟨1383195360868653468382105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844260481158204624509473 1383195360868653468382105)
          ·
            refine ⟨1037396520651490101286579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383195360868653468382105 1037396520651490101286579)
            ·
              refine ⟨1556094780977235151929869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037396520651490101286579 1556094780977235151929869)
              ·
                refine ⟨583535542866463181973701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556094780977235151929869 583535542866463181973701)
                ·
                  refine ⟨109412914287461846620069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583535542866463181973701 109412914287461846620069)
                  ·
                    refine ⟨20514921428899096241263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109412914287461846620069 20514921428899096241263)
                    ·
                      rfl

theorem cell23_119858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_119858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119858 prefixEnd_119858 := by exact prefixLift 119858
  have htrace : WordTrace (prefixWord ++ tailWord_119858) baseStart_119858 baseEnd_119858 := by
    simpa [prefixWord, tailWord_119858, baseEnd_119858] using wordTrace_append hprefix tailTrace_119858
  have hstable : (prefixWord ++ tailWord_119858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119858).length < 2 ^ (prefixWord ++ tailWord_119858).sum := by decide
  have hdescent : baseEnd_119858 < baseStart_119858 := by decide
  rcases family_descends (prefixWord ++ tailWord_119858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119868 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_119868 : Nat := 118140960795 + 119868 * 2 ^ 59
def prefixEnd_119868 : Nat := 4983230072969 + 3 ^ 40 * 119868 * 2
def baseEnd_119868 : Nat := 61549899093242249598743

theorem tailTrace_119868 : CollatzResearch.WordTrace tailWord_119868 prefixEnd_119868 61549899093242249598743 := by
  unfold tailWord_119868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185972564873091334832129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2914630086497455113109505 2185972564873091334832129)
  ·
    refine ⟨1639479423654818501124097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2185972564873091334832129 1639479423654818501124097)
    ·
      refine ⟨1229609567741113875843073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1639479423654818501124097 1229609567741113875843073)
      ·
        refine ⟨922207175805835406882305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229609567741113875843073 922207175805835406882305)
        ·
          refine ⟨691655381854376555161729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922207175805835406882305 691655381854376555161729)
          ·
            refine ⟨518741536390782416371297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691655381854376555161729 518741536390782416371297)
            ·
              refine ⟨389056152293086812278473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518741536390782416371297 389056152293086812278473)
              ·
                refine ⟨291792114219815109208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389056152293086812278473 291792114219815109208855)
                ·
                  refine ⟨437688171329722663813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291792114219815109208855 437688171329722663813283)
                  ·
                    refine ⟨656532256994583995719925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 437688171329722663813283 656532256994583995719925)
                    ·
                      refine ⟨61549899093242249598743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 656532256994583995719925 61549899093242249598743)
                      ·
                        rfl

theorem cell23_119868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_119868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119868 prefixEnd_119868 := by exact prefixLift 119868
  have htrace : WordTrace (prefixWord ++ tailWord_119868) baseStart_119868 baseEnd_119868 := by
    simpa [prefixWord, tailWord_119868, baseEnd_119868] using wordTrace_append hprefix tailTrace_119868
  have hstable : (prefixWord ++ tailWord_119868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119868).length < 2 ^ (prefixWord ++ tailWord_119868).sum := by decide
  have hdescent : baseEnd_119868 < baseStart_119868 := by decide
  rcases family_descends (prefixWord ++ tailWord_119868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119918 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_119918 : Nat := 118140960795 + 119918 * 2 ^ 59
def prefixEnd_119918 : Nat := 4983230072969 + 3 ^ 40 * 119918 * 2
def baseEnd_119918 : Nat := 20525191041989017991171

theorem tailTrace_119918 : CollatzResearch.WordTrace tailWord_119918 prefixEnd_119918 20525191041989017991171 := by
  unfold tailWord_119918
  simp only [CollatzResearch.WordTrace]
  refine ⟨546721097445630151123051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2915845853043360805989605 546721097445630151123051)
  ·
    refine ⟨820081646168445226684577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546721097445630151123051 820081646168445226684577)
    ·
      refine ⟨615061234626333920013433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 820081646168445226684577 615061234626333920013433)
      ·
        refine ⟨461295925969750440010075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615061234626333920013433 461295925969750440010075)
        ·
          refine ⟨691943888954625660015113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461295925969750440010075 691943888954625660015113)
          ·
            refine ⟨518957916715969245011335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691943888954625660015113 518957916715969245011335)
            ·
              refine ⟨778436875073953867517003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518957916715969245011335 778436875073953867517003)
              ·
                refine ⟨1167655312610930801275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778436875073953867517003 1167655312610930801275505)
                ·
                  refine ⟨875741484458198100956629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167655312610930801275505 875741484458198100956629)
                  ·
                    refine ⟨20525191041989017991171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 875741484458198100956629 20525191041989017991171)
                    ·
                      rfl

theorem cell23_119918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_119918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119918 prefixEnd_119918 := by exact prefixLift 119918
  have htrace : WordTrace (prefixWord ++ tailWord_119918) baseStart_119918 baseEnd_119918 := by
    simpa [prefixWord, tailWord_119918, baseEnd_119918] using wordTrace_append hprefix tailTrace_119918
  have hstable : (prefixWord ++ tailWord_119918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119918).length < 2 ^ (prefixWord ++ tailWord_119918).sum := by decide
  have hdescent : baseEnd_119918 < baseStart_119918 := by decide
  rcases family_descends (prefixWord ++ tailWord_119918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119951 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_119951 : Nat := 118140960795 + 119951 * 2 ^ 59
def prefixEnd_119951 : Nat := 4983230072969 + 3 ^ 40 * 119951 * 2
def baseEnd_119951 : Nat := 61592517987565424860861

theorem tailTrace_119951 : CollatzResearch.WordTrace tailWord_119951 prefixEnd_119951 61592517987565424860861 := by
  unfold tailWord_119951
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374972388445487844935707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2916648258963658563290471 4374972388445487844935707)
  ·
    refine ⟨6562458582668231767403561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4374972388445487844935707 6562458582668231767403561)
    ·
      refine ⟨4921843937001173825552671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6562458582668231767403561 4921843937001173825552671)
      ·
        refine ⟨7382765905501760738329007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921843937001173825552671 7382765905501760738329007)
        ·
          refine ⟨11074148858252641107493511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382765905501760738329007 11074148858252641107493511)
          ·
            refine ⟨16611223287378961661240267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074148858252641107493511 16611223287378961661240267)
            ·
              refine ⟨24916834931068442491860401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611223287378961661240267 24916834931068442491860401)
              ·
                refine ⟨18687626198301331868895301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24916834931068442491860401 18687626198301331868895301)
                ·
                  refine ⟨3503929912181499725417869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18687626198301331868895301 3503929912181499725417869)
                  ·
                    refine ⟨1313973717068062397031701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503929912181499725417869 1313973717068062397031701)
                    ·
                      refine ⟨61592517987565424860861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1313973717068062397031701 61592517987565424860861)
                      ·
                        rfl

theorem cell23_119951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_119951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119951 prefixEnd_119951 := by exact prefixLift 119951
  have htrace : WordTrace (prefixWord ++ tailWord_119951) baseStart_119951 baseEnd_119951 := by
    simpa [prefixWord, tailWord_119951, baseEnd_119951] using wordTrace_append hprefix tailTrace_119951
  have hstable : (prefixWord ++ tailWord_119951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119951).length < 2 ^ (prefixWord ++ tailWord_119951).sum := by decide
  have hdescent : baseEnd_119951 < baseStart_119951 := by decide
  rcases family_descends (prefixWord ++ tailWord_119951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119955 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 4, 2]
def baseStart_119955 : Nat := 118140960795 + 119955 * 2 ^ 59
def prefixEnd_119955 : Nat := 4983230072969 + 3 ^ 40 * 119955 * 2
def baseEnd_119955 : Nat := 61594571910183409210843

theorem tailTrace_119955 : CollatzResearch.WordTrace tailWord_119955 prefixEnd_119955 61594571910183409210843 := by
  unfold tailWord_119955
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375118280430996528081319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2916745520287331018720879 4375118280430996528081319)
  ·
    refine ⟨6562677420646494792121979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4375118280430996528081319 6562677420646494792121979)
    ·
      refine ⟨9844016130969742188182969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562677420646494792121979 9844016130969742188182969)
      ·
        refine ⟨7383012098227306641137227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844016130969742188182969 7383012098227306641137227)
        ·
          refine ⟨11074518147340959961705841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383012098227306641137227 11074518147340959961705841)
          ·
            refine ⟨8305888610505719971279381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11074518147340959961705841 8305888610505719971279381)
            ·
              refine ⟨389338528617455623653721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8305888610505719971279381 389338528617455623653721)
              ·
                refine ⟨292003896463091717740291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389338528617455623653721 292003896463091717740291)
                ·
                  refine ⟨438005844694637576610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292003896463091717740291 438005844694637576610437)
                  ·
                    refine ⟨82126095880244545614457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438005844694637576610437 82126095880244545614457)
                    ·
                      refine ⟨61594571910183409210843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82126095880244545614457 61594571910183409210843)
                      ·
                        rfl

theorem cell23_119955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4, 2].length) (baseStart_119955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119955 prefixEnd_119955 := by exact prefixLift 119955
  have htrace : WordTrace (prefixWord ++ tailWord_119955) baseStart_119955 baseEnd_119955 := by
    simpa [prefixWord, tailWord_119955, baseEnd_119955] using wordTrace_append hprefix tailTrace_119955
  have hstable : (prefixWord ++ tailWord_119955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119955).length < 2 ^ (prefixWord ++ tailWord_119955).sum := by decide
  have hdescent : baseEnd_119955 < baseStart_119955 := by decide
  rcases family_descends (prefixWord ++ tailWord_119955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119959 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_119959 : Nat := 118140960795 + 119959 * 2 ^ 59
def prefixEnd_119959 : Nat := 4983230072969 + 3 ^ 40 * 119959 * 2
def baseEnd_119959 : Nat := 61596625832801393560825

theorem tailTrace_119959 : CollatzResearch.WordTrace tailWord_119959 prefixEnd_119959 61596625832801393560825 := by
  unfold tailWord_119959
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375264172416505211226931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2916842781611003474151287 4375264172416505211226931)
  ·
    refine ⟨6562896258624757816840397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4375264172416505211226931 6562896258624757816840397)
    ·
      refine ⟨2461086096984284181315149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6562896258624757816840397 2461086096984284181315149)
      ·
        refine ⟨922907286369106567993181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2461086096984284181315149 922907286369106567993181)
        ·
          refine ⟨346090232388414962997443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922907286369106567993181 346090232388414962997443)
          ·
            refine ⟨519135348582622444496165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346090232388414962997443 519135348582622444496165)
            ·
              refine ⟨97337877859241708343031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519135348582622444496165 97337877859241708343031)
              ·
                refine ⟨146006816788862562514547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97337877859241708343031 146006816788862562514547)
                ·
                  refine ⟨219010225183293843771821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146006816788862562514547 219010225183293843771821)
                  ·
                    refine ⟨82128834443735191414433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219010225183293843771821 82128834443735191414433)
                    ·
                      refine ⟨61596625832801393560825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82128834443735191414433 61596625832801393560825)
                      ·
                        rfl

theorem cell23_119959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_119959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119959 prefixEnd_119959 := by exact prefixLift 119959
  have htrace : WordTrace (prefixWord ++ tailWord_119959) baseStart_119959 baseEnd_119959 := by
    simpa [prefixWord, tailWord_119959, baseEnd_119959] using wordTrace_append hprefix tailTrace_119959
  have hstable : (prefixWord ++ tailWord_119959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119959).length < 2 ^ (prefixWord ++ tailWord_119959).sum := by decide
  have hdescent : baseEnd_119959 < baseStart_119959 := by decide
  rcases family_descends (prefixWord ++ tailWord_119959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119966 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_119966 : Nat := 118140960795 + 119966 * 2 ^ 59
def prefixEnd_119966 : Nat := 4983230072969 + 3 ^ 40 * 119966 * 2
def baseEnd_119966 : Nat := 61600220197382866173293

theorem tailTrace_119966 : CollatzResearch.WordTrace tailWord_119966 prefixEnd_119966 61600220197382866173293 := by
  unfold tailWord_119966
  simp only [CollatzResearch.WordTrace]
  refine ⟨546939935423893175841469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2917012988927430271154501 546939935423893175841469)
  ·
    refine ⟨205102475783959940940551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 546939935423893175841469 205102475783959940940551)
    ·
      refine ⟨307653713675939911410827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205102475783959940940551 307653713675939911410827)
      ·
        refine ⟨461480570513909867116241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307653713675939911410827 461480570513909867116241)
        ·
          refine ⟨346110427885432400337181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461480570513909867116241 346110427885432400337181)
          ·
            refine ⟨129791410457037150126443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346110427885432400337181 129791410457037150126443)
            ·
              refine ⟨194687115685555725189665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129791410457037150126443 194687115685555725189665)
              ·
                refine ⟨146015336764166793892249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194687115685555725189665 146015336764166793892249)
                ·
                  refine ⟨109511502573125095419187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146015336764166793892249 109511502573125095419187)
                  ·
                    refine ⟨164267253859687643128781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109511502573125095419187 164267253859687643128781)
                    ·
                      refine ⟨61600220197382866173293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 164267253859687643128781 61600220197382866173293)
                      ·
                        rfl

theorem cell23_119966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_119966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119966 prefixEnd_119966 := by exact prefixLift 119966
  have htrace : WordTrace (prefixWord ++ tailWord_119966) baseStart_119966 baseEnd_119966 := by
    simpa [prefixWord, tailWord_119966, baseEnd_119966] using wordTrace_append hprefix tailTrace_119966
  have hstable : (prefixWord ++ tailWord_119966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119966).length < 2 ^ (prefixWord ++ tailWord_119966).sum := by decide
  have hdescent : baseEnd_119966 < baseStart_119966 := by decide
  rcases family_descends (prefixWord ++ tailWord_119966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119968 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_119968 : Nat := 118140960795 + 119968 * 2 ^ 59
def prefixEnd_119968 : Nat := 4983230072969 + 3 ^ 40 * 119968 * 2
def baseEnd_119968 : Nat := 61601247158691858348283

theorem tailTrace_119968 : CollatzResearch.WordTrace tailWord_119968 prefixEnd_119968 61601247158691858348283 := by
  unfold tailWord_119968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187796214691949874152279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2917061619589266498869705 2187796214691949874152279)
  ·
    refine ⟨3281694322037924811228419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187796214691949874152279 3281694322037924811228419)
    ·
      refine ⟨4922541483056887216842629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281694322037924811228419 4922541483056887216842629)
      ·
        refine ⟨922976528073166353157993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4922541483056887216842629 922976528073166353157993)
        ·
          refine ⟨692232396054874764868495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922976528073166353157993 692232396054874764868495)
          ·
            refine ⟨1038348594082312147302743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692232396054874764868495 1038348594082312147302743)
            ·
              refine ⟨1557522891123468220954115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038348594082312147302743 1557522891123468220954115)
              ·
                refine ⟨2336284336685202331431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557522891123468220954115 2336284336685202331431173)
                ·
                  refine ⟨438053313128475437143345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336284336685202331431173 438053313128475437143345)
                  ·
                    refine ⟨328539984846356577857509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438053313128475437143345 328539984846356577857509)
                    ·
                      refine ⟨61601247158691858348283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 328539984846356577857509 61601247158691858348283)
                      ·
                        rfl

theorem cell23_119968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_119968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119968 prefixEnd_119968 := by exact prefixLift 119968
  have htrace : WordTrace (prefixWord ++ tailWord_119968) baseStart_119968 baseEnd_119968 := by
    simpa [prefixWord, tailWord_119968, baseEnd_119968] using wordTrace_append hprefix tailTrace_119968
  have hstable : (prefixWord ++ tailWord_119968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119968).length < 2 ^ (prefixWord ++ tailWord_119968).sum := by decide
  have hdescent : baseEnd_119968 < baseStart_119968 := by decide
  rcases family_descends (prefixWord ++ tailWord_119968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119985 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_119985 : Nat := 118140960795 + 119985 * 2 ^ 59
def prefixEnd_119985 : Nat := 4983230072969 + 3 ^ 40 * 119985 * 2
def baseEnd_119985 : Nat := 61609976329818291835705

theorem tailTrace_119985 : CollatzResearch.WordTrace tailWord_119985 prefixEnd_119985 61609976329818291835705 := by
  unfold tailWord_119985
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376212470322311651673409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2917474980214874434448939 4376212470322311651673409)
  ·
    refine ⟨3282159352741733738755057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4376212470322311651673409 3282159352741733738755057)
    ·
      refine ⟨2461619514556300304066293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3282159352741733738755057 2461619514556300304066293)
      ·
        refine ⟨230776829489653153506215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2461619514556300304066293 230776829489653153506215)
        ·
          refine ⟨346165244234479730259323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230776829489653153506215 346165244234479730259323)
          ·
            refine ⟨519247866351719595388985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346165244234479730259323 519247866351719595388985)
            ·
              refine ⟨389435899763789696541739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519247866351719595388985 389435899763789696541739)
              ·
                refine ⟨584153849645684544812609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389435899763789696541739 584153849645684544812609)
                ·
                  refine ⟨438115387234263408609457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584153849645684544812609 438115387234263408609457)
                  ·
                    refine ⟨328586540425697556457093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438115387234263408609457 328586540425697556457093)
                    ·
                      refine ⟨61609976329818291835705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 328586540425697556457093 61609976329818291835705)
                      ·
                        rfl

theorem cell23_119985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_119985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_119985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_119985 prefixEnd_119985 := by exact prefixLift 119985
  have htrace : WordTrace (prefixWord ++ tailWord_119985) baseStart_119985 baseEnd_119985 := by
    simpa [prefixWord, tailWord_119985, baseEnd_119985] using wordTrace_append hprefix tailTrace_119985
  have hstable : (prefixWord ++ tailWord_119985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119985).length < 2 ^ (prefixWord ++ tailWord_119985).sum := by decide
  have hdescent : baseEnd_119985 < baseStart_119985 := by decide
  rcases family_descends (prefixWord ++ tailWord_119985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120008 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_120008 : Nat := 118140960795 + 120008 * 2 ^ 59
def prefixEnd_120008 : Nat := 4983230072969 + 3 ^ 40 * 120008 * 2
def baseEnd_120008 : Nat := 20540595461623900616033

theorem tailTrace_120008 : CollatzResearch.WordTrace tailWord_120008 prefixEnd_120008 20540595461623900616033 := by
  unfold tailWord_120008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188525674619493289880339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2918034232825991053173785 2188525674619493289880339)
  ·
    refine ⟨3282788511929239934820509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188525674619493289880339 3282788511929239934820509)
    ·
      refine ⟨1231045691973464975557691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3282788511929239934820509 1231045691973464975557691)
      ·
        refine ⟨1846568537960197463336537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231045691973464975557691 1846568537960197463336537)
        ·
          refine ⟨1384926403470148097502403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1846568537960197463336537 1384926403470148097502403)
          ·
            refine ⟨2077389605205222146253605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384926403470148097502403 2077389605205222146253605)
            ·
              refine ⟨389510550975979152422551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2077389605205222146253605 389510550975979152422551)
              ·
                refine ⟨584265826463968728633827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389510550975979152422551 584265826463968728633827)
                ·
                  refine ⟨876398739695953092950741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584265826463968728633827 876398739695953092950741)
                  ·
                    refine ⟨20540595461623900616033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 876398739695953092950741 20540595461623900616033)
                    ·
                      rfl

theorem cell23_120008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_120008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120008 prefixEnd_120008 := by exact prefixLift 120008
  have htrace : WordTrace (prefixWord ++ tailWord_120008) baseStart_120008 baseEnd_120008 := by
    simpa [prefixWord, tailWord_120008, baseEnd_120008] using wordTrace_append hprefix tailTrace_120008
  have hstable : (prefixWord ++ tailWord_120008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120008).length < 2 ^ (prefixWord ++ tailWord_120008).sum := by decide
  have hdescent : baseEnd_120008 < baseStart_120008 := by decide
  rcases family_descends (prefixWord ++ tailWord_120008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120029 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 7]
def baseStart_120029 : Nat := 118140960795 + 120029 * 2 ^ 59
def prefixEnd_120029 : Nat := 4983230072969 + 3 ^ 40 * 120029 * 2
def baseEnd_120029 : Nat := 6848063275401791076167

theorem tailTrace_120029 : CollatzResearch.WordTrace tailWord_120029 prefixEnd_120029 6848063275401791076167 := by
  unfold tailWord_120029
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377817282162907166275141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918544854775271444183427 4377817282162907166275141)
  ·
    refine ⟨820840740405545093676589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4377817282162907166275141 820840740405545093676589)
    ·
      refine ⟨307815277652079410128721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 820840740405545093676589 307815277652079410128721)
      ·
        refine ⟨230861458239059557596541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307815277652079410128721 230861458239059557596541)
        ·
          refine ⟨86573046839647334098703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230861458239059557596541 86573046839647334098703)
          ·
            refine ⟨129859570259471001148055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86573046839647334098703 129859570259471001148055)
            ·
              refine ⟨194789355389206501722083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129859570259471001148055 194789355389206501722083)
              ·
                refine ⟨292184033083809752583125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194789355389206501722083 292184033083809752583125)
                ·
                  refine ⟨6848063275401791076167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292184033083809752583125 6848063275401791076167)
                  ·
                    rfl

theorem cell23_120029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_120029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120029 prefixEnd_120029 := by exact prefixLift 120029
  have htrace : WordTrace (prefixWord ++ tailWord_120029) baseStart_120029 baseEnd_120029 := by
    simpa [prefixWord, tailWord_120029, baseEnd_120029] using wordTrace_append hprefix tailTrace_120029
  have hstable : (prefixWord ++ tailWord_120029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120029).length < 2 ^ (prefixWord ++ tailWord_120029).sum := by decide
  have hdescent : baseEnd_120029 < baseStart_120029 := by decide
  rcases family_descends (prefixWord ++ tailWord_120029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120062 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_120062 : Nat := 118140960795 + 120062 * 2 ^ 59
def prefixEnd_120062 : Nat := 4983230072969 + 3 ^ 40 * 120062 * 2
def baseEnd_120062 : Nat := 61649514340214490572851

theorem tailTrace_120062 : CollatzResearch.WordTrace tailWord_120062 prefixEnd_120062 61649514340214490572851 := by
  unfold tailWord_120062
  simp only [CollatzResearch.WordTrace]
  refine ⟨547377611380419225278305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2919347260695569201484293 547377611380419225278305)
  ·
    refine ⟨410533208535314418958729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 547377611380419225278305 410533208535314418958729)
    ·
      refine ⟨307899906401485814219047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410533208535314418958729 307899906401485814219047)
      ·
        refine ⟨461849859602228721328571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307899906401485814219047 461849859602228721328571)
        ·
          refine ⟨692774789403343081992857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461849859602228721328571 692774789403343081992857)
          ·
            refine ⟨519581092052507311494643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692774789403343081992857 519581092052507311494643)
            ·
              refine ⟨779371638078760967241965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519581092052507311494643 779371638078760967241965)
              ·
                refine ⟨292264364279535362715737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779371638078760967241965 292264364279535362715737)
                ·
                  refine ⟨219198273209651522036803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292264364279535362715737 219198273209651522036803)
                  ·
                    refine ⟨328797409814477283055205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219198273209651522036803 328797409814477283055205)
                    ·
                      refine ⟨61649514340214490572851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 328797409814477283055205 61649514340214490572851)
                      ·
                        rfl

theorem cell23_120062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_120062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120062 prefixEnd_120062 := by exact prefixLift 120062
  have htrace : WordTrace (prefixWord ++ tailWord_120062) baseStart_120062 baseEnd_120062 := by
    simpa [prefixWord, tailWord_120062, baseEnd_120062] using wordTrace_append hprefix tailTrace_120062
  have hstable : (prefixWord ++ tailWord_120062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120062).length < 2 ^ (prefixWord ++ tailWord_120062).sum := by decide
  have hdescent : baseEnd_120062 < baseStart_120062 := by decide
  rcases family_descends (prefixWord ++ tailWord_120062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 9, 2]
def baseStart_120105 : Nat := 118140960795 + 120105 * 2 ^ 59
def prefixEnd_120105 : Nat := 4983230072969 + 3 ^ 40 * 120105 * 2
def baseEnd_120105 : Nat := 61671594008357822335153

theorem tailTrace_120105 : CollatzResearch.WordTrace tailWord_120105 prefixEnd_120105 61671594008357822335153 := by
  unfold tailWord_120105
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380589229887572146041769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2920392819925048097361179 4380589229887572146041769)
  ·
    refine ⟨3285441922415679109531327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4380589229887572146041769 3285441922415679109531327)
    ·
      refine ⟨4928162883623518664296991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285441922415679109531327 4928162883623518664296991)
      ·
        refine ⟨7392244325435277996445487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928162883623518664296991 7392244325435277996445487)
        ·
          refine ⟨11088366488152916994668231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392244325435277996445487 11088366488152916994668231)
          ·
            refine ⟨16632549732229375492002347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088366488152916994668231 16632549732229375492002347)
            ·
              refine ⟨24948824598344063238003521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632549732229375492002347 24948824598344063238003521)
              ·
                refine ⟨18711618448758047428502641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24948824598344063238003521 18711618448758047428502641)
                ·
                  refine ⟨14033713836568535571376981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18711618448758047428502641 14033713836568535571376981)
                  ·
                    refine ⟨82228792011143763113537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14033713836568535571376981 82228792011143763113537)
                    ·
                      refine ⟨61671594008357822335153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82228792011143763113537 61671594008357822335153)
                      ·
                        rfl

theorem cell23_120105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9, 2].length) (baseStart_120105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120105 prefixEnd_120105 := by exact prefixLift 120105
  have htrace : WordTrace (prefixWord ++ tailWord_120105) baseStart_120105 baseEnd_120105 := by
    simpa [prefixWord, tailWord_120105, baseEnd_120105] using wordTrace_append hprefix tailTrace_120105
  have hstable : (prefixWord ++ tailWord_120105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120105).length < 2 ^ (prefixWord ++ tailWord_120105).sum := by decide
  have hdescent : baseEnd_120105 < baseStart_120105 := by decide
  rcases family_descends (prefixWord ++ tailWord_120105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120108 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_120108 : Nat := 118140960795 + 120108 * 2 ^ 59
def prefixEnd_120108 : Nat := 4983230072969 + 3 ^ 40 * 120108 * 2
def baseEnd_120108 : Nat := 61673134450321310597639

theorem tailTrace_120108 : CollatzResearch.WordTrace tailWord_120108 prefixEnd_120108 61673134450321310597639 := by
  unfold tailWord_120108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190349324438351829200489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2920465765917802438933985 2190349324438351829200489)
  ·
    refine ⟨1642761993328763871900367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2190349324438351829200489 1642761993328763871900367)
    ·
      refine ⟨2464142989993145807850551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642761993328763871900367 2464142989993145807850551)
      ·
        refine ⟨3696214484989718711775827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464142989993145807850551 3696214484989718711775827)
        ·
          refine ⟨5544321727484578067663741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696214484989718711775827 5544321727484578067663741)
          ·
            refine ⟨2079120647806716775373903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5544321727484578067663741 2079120647806716775373903)
            ·
              refine ⟨3118680971710075163060855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079120647806716775373903 3118680971710075163060855)
              ·
                refine ⟨4678021457565112744591283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118680971710075163060855 4678021457565112744591283)
                ·
                  refine ⟨7017032186347669116886925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678021457565112744591283 7017032186347669116886925)
                  ·
                    refine ⟨2631387069880375918832597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7017032186347669116886925 2631387069880375918832597)
                    ·
                      refine ⟨61673134450321310597639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2631387069880375918832597 61673134450321310597639)
                      ·
                        rfl

theorem cell23_120108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_120108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120108 prefixEnd_120108 := by exact prefixLift 120108
  have htrace : WordTrace (prefixWord ++ tailWord_120108) baseStart_120108 baseEnd_120108 := by
    simpa [prefixWord, tailWord_120108, baseEnd_120108] using wordTrace_append hprefix tailTrace_120108
  have hstable : (prefixWord ++ tailWord_120108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120108).length < 2 ^ (prefixWord ++ tailWord_120108).sum := by decide
  have hdescent : baseEnd_120108 < baseStart_120108 := by decide
  rcases family_descends (prefixWord ++ tailWord_120108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120112 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_120112 : Nat := 118140960795 + 120112 * 2 ^ 59
def prefixEnd_120112 : Nat := 4983230072969 + 3 ^ 40 * 120112 * 2
def baseEnd_120112 : Nat := 61675188372939294947621

theorem tailTrace_120112 : CollatzResearch.WordTrace tailWord_120112 prefixEnd_120112 61675188372939294947621 := by
  unfold tailWord_120112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190422270431106170773295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2920563027241474894364393 2190422270431106170773295)
  ·
    refine ⟨3285633405646659256159943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190422270431106170773295 3285633405646659256159943)
    ·
      refine ⟨4928450108469988884239915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285633405646659256159943 4928450108469988884239915)
      ·
        refine ⟨7392675162704983326359873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928450108469988884239915 7392675162704983326359873)
        ·
          refine ⟨5544506372028737494769905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7392675162704983326359873 5544506372028737494769905)
          ·
            refine ⟨4158379779021553121077429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544506372028737494769905 4158379779021553121077429)
            ·
              refine ⟨389848104283270605101009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4158379779021553121077429 389848104283270605101009)
              ·
                refine ⟨292386078212452953825757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389848104283270605101009 292386078212452953825757)
                ·
                  refine ⟨109644779329669857684659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292386078212452953825757 109644779329669857684659)
                  ·
                    refine ⟨164467168994504786526989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109644779329669857684659 164467168994504786526989)
                    ·
                      refine ⟨61675188372939294947621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 164467168994504786526989 61675188372939294947621)
                      ·
                        rfl

theorem cell23_120112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_120112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120112 prefixEnd_120112 := by exact prefixLift 120112
  have htrace : WordTrace (prefixWord ++ tailWord_120112) baseStart_120112 baseEnd_120112 := by
    simpa [prefixWord, tailWord_120112, baseEnd_120112] using wordTrace_append hprefix tailTrace_120112
  have hstable : (prefixWord ++ tailWord_120112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120112).length < 2 ^ (prefixWord ++ tailWord_120112).sum := by decide
  have hdescent : baseEnd_120112 < baseStart_120112 := by decide
  rcases family_descends (prefixWord ++ tailWord_120112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120115 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 3, 5]
def baseStart_120115 : Nat := 118140960795 + 120115 * 2 ^ 59
def prefixEnd_120115 : Nat := 4983230072969 + 3 ^ 40 * 120115 * 2
def baseEnd_120115 : Nat := 20558909604967594403369

theorem tailTrace_120115 : CollatzResearch.WordTrace tailWord_120115 prefixEnd_120115 20558909604967594403369 := by
  unfold tailWord_120115
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380953959851343853905799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2920635973234229235937199 4380953959851343853905799)
  ·
    refine ⟨6571430939777015780858699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380953959851343853905799 6571430939777015780858699)
    ·
      refine ⟨9857146409665523671288049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6571430939777015780858699 9857146409665523671288049)
      ·
        refine ⟨7392859807249142753466037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857146409665523671288049 7392859807249142753466037)
        ·
          refine ⟨693080606929607133137441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7392859807249142753466037 693080606929607133137441)
          ·
            refine ⟨519810455197205349853081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693080606929607133137441 519810455197205349853081)
            ·
              refine ⟨389857841397904012389811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519810455197205349853081 389857841397904012389811)
              ·
                refine ⟨584786762096856018584717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389857841397904012389811 584786762096856018584717)
                ·
                  refine ⟨219295035786321006969269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584786762096856018584717 219295035786321006969269)
                  ·
                    refine ⟨20558909604967594403369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 219295035786321006969269 20558909604967594403369)
                    ·
                      rfl

theorem cell23_120115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].length) (baseStart_120115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120115 prefixEnd_120115 := by exact prefixLift 120115
  have htrace : WordTrace (prefixWord ++ tailWord_120115) baseStart_120115 baseEnd_120115 := by
    simpa [prefixWord, tailWord_120115, baseEnd_120115] using wordTrace_append hprefix tailTrace_120115
  have hstable : (prefixWord ++ tailWord_120115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120115).length < 2 ^ (prefixWord ++ tailWord_120115).sum := by decide
  have hdescent : baseEnd_120115 < baseStart_120115 := by decide
  rcases family_descends (prefixWord ++ tailWord_120115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120122 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_120122 : Nat := 118140960795 + 120122 * 2 ^ 59
def prefixEnd_120122 : Nat := 4983230072969 + 3 ^ 40 * 120122 * 2
def baseEnd_120122 : Nat := 61680323179484255822575

theorem tailTrace_120122 : CollatzResearch.WordTrace tailWord_120122 prefixEnd_120122 61680323179484255822575 := by
  unfold tailWord_120122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095302317706496012352655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2920806180550656032940413 1095302317706496012352655)
  ·
    refine ⟨1642953476559744018528983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095302317706496012352655 1642953476559744018528983)
    ·
      refine ⟨2464430214839616027793475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642953476559744018528983 2464430214839616027793475)
      ·
        refine ⟨3696645322259424041690213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464430214839616027793475 3696645322259424041690213)
        ·
          refine ⟨693120997923642007816915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3696645322259424041690213 693120997923642007816915)
          ·
            refine ⟨1039681496885463011725373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693120997923642007816915 1039681496885463011725373)
            ·
              refine ⟨389880561332048629397015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1039681496885463011725373 389880561332048629397015)
              ·
                refine ⟨584820841998072944095523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389880561332048629397015 584820841998072944095523)
                ·
                  refine ⟨877231262997109416143285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584820841998072944095523 877231262997109416143285)
                  ·
                    refine ⟨82240430905979007763433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 877231262997109416143285 82240430905979007763433)
                    ·
                      refine ⟨61680323179484255822575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82240430905979007763433 61680323179484255822575)
                      ·
                        rfl

theorem cell23_120122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_120122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120122 prefixEnd_120122 := by exact prefixLift 120122
  have htrace : WordTrace (prefixWord ++ tailWord_120122) baseStart_120122 baseEnd_120122 := by
    simpa [prefixWord, tailWord_120122, baseEnd_120122] using wordTrace_append hprefix tailTrace_120122
  have hstable : (prefixWord ++ tailWord_120122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120122).length < 2 ^ (prefixWord ++ tailWord_120122).sum := by decide
  have hdescent : baseEnd_120122 < baseStart_120122 := by decide
  rcases family_descends (prefixWord ++ tailWord_120122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120165 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_120165 : Nat := 118140960795 + 120165 * 2 ^ 59
def prefixEnd_120165 : Nat := 4983230072969 + 3 ^ 40 * 120165 * 2
def baseEnd_120165 : Nat := 61702402847627587584877

theorem tailTrace_120165 : CollatzResearch.WordTrace tailWord_120165 prefixEnd_120165 61702402847627587584877 := by
  unfold tailWord_120165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382777609670202393225949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2921851739780134928817299 4382777609670202393225949)
  ·
    refine ⟨1643541603626325897459731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4382777609670202393225949 1643541603626325897459731)
    ·
      refine ⟨2465312405439488846189597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643541603626325897459731 2465312405439488846189597)
      ·
        refine ⟨924492152039808317321099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2465312405439488846189597 924492152039808317321099)
        ·
          refine ⟨1386738228059712475981649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924492152039808317321099 1386738228059712475981649)
          ·
            refine ⟨1040053671044784356986237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386738228059712475981649 1040053671044784356986237)
            ·
              refine ⟨390020126641794133869839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040053671044784356986237 390020126641794133869839)
              ·
                refine ⟨585030189962691200804759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390020126641794133869839 585030189962691200804759)
                ·
                  refine ⟨877545284944036801207139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585030189962691200804759 877545284944036801207139)
                  ·
                    refine ⟨1316317927416055201810709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877545284944036801207139 1316317927416055201810709)
                    ·
                      refine ⟨61702402847627587584877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1316317927416055201810709 61702402847627587584877)
                      ·
                        rfl

theorem cell23_120165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_120165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120165 prefixEnd_120165 := by exact prefixLift 120165
  have htrace : WordTrace (prefixWord ++ tailWord_120165) baseStart_120165 baseEnd_120165 := by
    simpa [prefixWord, tailWord_120165, baseEnd_120165] using wordTrace_append hprefix tailTrace_120165
  have hstable : (prefixWord ++ tailWord_120165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120165).length < 2 ^ (prefixWord ++ tailWord_120165).sum := by decide
  have hdescent : baseEnd_120165 < baseStart_120165 := by decide
  rcases family_descends (prefixWord ++ tailWord_120165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120203 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 1, 2, 2]
def baseStart_120203 : Nat := 118140960795 + 120203 * 2 ^ 59
def prefixEnd_120203 : Nat := 4983230072969 + 3 ^ 40 * 120203 * 2
def baseEnd_120203 : Nat := 61721915112498438909703

theorem tailTrace_120203 : CollatzResearch.WordTrace tailWord_120203 prefixEnd_120203 61721915112498438909703 := by
  unfold tailWord_120203
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384163583532534883109263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2922775722355023255406175 4384163583532534883109263)
  ·
    refine ⟨6576245375298802324663895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4384163583532534883109263 6576245375298802324663895)
    ·
      refine ⟨9864368062948203486995843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576245375298802324663895 9864368062948203486995843)
      ·
        refine ⟨14796552094422305230493765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864368062948203486995843 14796552094422305230493765)
        ·
          refine ⟨2774353517704182230717581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14796552094422305230493765 2774353517704182230717581)
          ·
            refine ⟨1040382569139068336519093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2774353517704182230717581 1040382569139068336519093)
            ·
              refine ⟨97535865856787656548665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1040382569139068336519093 97535865856787656548665)
              ·
                refine ⟨73151899392590742411499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97535865856787656548665 73151899392590742411499)
                ·
                  refine ⟨109727849088886113617249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73151899392590742411499 109727849088886113617249)
                  ·
                    refine ⟨82295886816664585212937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109727849088886113617249 82295886816664585212937)
                    ·
                      refine ⟨61721915112498438909703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82295886816664585212937 61721915112498438909703)
                      ·
                        rfl

theorem cell23_120203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 2, 2].length) (baseStart_120203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120203 prefixEnd_120203 := by exact prefixLift 120203
  have htrace : WordTrace (prefixWord ++ tailWord_120203) baseStart_120203 baseEnd_120203 := by
    simpa [prefixWord, tailWord_120203, baseEnd_120203] using wordTrace_append hprefix tailTrace_120203
  have hstable : (prefixWord ++ tailWord_120203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120203).length < 2 ^ (prefixWord ++ tailWord_120203).sum := by decide
  have hdescent : baseEnd_120203 < baseStart_120203 := by decide
  rcases family_descends (prefixWord ++ tailWord_120203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120229 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_120229 : Nat := 118140960795 + 120229 * 2 ^ 59
def prefixEnd_120229 : Nat := 4983230072969 + 3 ^ 40 * 120229 * 2
def baseEnd_120229 : Nat := 61735265609515337184583

theorem tailTrace_120229 : CollatzResearch.WordTrace tailWord_120229 prefixEnd_120229 61735265609515337184583 := by
  unfold tailWord_120229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385111881438341323555741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2923407920958894215703827 4385111881438341323555741)
  ·
    refine ⟨1644416955539377996333403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4385111881438341323555741 1644416955539377996333403)
    ·
      refine ⟨2466625433309066994500105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644416955539377996333403 2466625433309066994500105)
      ·
        refine ⟨1849969074981800245875079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466625433309066994500105 1849969074981800245875079)
        ·
          refine ⟨2774953612472700368812619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849969074981800245875079 2774953612472700368812619)
          ·
            refine ⟨4162430418709050553218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774953612472700368812619 4162430418709050553218929)
            ·
              refine ⟨3121822814031787914914197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162430418709050553218929 3121822814031787914914197)
              ·
                refine ⟨146335444407740058511603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3121822814031787914914197 146335444407740058511603)
                ·
                  refine ⟨219503166611610087767405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146335444407740058511603 219503166611610087767405)
                  ·
                    refine ⟨82313687479353782912777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219503166611610087767405 82313687479353782912777)
                    ·
                      refine ⟨61735265609515337184583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82313687479353782912777 61735265609515337184583)
                      ·
                        rfl

theorem cell23_120229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_120229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120229 prefixEnd_120229 := by exact prefixLift 120229
  have htrace : WordTrace (prefixWord ++ tailWord_120229) baseStart_120229 baseEnd_120229 := by
    simpa [prefixWord, tailWord_120229, baseEnd_120229] using wordTrace_append hprefix tailTrace_120229
  have hstable : (prefixWord ++ tailWord_120229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120229).length < 2 ^ (prefixWord ++ tailWord_120229).sum := by decide
  have hdescent : baseEnd_120229 < baseStart_120229 := by decide
  rcases family_descends (prefixWord ++ tailWord_120229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120255 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_120255 : Nat := 118140960795 + 120255 * 2 ^ 59
def prefixEnd_120255 : Nat := 4983230072969 + 3 ^ 40 * 120255 * 2
def baseEnd_120255 : Nat := 61748616106532235459463

theorem tailTrace_120255 : CollatzResearch.WordTrace tailWord_120255 prefixEnd_120255 61748616106532235459463 := by
  unfold tailWord_120255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386060179344147764002219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2924040119562765176001479 4386060179344147764002219)
  ·
    refine ⟨6579090269016221646003329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386060179344147764002219 6579090269016221646003329)
    ·
      refine ⟨4934317701762166234502497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579090269016221646003329 4934317701762166234502497)
      ·
        refine ⟨3700738276321624675876873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4934317701762166234502497 3700738276321624675876873)
        ·
          refine ⟨2775553707241218506907655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700738276321624675876873 2775553707241218506907655)
          ·
            refine ⟨4163330560861827760361483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775553707241218506907655 4163330560861827760361483)
            ·
              refine ⟨6244995841292741640542225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163330560861827760361483 6244995841292741640542225)
              ·
                refine ⟨4683746880969556230406669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244995841292741640542225 4683746880969556230406669)
                ·
                  refine ⟨1756405080363583586402501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4683746880969556230406669 1756405080363583586402501)
                  ·
                    refine ⟨329325952568171922450469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756405080363583586402501 329325952568171922450469)
                    ·
                      refine ⟨61748616106532235459463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 329325952568171922450469 61748616106532235459463)
                      ·
                        rfl

theorem cell23_120255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_120255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120255 prefixEnd_120255 := by exact prefixLift 120255
  have htrace : WordTrace (prefixWord ++ tailWord_120255) baseStart_120255 baseEnd_120255 := by
    simpa [prefixWord, tailWord_120255, baseEnd_120255] using wordTrace_append hprefix tailTrace_120255
  have hstable : (prefixWord ++ tailWord_120255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120255).length < 2 ^ (prefixWord ++ tailWord_120255).sum := by decide
  have hdescent : baseEnd_120255 < baseStart_120255 := by decide
  rcases family_descends (prefixWord ++ tailWord_120255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120259 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 4, 2, 2]
def baseStart_120259 : Nat := 118140960795 + 120259 * 2 ^ 59
def prefixEnd_120259 : Nat := 4983230072969 + 3 ^ 40 * 120259 * 2
def baseEnd_120259 : Nat := 61750670029150219809445

theorem tailTrace_120259 : CollatzResearch.WordTrace tailWord_120259 prefixEnd_120259 61750670029150219809445 := by
  unfold tailWord_120259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386206071329656447147831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2924137380886437631431887 4386206071329656447147831)
  ·
    refine ⟨6579309106994484670721747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386206071329656447147831 6579309106994484670721747)
    ·
      refine ⟨9868963660491727006082621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579309106994484670721747 9868963660491727006082621)
      ·
        refine ⟨3700861372684397627280983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9868963660491727006082621 3700861372684397627280983)
        ·
          refine ⟨5551292059026596440921475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700861372684397627280983 5551292059026596440921475)
          ·
            refine ⟨8326938088539894661382213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551292059026596440921475 8326938088539894661382213)
            ·
              refine ⟨1561300891601230249009165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8326938088539894661382213 1561300891601230249009165)
              ·
                refine ⟨585487834350461343378437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561300891601230249009165 585487834350461343378437)
                ·
                  refine ⟨109778968940711501883457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585487834350461343378437 109778968940711501883457)
                  ·
                    refine ⟨82334226705533626412593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109778968940711501883457 82334226705533626412593)
                    ·
                      refine ⟨61750670029150219809445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82334226705533626412593 61750670029150219809445)
                      ·
                        rfl

theorem cell23_120259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_120259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120259 prefixEnd_120259 := by exact prefixLift 120259
  have htrace : WordTrace (prefixWord ++ tailWord_120259) baseStart_120259 baseEnd_120259 := by
    simpa [prefixWord, tailWord_120259, baseEnd_120259] using wordTrace_append hprefix tailTrace_120259
  have hstable : (prefixWord ++ tailWord_120259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120259).length < 2 ^ (prefixWord ++ tailWord_120259).sum := by decide
  have hdescent : baseEnd_120259 < baseStart_120259 := by decide
  rcases family_descends (prefixWord ++ tailWord_120259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120265 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 7]
def baseStart_120265 : Nat := 118140960795 + 120265 * 2 ^ 59
def prefixEnd_120265 : Nat := 4983230072969 + 3 ^ 40 * 120265 * 2
def baseEnd_120265 : Nat := 6861527879230799592713

theorem tailTrace_120265 : CollatzResearch.WordTrace tailWord_120265 prefixEnd_120265 6861527879230799592713 := by
  unfold tailWord_120265
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386424909307919471866249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2924283272871946314577499 4386424909307919471866249)
  ·
    refine ⟨3289818681980939603899687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4386424909307919471866249 3289818681980939603899687)
    ·
      refine ⟨4934728022971409405849531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3289818681980939603899687 4934728022971409405849531)
      ·
        refine ⟨7402092034457114108774297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934728022971409405849531 7402092034457114108774297)
        ·
          refine ⟨5551569025842835581580723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402092034457114108774297 5551569025842835581580723)
          ·
            refine ⟨8327353538764253372371085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551569025842835581580723 8327353538764253372371085)
            ·
              refine ⟨3122757577036595014639157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8327353538764253372371085 3122757577036595014639157)
              ·
                refine ⟨292758522847180782622421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3122757577036595014639157 292758522847180782622421)
                ·
                  refine ⟨6861527879230799592713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292758522847180782622421 6861527879230799592713)
                  ·
                    rfl

theorem cell23_120265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_120265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120265 prefixEnd_120265 := by exact prefixLift 120265
  have htrace : WordTrace (prefixWord ++ tailWord_120265) baseStart_120265 baseEnd_120265 := by
    simpa [prefixWord, tailWord_120265, baseEnd_120265] using wordTrace_append hprefix tailTrace_120265
  have hstable : (prefixWord ++ tailWord_120265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120265).length < 2 ^ (prefixWord ++ tailWord_120265).sum := by decide
  have hdescent : baseEnd_120265 < baseStart_120265 := by decide
  rcases family_descends (prefixWord ++ tailWord_120265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120282 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_120282 : Nat := 118140960795 + 120282 * 2 ^ 59
def prefixEnd_120282 : Nat := 4983230072969 + 3 ^ 40 * 120282 * 2
def baseEnd_120282 : Nat := 6862497787133736646871

theorem tailTrace_120282 : CollatzResearch.WordTrace tailWord_120282 prefixEnd_120282 6862497787133736646871 := by
  unfold tailWord_120282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096761237561582843808775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2924696633497554250156733 1096761237561582843808775)
  ·
    refine ⟨1645141856342374265713163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096761237561582843808775 1645141856342374265713163)
    ·
      refine ⟨2467712784513561398569745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645141856342374265713163 2467712784513561398569745)
      ·
        refine ⟨1850784588385171048927309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2467712784513561398569745 1850784588385171048927309)
        ·
          refine ⟨694044220644439143347741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1850784588385171048927309 694044220644439143347741)
          ·
            refine ⟨260266582741664678755403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694044220644439143347741 260266582741664678755403)
            ·
              refine ⟨390399874112497018133105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260266582741664678755403 390399874112497018133105)
              ·
                refine ⟨292799905584372763599829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390399874112497018133105 292799905584372763599829)
                ·
                  refine ⟨6862497787133736646871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292799905584372763599829 6862497787133736646871)
                  ·
                    rfl

theorem cell23_120282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_120282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120282 prefixEnd_120282 := by exact prefixLift 120282
  have htrace : WordTrace (prefixWord ++ tailWord_120282) baseStart_120282 baseEnd_120282 := by
    simpa [prefixWord, tailWord_120282, baseEnd_120282] using wordTrace_append hprefix tailTrace_120282
  have hstable : (prefixWord ++ tailWord_120282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120282).length < 2 ^ (prefixWord ++ tailWord_120282).sum := by decide
  have hdescent : baseEnd_120282 < baseStart_120282 := by decide
  rcases family_descends (prefixWord ++ tailWord_120282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120310 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_120310 : Nat := 118140960795 + 120310 * 2 ^ 59
def prefixEnd_120310 : Nat := 4983230072969 + 3 ^ 40 * 120310 * 2
def baseEnd_120310 : Nat := 61776857542529520271711

theorem tailTrace_120310 : CollatzResearch.WordTrace tailWord_120310 prefixEnd_120310 61776857542529520271711 := by
  unfold tailWord_120310
  simp only [CollatzResearch.WordTrace]
  refine ⟨274254137134055759828399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2925377462763261438169589 274254137134055759828399)
  ·
    refine ⟨411381205701083639742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274254137134055759828399 411381205701083639742599)
    ·
      refine ⟨617071808551625459613899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411381205701083639742599 617071808551625459613899)
      ·
        refine ⟨925607712827438189420849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617071808551625459613899 925607712827438189420849)
        ·
          refine ⟨694205784620578642065637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925607712827438189420849 694205784620578642065637)
          ·
            refine ⟨130163584616358495387307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 694205784620578642065637 130163584616358495387307)
            ·
              refine ⟨195245376924537743080961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130163584616358495387307 195245376924537743080961)
              ·
                refine ⟨146434032693403307310721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195245376924537743080961 146434032693403307310721)
                ·
                  refine ⟨109825524520052480483041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146434032693403307310721 109825524520052480483041)
                  ·
                    refine ⟨82369143390039360362281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109825524520052480483041 82369143390039360362281)
                    ·
                      refine ⟨61776857542529520271711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82369143390039360362281 61776857542529520271711)
                      ·
                        rfl

theorem cell23_120310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_120310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120310 prefixEnd_120310 := by exact prefixLift 120310
  have htrace : WordTrace (prefixWord ++ tailWord_120310) baseStart_120310 baseEnd_120310 := by
    simpa [prefixWord, tailWord_120310, baseEnd_120310] using wordTrace_append hprefix tailTrace_120310
  have hstable : (prefixWord ++ tailWord_120310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120310).length < 2 ^ (prefixWord ++ tailWord_120310).sum := by decide
  have hdescent : baseEnd_120310 < baseStart_120310 := by decide
  rcases family_descends (prefixWord ++ tailWord_120310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120335 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_120335 : Nat := 118140960795 + 120335 * 2 ^ 59
def prefixEnd_120335 : Nat := 4983230072969 + 3 ^ 40 * 120335 * 2
def baseEnd_120335 : Nat := 61789694558891922459095

theorem tailTrace_120335 : CollatzResearch.WordTrace tailWord_120335 prefixEnd_120335 61789694558891922459095 := by
  unfold tailWord_120335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388978019054321426914459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2925985346036214284609639 4388978019054321426914459)
  ·
    refine ⟨6583467028581482140371689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4388978019054321426914459 6583467028581482140371689)
    ·
      refine ⟨4937600271436111605278767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6583467028581482140371689 4937600271436111605278767)
      ·
        refine ⟨7406400407154167407918151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937600271436111605278767 7406400407154167407918151)
        ·
          refine ⟨11109600610731251111877227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7406400407154167407918151 11109600610731251111877227)
          ·
            refine ⟨16664400916096876667815841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109600610731251111877227 16664400916096876667815841)
            ·
              refine ⟨12498300687072657500861881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16664400916096876667815841 12498300687072657500861881)
              ·
                refine ⟨9373725515304493125646411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12498300687072657500861881 9373725515304493125646411)
                ·
                  refine ⟨14060588272956739688469617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9373725515304493125646411 14060588272956739688469617)
                  ·
                    refine ⟨10545441204717554766352213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14060588272956739688469617 10545441204717554766352213)
                    ·
                      refine ⟨61789694558891922459095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 10545441204717554766352213 61789694558891922459095)
                      ·
                        rfl

theorem cell23_120335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_120335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120335 prefixEnd_120335 := by exact prefixLift 120335
  have htrace : WordTrace (prefixWord ++ tailWord_120335) baseStart_120335 baseEnd_120335 := by
    simpa [prefixWord, tailWord_120335, baseEnd_120335] using wordTrace_append hprefix tailTrace_120335
  have hstable : (prefixWord ++ tailWord_120335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120335).length < 2 ^ (prefixWord ++ tailWord_120335).sum := by decide
  have hdescent : baseEnd_120335 < baseStart_120335 := by decide
  rcases family_descends (prefixWord ++ tailWord_120335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120349 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_120349 : Nat := 118140960795 + 120349 * 2 ^ 59
def prefixEnd_120349 : Nat := 4983230072969 + 3 ^ 40 * 120349 * 2
def baseEnd_120349 : Nat := 61796883288054867684031

theorem tailTrace_120349 : CollatzResearch.WordTrace tailWord_120349 prefixEnd_120349 61796883288054867684031 := by
  unfold tailWord_120349
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389488641003601817924101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2926325760669067878616067 4389488641003601817924101)
  ·
    refine ⟨823029120188175340860769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4389488641003601817924101 823029120188175340860769)
    ·
      refine ⟨617271840141131505645577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823029120188175340860769 617271840141131505645577)
      ·
        refine ⟨462953880105848629234183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617271840141131505645577 462953880105848629234183)
        ·
          refine ⟨694430820158772943851275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462953880105848629234183 694430820158772943851275)
          ·
            refine ⟨1041646230238159415776913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694430820158772943851275 1041646230238159415776913)
            ·
              refine ⟨781234672678619561832685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041646230238159415776913 781234672678619561832685)
              ·
                refine ⟨292963002254482335687257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781234672678619561832685 292963002254482335687257)
                ·
                  refine ⟨219722251690861751765443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292963002254482335687257 219722251690861751765443)
                  ·
                    refine ⟨329583377536292627648165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219722251690861751765443 329583377536292627648165)
                    ·
                      refine ⟨61796883288054867684031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 329583377536292627648165 61796883288054867684031)
                      ·
                        rfl

theorem cell23_120349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_120349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120349 prefixEnd_120349 := by exact prefixLift 120349
  have htrace : WordTrace (prefixWord ++ tailWord_120349) baseStart_120349 baseEnd_120349 := by
    simpa [prefixWord, tailWord_120349, baseEnd_120349] using wordTrace_append hprefix tailTrace_120349
  have hstable : (prefixWord ++ tailWord_120349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120349).length < 2 ^ (prefixWord ++ tailWord_120349).sum := by decide
  have hdescent : baseEnd_120349 < baseStart_120349 := by decide
  rcases family_descends (prefixWord ++ tailWord_120349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120366 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_120366 : Nat := 118140960795 + 120366 * 2 ^ 59
def prefixEnd_120366 : Nat := 4983230072969 + 3 ^ 40 * 120366 * 2
def baseEnd_120366 : Nat := 61805612459181301171453

theorem tailTrace_120366 : CollatzResearch.WordTrace tailWord_120366 prefixEnd_120366 61805612459181301171453 := by
  unfold tailWord_120366
  simp only [CollatzResearch.WordTrace]
  refine ⟨548763585242751715161619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2926739121294675814195301 548763585242751715161619)
  ·
    refine ⟨823145377864127572742429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548763585242751715161619 823145377864127572742429)
    ·
      refine ⟨308679516699047839778411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 823145377864127572742429 308679516699047839778411)
      ·
        refine ⟨463019275048571759667617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308679516699047839778411 463019275048571759667617)
        ·
          refine ⟨347264456286428819750713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463019275048571759667617 347264456286428819750713)
          ·
            refine ⟨260448342214821614813035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347264456286428819750713 260448342214821614813035)
            ·
              refine ⟨390672513322232422219553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260448342214821614813035 390672513322232422219553)
              ·
                refine ⟨293004384991674316664665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390672513322232422219553 293004384991674316664665)
                ·
                  refine ⟨219753288743755737498499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293004384991674316664665 219753288743755737498499)
                  ·
                    refine ⟨329629933115633606247749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219753288743755737498499 329629933115633606247749)
                    ·
                      refine ⟨61805612459181301171453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 329629933115633606247749 61805612459181301171453)
                      ·
                        rfl

theorem cell23_120366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_120366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120366 prefixEnd_120366 := by exact prefixLift 120366
  have htrace : WordTrace (prefixWord ++ tailWord_120366) baseStart_120366 baseEnd_120366 := by
    simpa [prefixWord, tailWord_120366, baseEnd_120366] using wordTrace_append hprefix tailTrace_120366
  have hstable : (prefixWord ++ tailWord_120366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120366).length < 2 ^ (prefixWord ++ tailWord_120366).sum := by decide
  have hdescent : baseEnd_120366 < baseStart_120366 := by decide
  rcases family_descends (prefixWord ++ tailWord_120366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120376 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_120376 : Nat := 118140960795 + 120376 * 2 ^ 59
def prefixEnd_120376 : Nat := 4983230072969 + 3 ^ 40 * 120376 * 2
def baseEnd_120376 : Nat := 20603582421908754015469

theorem tailTrace_120376 : CollatzResearch.WordTrace tailWord_120376 prefixEnd_120376 20603582421908754015469 := by
  unfold tailWord_120376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195236705952892714578491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2926982274603856952771321 2195236705952892714578491)
  ·
    refine ⟨3292855058929339071867737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2195236705952892714578491 3292855058929339071867737)
    ·
      refine ⟨2469641294197004303900803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292855058929339071867737 2469641294197004303900803)
      ·
        refine ⟨3704461941295506455851205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469641294197004303900803 3704461941295506455851205)
        ·
          refine ⟨694586613992907460472101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3704461941295506455851205 694586613992907460472101)
          ·
            refine ⟨130234990123670148838519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 694586613992907460472101 130234990123670148838519)
            ·
              refine ⟨195352485185505223257779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130234990123670148838519 195352485185505223257779)
              ·
                refine ⟨293028727778257834886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195352485185505223257779 293028727778257834886669)
                ·
                  refine ⟨109885772916846688082501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293028727778257834886669 109885772916846688082501)
                  ·
                    refine ⟨20603582421908754015469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109885772916846688082501 20603582421908754015469)
                    ·
                      rfl

theorem cell23_120376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_120376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120376 prefixEnd_120376 := by exact prefixLift 120376
  have htrace : WordTrace (prefixWord ++ tailWord_120376) baseStart_120376 baseEnd_120376 := by
    simpa [prefixWord, tailWord_120376, baseEnd_120376] using wordTrace_append hprefix tailTrace_120376
  have hstable : (prefixWord ++ tailWord_120376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120376).length < 2 ^ (prefixWord ++ tailWord_120376).sum := by decide
  have hdescent : baseEnd_120376 < baseStart_120376 := by decide
  rcases family_descends (prefixWord ++ tailWord_120376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120399 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_120399 : Nat := 118140960795 + 120399 * 2 ^ 59
def prefixEnd_120399 : Nat := 4983230072969 + 3 ^ 40 * 120399 * 2
def baseEnd_120399 : Nat := 61822557320779672058801

theorem tailTrace_120399 : CollatzResearch.WordTrace tailWord_120399 prefixEnd_120399 61822557320779672058801 := by
  unfold tailWord_120399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391312290822460357244251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2927541527214973571496167 4391312290822460357244251)
  ·
    refine ⟨6586968436233690535866377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391312290822460357244251 6586968436233690535866377)
    ·
      refine ⟨4940226327175267901899783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6586968436233690535866377 4940226327175267901899783)
      ·
        refine ⟨7410339490762901852849675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940226327175267901899783 7410339490762901852849675)
        ·
          refine ⟨11115509236144352779274513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410339490762901852849675 11115509236144352779274513)
          ·
            refine ⟨8336631927108264584455885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115509236144352779274513 8336631927108264584455885)
            ·
              refine ⟨3126236972665599219170957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8336631927108264584455885 3126236972665599219170957)
              ·
                refine ⟨1172338864749599707189109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126236972665599219170957 1172338864749599707189109)
                ·
                  refine ⟨109906768570274972548979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172338864749599707189109 109906768570274972548979)
                  ·
                    refine ⟨164860152855412458823469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109906768570274972548979 164860152855412458823469)
                    ·
                      refine ⟨61822557320779672058801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 164860152855412458823469 61822557320779672058801)
                      ·
                        rfl

theorem cell23_120399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_120399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120399 prefixEnd_120399 := by exact prefixLift 120399
  have htrace : WordTrace (prefixWord ++ tailWord_120399) baseStart_120399 baseEnd_120399 := by
    simpa [prefixWord, tailWord_120399, baseEnd_120399] using wordTrace_append hprefix tailTrace_120399
  have hstable : (prefixWord ++ tailWord_120399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120399).length < 2 ^ (prefixWord ++ tailWord_120399).sum := by decide
  have hdescent : baseEnd_120399 < baseStart_120399 := by decide
  rcases family_descends (prefixWord ++ tailWord_120399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120409 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 5, 2]
def baseStart_120409 : Nat := 118140960795 + 120409 * 2 ^ 59
def prefixEnd_120409 : Nat := 4983230072969 + 3 ^ 40 * 120409 * 2
def baseEnd_120409 : Nat := 61827692127324632933755

theorem tailTrace_120409 : CollatzResearch.WordTrace tailWord_120409 prefixEnd_120409 61827692127324632933755 := by
  unfold tailWord_120409
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391677020786232065108281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2927784680524154710072187 4391677020786232065108281)
  ·
    refine ⟨3293757765589674048831211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391677020786232065108281 3293757765589674048831211)
    ·
      refine ⟨4940636648384511073246817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293757765589674048831211 4940636648384511073246817)
      ·
        refine ⟨3705477486288383304935113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4940636648384511073246817 3705477486288383304935113)
        ·
          refine ⟨2779108114716287478701335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705477486288383304935113 2779108114716287478701335)
          ·
            refine ⟨4168662172074431218052003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779108114716287478701335 4168662172074431218052003)
            ·
              refine ⟨6252993258111646827078005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168662172074431218052003 6252993258111646827078005)
              ·
                refine ⟨586218117947966890038563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6252993258111646827078005 586218117947966890038563)
                ·
                  refine ⟨879327176921950335057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586218117947966890038563 879327176921950335057845)
                  ·
                    refine ⟨82436922836432843911673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 879327176921950335057845 82436922836432843911673)
                    ·
                      refine ⟨61827692127324632933755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82436922836432843911673 61827692127324632933755)
                      ·
                        rfl

theorem cell23_120409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_120409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120409 prefixEnd_120409 := by exact prefixLift 120409
  have htrace : WordTrace (prefixWord ++ tailWord_120409) baseStart_120409 baseEnd_120409 := by
    simpa [prefixWord, tailWord_120409, baseEnd_120409] using wordTrace_append hprefix tailTrace_120409
  have hstable : (prefixWord ++ tailWord_120409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120409).length < 2 ^ (prefixWord ++ tailWord_120409).sum := by decide
  have hdescent : baseEnd_120409 < baseStart_120409 := by decide
  rcases family_descends (prefixWord ++ tailWord_120409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120439 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_120439 : Nat := 118140960795 + 120439 * 2 ^ 59
def prefixEnd_120439 : Nat := 4983230072969 + 3 ^ 40 * 120439 * 2
def baseEnd_120439 : Nat := 61843096546959515558617

theorem tailTrace_120439 : CollatzResearch.WordTrace tailWord_120439 prefixEnd_120439 61843096546959515558617 := by
  unfold tailWord_120439
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392771210677547188700371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2928514140451698125800247 4392771210677547188700371)
  ·
    refine ⟨6589156816016320783050557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4392771210677547188700371 6589156816016320783050557)
    ·
      refine ⟨2470933806006120293643959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6589156816016320783050557 2470933806006120293643959)
      ·
        refine ⟨3706400709009180440465939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470933806006120293643959 3706400709009180440465939)
        ·
          refine ⟨5559601063513770660698909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706400709009180440465939 5559601063513770660698909)
          ·
            refine ⟨2084850398817663997762091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5559601063513770660698909 2084850398817663997762091)
            ·
              refine ⟨3127275598226495996643137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084850398817663997762091 3127275598226495996643137)
              ·
                refine ⟨2345456698669871997482353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127275598226495996643137 2345456698669871997482353)
                ·
                  refine ⟨1759092524002403998111765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345456698669871997482353 1759092524002403998111765)
                  ·
                    refine ⟨82457462062612687411489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1759092524002403998111765 82457462062612687411489)
                    ·
                      refine ⟨61843096546959515558617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82457462062612687411489 61843096546959515558617)
                      ·
                        rfl

theorem cell23_120439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_120439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120439 prefixEnd_120439 := by exact prefixLift 120439
  have htrace : WordTrace (prefixWord ++ tailWord_120439) baseStart_120439 baseEnd_120439 := by
    simpa [prefixWord, tailWord_120439, baseEnd_120439] using wordTrace_append hprefix tailTrace_120439
  have hstable : (prefixWord ++ tailWord_120439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120439).length < 2 ^ (prefixWord ++ tailWord_120439).sum := by decide
  have hdescent : baseEnd_120439 < baseStart_120439 := by decide
  rcases family_descends (prefixWord ++ tailWord_120439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120449 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_120449 : Nat := 118140960795 + 120449 * 2 ^ 59
def prefixEnd_120449 : Nat := 4983230072969 + 3 ^ 40 * 120449 * 2
def baseEnd_120449 : Nat := 20616077117834825477857

theorem tailTrace_120449 : CollatzResearch.WordTrace tailWord_120449 prefixEnd_120449 20616077117834825477857 := by
  unfold tailWord_120449
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393135940641318896564401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2928757293760879264376267 4393135940641318896564401)
  ·
    refine ⟨3294851955480989172423301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4393135940641318896564401 3294851955480989172423301)
    ·
      refine ⟨617784741652685469829369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3294851955480989172423301 617784741652685469829369)
      ·
        refine ⟨463338556239514102372027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617784741652685469829369 463338556239514102372027)
        ·
          refine ⟨695007834359271153558041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463338556239514102372027 695007834359271153558041)
          ·
            refine ⟨521255875769453365168531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695007834359271153558041 521255875769453365168531)
            ·
              refine ⟨781883813654180047752797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521255875769453365168531 781883813654180047752797)
              ·
                refine ⟨293206430120317517907299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781883813654180047752797 293206430120317517907299)
                ·
                  refine ⟨439809645180476276860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293206430120317517907299 439809645180476276860949)
                  ·
                    refine ⟨20616077117834825477857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 439809645180476276860949 20616077117834825477857)
                    ·
                      rfl

theorem cell23_120449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_120449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120449 prefixEnd_120449 := by exact prefixLift 120449
  have htrace : WordTrace (prefixWord ++ tailWord_120449) baseStart_120449 baseEnd_120449 := by
    simpa [prefixWord, tailWord_120449, baseEnd_120449] using wordTrace_append hprefix tailTrace_120449
  have hstable : (prefixWord ++ tailWord_120449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120449).length < 2 ^ (prefixWord ++ tailWord_120449).sum := by decide
  have hdescent : baseEnd_120449 < baseStart_120449 := by decide
  rcases family_descends (prefixWord ++ tailWord_120449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120459 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3]
def baseStart_120459 : Nat := 118140960795 + 120459 * 2 ^ 59
def prefixEnd_120459 : Nat := 4983230072969 + 3 ^ 40 * 120459 * 2
def baseEnd_120459 : Nat := 61853366160049437308525

theorem tailTrace_120459 : CollatzResearch.WordTrace tailWord_120459 prefixEnd_120459 61853366160049437308525 := by
  unfold tailWord_120459
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393500670605090604428431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2929000447070060402952287 4393500670605090604428431)
  ·
    refine ⟨6590251005907635906642647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4393500670605090604428431 6590251005907635906642647)
    ·
      refine ⟨9885376508861453859963971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590251005907635906642647 9885376508861453859963971)
      ·
        refine ⟨14828064763292180789945957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885376508861453859963971 14828064763292180789945957)
        ·
          refine ⟨2780262143117283898114867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14828064763292180789945957 2780262143117283898114867)
          ·
            refine ⟨4170393214675925847172301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780262143117283898114867 4170393214675925847172301)
            ·
              refine ⟨1563897455503472192689613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4170393214675925847172301 1563897455503472192689613)
              ·
                refine ⟨586461545813802072258605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1563897455503472192689613 586461545813802072258605)
                ·
                  refine ⟨219923079680175777096977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586461545813802072258605 219923079680175777096977)
                  ·
                    refine ⟨164942309760131832822733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219923079680175777096977 164942309760131832822733)
                    ·
                      refine ⟨61853366160049437308525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 164942309760131832822733 61853366160049437308525)
                      ·
                        rfl

theorem cell23_120459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].length) (baseStart_120459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120459 prefixEnd_120459 := by exact prefixLift 120459
  have htrace : WordTrace (prefixWord ++ tailWord_120459) baseStart_120459 baseEnd_120459 := by
    simpa [prefixWord, tailWord_120459, baseEnd_120459] using wordTrace_append hprefix tailTrace_120459
  have hstable : (prefixWord ++ tailWord_120459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120459).length < 2 ^ (prefixWord ++ tailWord_120459).sum := by decide
  have hdescent : baseEnd_120459 < baseStart_120459 := by decide
  rcases family_descends (prefixWord ++ tailWord_120459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120506 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_120506 : Nat := 118140960795 + 120506 * 2 ^ 59
def prefixEnd_120506 : Nat := 4983230072969 + 3 ^ 40 * 120506 * 2
def baseEnd_120506 : Nat := 61877499750810753420809

theorem tailTrace_120506 : CollatzResearch.WordTrace tailWord_120506 prefixEnd_120506 61877499750810753420809 := by
  unfold tailWord_120506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098803725358704407847343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2930143267623211754259581 1098803725358704407847343)
  ·
    refine ⟨1648205588038056611771015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098803725358704407847343 1648205588038056611771015)
    ·
      refine ⟨2472308382057084917656523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648205588038056611771015 2472308382057084917656523)
      ·
        refine ⟨3708462573085627376484785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472308382057084917656523 3708462573085627376484785)
        ·
          refine ⟨2781346929814220532363589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708462573085627376484785 2781346929814220532363589)
          ·
            refine ⟨521502549340166349818173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2781346929814220532363589 521502549340166349818173)
            ·
              refine ⟨195563456002562381181815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521502549340166349818173 195563456002562381181815)
              ·
                refine ⟨293345184003843571772723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195563456002562381181815 293345184003843571772723)
                ·
                  refine ⟨440017776005765357659085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293345184003843571772723 440017776005765357659085)
                  ·
                    refine ⟨165006666002162009122157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440017776005765357659085 165006666002162009122157)
                    ·
                      refine ⟨61877499750810753420809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165006666002162009122157 61877499750810753420809)
                      ·
                        rfl

theorem cell23_120506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_120506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120506 prefixEnd_120506 := by exact prefixLift 120506
  have htrace : WordTrace (prefixWord ++ tailWord_120506) baseStart_120506 baseEnd_120506 := by
    simpa [prefixWord, tailWord_120506, baseEnd_120506] using wordTrace_append hprefix tailTrace_120506
  have hstable : (prefixWord ++ tailWord_120506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120506).length < 2 ^ (prefixWord ++ tailWord_120506).sum := by decide
  have hdescent : baseEnd_120506 < baseStart_120506 := by decide
  rcases family_descends (prefixWord ++ tailWord_120506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120524 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_120524 : Nat := 118140960795 + 120524 * 2 ^ 59
def prefixEnd_120524 : Nat := 4983230072969 + 3 ^ 40 * 120524 * 2
def baseEnd_120524 : Nat := 61886742402591682995727

theorem tailTrace_120524 : CollatzResearch.WordTrace tailWord_120524 prefixEnd_120524 61886742402591682995727 := by
  unfold tailWord_120524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197935707684803352772313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2930580943579737803696417 2197935707684803352772313)
  ·
    refine ⟨1648451780763602514579235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2197935707684803352772313 1648451780763602514579235)
    ·
      refine ⟨2472677671145403771868853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648451780763602514579235 2472677671145403771868853)
      ·
        refine ⟨231813531669881603612705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2472677671145403771868853 231813531669881603612705)
        ·
          refine ⟨173860148752411202709529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231813531669881603612705 173860148752411202709529)
          ·
            refine ⟨130395111564308402032147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173860148752411202709529 130395111564308402032147)
            ·
              refine ⟨195592667346462603048221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130395111564308402032147 195592667346462603048221)
              ·
                refine ⟨73347250254923476143083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195592667346462603048221 73347250254923476143083)
                ·
                  refine ⟨110020875382385214214625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73347250254923476143083 110020875382385214214625)
                  ·
                    refine ⟨82515656536788910660969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110020875382385214214625 82515656536788910660969)
                    ·
                      refine ⟨61886742402591682995727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82515656536788910660969 61886742402591682995727)
                      ·
                        rfl

theorem cell23_120524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_120524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120524 prefixEnd_120524 := by exact prefixLift 120524
  have htrace : WordTrace (prefixWord ++ tailWord_120524) baseStart_120524 baseEnd_120524 := by
    simpa [prefixWord, tailWord_120524, baseEnd_120524] using wordTrace_append hprefix tailTrace_120524
  have hstable : (prefixWord ++ tailWord_120524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120524).length < 2 ^ (prefixWord ++ tailWord_120524).sum := by decide
  have hdescent : baseEnd_120524 < baseStart_120524 := by decide
  rcases family_descends (prefixWord ++ tailWord_120524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120541 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_120541 : Nat := 118140960795 + 120541 * 2 ^ 59
def prefixEnd_120541 : Nat := 4983230072969 + 3 ^ 40 * 120541 * 2
def baseEnd_120541 : Nat := 61895471573718116483149

theorem tailTrace_120541 : CollatzResearch.WordTrace tailWord_120541 prefixEnd_120541 61895471573718116483149 := by
  unfold tailWord_120541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396491456308018608913477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2930994304205345739275651 4396491456308018608913477)
  ·
    refine ⟨824342148057753489171277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4396491456308018608913477 824342148057753489171277)
    ·
      refine ⟨309128305521657558439229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 824342148057753489171277 309128305521657558439229)
      ·
        refine ⟨115923114570621584414711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309128305521657558439229 115923114570621584414711)
        ·
          refine ⟨173884671855932376622067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115923114570621584414711 173884671855932376622067)
          ·
            refine ⟨260827007783898564933101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173884671855932376622067 260827007783898564933101)
            ·
              refine ⟨97810127918961961849913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260827007783898564933101 97810127918961961849913)
              ·
                refine ⟨73357595939221471387435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97810127918961961849913 73357595939221471387435)
                ·
                  refine ⟨110036393908832207081153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73357595939221471387435 110036393908832207081153)
                  ·
                    refine ⟨82527295431624155310865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110036393908832207081153 82527295431624155310865)
                    ·
                      refine ⟨61895471573718116483149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82527295431624155310865 61895471573718116483149)
                      ·
                        rfl

theorem cell23_120541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_120541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120541 prefixEnd_120541 := by exact prefixLift 120541
  have htrace : WordTrace (prefixWord ++ tailWord_120541) baseStart_120541 baseEnd_120541 := by
    simpa [prefixWord, tailWord_120541, baseEnd_120541] using wordTrace_append hprefix tailTrace_120541
  have hstable : (prefixWord ++ tailWord_120541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120541).length < 2 ^ (prefixWord ++ tailWord_120541).sum := by decide
  have hdescent : baseEnd_120541 < baseStart_120541 := by decide
  rcases family_descends (prefixWord ++ tailWord_120541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120549 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_120549 : Nat := 118140960795 + 120549 * 2 ^ 59
def prefixEnd_120549 : Nat := 4983230072969 + 3 ^ 40 * 120549 * 2
def baseEnd_120549 : Nat := 61899579418954085183111

theorem tailTrace_120549 : CollatzResearch.WordTrace tailWord_120549 prefixEnd_120549 61899579418954085183111 := by
  unfold tailWord_120549
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396783240279035975204701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2931188826852690650136467 4396783240279035975204701)
  ·
    refine ⟨1648793715104638490701763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4396783240279035975204701 1648793715104638490701763)
    ·
      refine ⟨2473190572656957736052645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648793715104638490701763 2473190572656957736052645)
      ·
        refine ⟨463723232373179575509871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2473190572656957736052645 463723232373179575509871)
        ·
          refine ⟨695584848559769363264807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463723232373179575509871 695584848559769363264807)
          ·
            refine ⟨1043377272839654044897211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695584848559769363264807 1043377272839654044897211)
            ·
              refine ⟨1565065909259481067345817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043377272839654044897211 1565065909259481067345817)
              ·
                refine ⟨1173799431944610800509363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565065909259481067345817 1173799431944610800509363)
                ·
                  refine ⟨1760699147916916200764045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173799431944610800509363 1760699147916916200764045)
                  ·
                    refine ⟨660262180468843575286517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1760699147916916200764045 660262180468843575286517)
                    ·
                      refine ⟨61899579418954085183111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 660262180468843575286517 61899579418954085183111)
                      ·
                        rfl

theorem cell23_120549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_120549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120549 prefixEnd_120549 := by exact prefixLift 120549
  have htrace : WordTrace (prefixWord ++ tailWord_120549) baseStart_120549 baseEnd_120549 := by
    simpa [prefixWord, tailWord_120549, baseEnd_120549] using wordTrace_append hprefix tailTrace_120549
  have hstable : (prefixWord ++ tailWord_120549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120549).length < 2 ^ (prefixWord ++ tailWord_120549).sum := by decide
  have hdescent : baseEnd_120549 < baseStart_120549 := by decide
  rcases family_descends (prefixWord ++ tailWord_120549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120557 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_120557 : Nat := 118140960795 + 120557 * 2 ^ 59
def prefixEnd_120557 : Nat := 4983230072969 + 3 ^ 40 * 120557 * 2
def baseEnd_120557 : Nat := 61903687264190053883075

theorem tailTrace_120557 : CollatzResearch.WordTrace tailWord_120557 prefixEnd_120557 61903687264190053883075 := by
  unfold tailWord_120557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397075024250053341495925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2931383349500035560997283 4397075024250053341495925)
  ·
    refine ⟨412225783523442500765243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4397075024250053341495925 412225783523442500765243)
    ·
      refine ⟨618338675285163751147865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412225783523442500765243 618338675285163751147865)
      ·
        refine ⟨463754006463872813360899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618338675285163751147865 463754006463872813360899)
        ·
          refine ⟨695631009695809220041349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463754006463872813360899 695631009695809220041349)
          ·
            refine ⟨130430814317964228757753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695631009695809220041349 130430814317964228757753)
            ·
              refine ⟨97823110738473171568315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130430814317964228757753 97823110738473171568315)
              ·
                refine ⟨146734666107709757352473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97823110738473171568315 146734666107709757352473)
                ·
                  refine ⟨110050999580782318014355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146734666107709757352473 110050999580782318014355)
                  ·
                    refine ⟨165076499371173477021533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110050999580782318014355 165076499371173477021533)
                    ·
                      refine ⟨61903687264190053883075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165076499371173477021533 61903687264190053883075)
                      ·
                        rfl

theorem cell23_120557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_120557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120557 prefixEnd_120557 := by exact prefixLift 120557
  have htrace : WordTrace (prefixWord ++ tailWord_120557) baseStart_120557 baseEnd_120557 := by
    simpa [prefixWord, tailWord_120557, baseEnd_120557] using wordTrace_append hprefix tailTrace_120557
  have hstable : (prefixWord ++ tailWord_120557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120557).length < 2 ^ (prefixWord ++ tailWord_120557).sum := by decide
  have hdescent : baseEnd_120557 < baseStart_120557 := by decide
  rcases family_descends (prefixWord ++ tailWord_120557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120559 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_120559 : Nat := 118140960795 + 120559 * 2 ^ 59
def prefixEnd_120559 : Nat := 4983230072969 + 3 ^ 40 * 120559 * 2
def baseEnd_120559 : Nat := 61904714225499046058065

theorem tailTrace_120559 : CollatzResearch.WordTrace tailWord_120559 prefixEnd_120559 61904714225499046058065 := by
  unfold tailWord_120559
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397147970242807683068731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2931431980161871788712487 4397147970242807683068731)
  ·
    refine ⟨6595721955364211524603097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4397147970242807683068731 6595721955364211524603097)
    ·
      refine ⟨4946791466523158643452323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6595721955364211524603097 4946791466523158643452323)
      ·
        refine ⟨7420187199784737965178485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946791466523158643452323 7420187199784737965178485)
        ·
          refine ⟨695642549979819184235483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7420187199784737965178485 695642549979819184235483)
          ·
            refine ⟨1043463824969728776353225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695642549979819184235483 1043463824969728776353225)
            ·
              refine ⟨782597868727296582264919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043463824969728776353225 782597868727296582264919)
              ·
                refine ⟨1173896803090944873397379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782597868727296582264919 1173896803090944873397379)
                ·
                  refine ⟨1760845204636417310096069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173896803090944873397379 1760845204636417310096069)
                  ·
                    refine ⟨330158475869328245643013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760845204636417310096069 330158475869328245643013)
                    ·
                      refine ⟨61904714225499046058065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 330158475869328245643013 61904714225499046058065)
                      ·
                        rfl

theorem cell23_120559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_120559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120559 prefixEnd_120559 := by exact prefixLift 120559
  have htrace : WordTrace (prefixWord ++ tailWord_120559) baseStart_120559 baseEnd_120559 := by
    simpa [prefixWord, tailWord_120559, baseEnd_120559] using wordTrace_append hprefix tailTrace_120559
  have hstable : (prefixWord ++ tailWord_120559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120559).length < 2 ^ (prefixWord ++ tailWord_120559).sum := by decide
  have hdescent : baseEnd_120559 < baseStart_120559 := by decide
  rcases family_descends (prefixWord ++ tailWord_120559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120566 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_120566 : Nat := 118140960795 + 120566 * 2 ^ 59
def prefixEnd_120566 : Nat := 4983230072969 + 3 ^ 40 * 120566 * 2
def baseEnd_120566 : Nat := 61908308590080518670533

theorem tailTrace_120566 : CollatzResearch.WordTrace tailWord_120566 prefixEnd_120566 61908308590080518670533 := by
  unfold tailWord_120566
  simp only [CollatzResearch.WordTrace]
  refine ⟨274837705076090492410847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2931602187478298585715701 274837705076090492410847)
  ·
    refine ⟨412256557614135738616271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274837705076090492410847 412256557614135738616271)
    ·
      refine ⟨618384836421203607924407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412256557614135738616271 618384836421203607924407)
      ·
        refine ⟨927577254631805411886611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618384836421203607924407 927577254631805411886611)
        ·
          refine ⟨1391365881947708117829917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927577254631805411886611 1391365881947708117829917)
          ·
            refine ⟨521762205730390544186219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391365881947708117829917 521762205730390544186219)
            ·
              refine ⟨782643308595585816279329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521762205730390544186219 782643308595585816279329)
              ·
                refine ⟨586982481446689362209497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782643308595585816279329 586982481446689362209497)
                ·
                  refine ⟨440236861085017021657123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586982481446689362209497 440236861085017021657123)
                  ·
                    refine ⟨660355291627525532485685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440236861085017021657123 660355291627525532485685)
                    ·
                      refine ⟨61908308590080518670533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 660355291627525532485685 61908308590080518670533)
                      ·
                        rfl

theorem cell23_120566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_120566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120566 prefixEnd_120566 := by exact prefixLift 120566
  have htrace : WordTrace (prefixWord ++ tailWord_120566) baseStart_120566 baseEnd_120566 := by
    simpa [prefixWord, tailWord_120566, baseEnd_120566] using wordTrace_append hprefix tailTrace_120566
  have hstable : (prefixWord ++ tailWord_120566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120566).length < 2 ^ (prefixWord ++ tailWord_120566).sum := by decide
  have hdescent : baseEnd_120566 < baseStart_120566 := by decide
  rcases family_descends (prefixWord ++ tailWord_120566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120633 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_120633 : Nat := 118140960795 + 120633 * 2 ^ 59
def prefixEnd_120633 : Nat := 4983230072969 + 3 ^ 40 * 120633 * 2
def baseEnd_120633 : Nat := 20647570597977252177575

theorem tailTrace_120633 : CollatzResearch.WordTrace tailWord_120633 prefixEnd_120633 20647570597977252177575 := by
  unfold tailWord_120633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399846971974718321262553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933231314649812214175035 4399846971974718321262553)
  ·
    refine ⟨3299885228981038740946915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4399846971974718321262553 3299885228981038740946915)
    ·
      refine ⟨4949827843471558111420373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299885228981038740946915 4949827843471558111420373)
      ·
        refine ⟨116011590081364643236415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4949827843471558111420373 116011590081364643236415)
        ·
          refine ⟨174017385122046964854623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116011590081364643236415 174017385122046964854623)
          ·
            refine ⟨261026077683070447281935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174017385122046964854623 261026077683070447281935)
            ·
              refine ⟨391539116524605670922903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261026077683070447281935 391539116524605670922903)
              ·
                refine ⟨587308674786908506384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391539116524605670922903 587308674786908506384355)
                ·
                  refine ⟨880963012180362759576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587308674786908506384355 880963012180362759576533)
                  ·
                    refine ⟨20647570597977252177575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 880963012180362759576533 20647570597977252177575)
                    ·
                      rfl

theorem cell23_120633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_120633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120633 prefixEnd_120633 := by exact prefixLift 120633
  have htrace : WordTrace (prefixWord ++ tailWord_120633) baseStart_120633 baseEnd_120633 := by
    simpa [prefixWord, tailWord_120633, baseEnd_120633] using wordTrace_append hprefix tailTrace_120633
  have hstable : (prefixWord ++ tailWord_120633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120633).length < 2 ^ (prefixWord ++ tailWord_120633).sum := by decide
  have hdescent : baseEnd_120633 < baseStart_120633 := by decide
  rcases family_descends (prefixWord ++ tailWord_120633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120649 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_120649 : Nat := 118140960795 + 120649 * 2 ^ 59
def prefixEnd_120649 : Nat := 4983230072969 + 3 ^ 40 * 120649 * 2
def baseEnd_120649 : Nat := 61950927484403693932651

theorem tailTrace_120649 : CollatzResearch.WordTrace tailWord_120649 prefixEnd_120649 61950927484403693932651 := by
  unfold tailWord_120649
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400430539916753053845001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933620359944502035896667 4400430539916753053845001)
  ·
    refine ⟨3300322904937564790383751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4400430539916753053845001 3300322904937564790383751)
    ·
      refine ⟨4950484357406347185575627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300322904937564790383751 4950484357406347185575627)
      ·
        refine ⟨7425726536109520778363441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950484357406347185575627 7425726536109520778363441)
        ·
          refine ⟨5569294902082140583772581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425726536109520778363441 5569294902082140583772581)
          ·
            refine ⟨1044242794140401359457359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5569294902082140583772581 1044242794140401359457359)
            ·
              refine ⟨1566364191210602039186039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044242794140401359457359 1566364191210602039186039)
              ·
                refine ⟨2349546286815903058779059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566364191210602039186039 2349546286815903058779059)
                ·
                  refine ⟨3524319430223854588168589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349546286815903058779059 3524319430223854588168589)
                  ·
                    refine ⟨1321619786333945470563221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3524319430223854588168589 1321619786333945470563221)
                    ·
                      refine ⟨61950927484403693932651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1321619786333945470563221 61950927484403693932651)
                      ·
                        rfl

theorem cell23_120649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_120649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120649 prefixEnd_120649 := by exact prefixLift 120649
  have htrace : WordTrace (prefixWord ++ tailWord_120649) baseStart_120649 baseEnd_120649 := by
    simpa [prefixWord, tailWord_120649, baseEnd_120649] using wordTrace_append hprefix tailTrace_120649
  have hstable : (prefixWord ++ tailWord_120649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120649).length < 2 ^ (prefixWord ++ tailWord_120649).sum := by decide
  have hdescent : baseEnd_120649 < baseStart_120649 := by decide
  rcases family_descends (prefixWord ++ tailWord_120649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120656 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_120656 : Nat := 118140960795 + 120656 * 2 ^ 59
def prefixEnd_120656 : Nat := 4983230072969 + 3 ^ 40 * 120656 * 2
def baseEnd_120656 : Nat := 61954521848985166545119

theorem tailTrace_120656 : CollatzResearch.WordTrace tailWord_120656 prefixEnd_120656 61954521848985166545119 := by
  unfold tailWord_120656
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200342925445696624674911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2933790567260928832899881 2200342925445696624674911)
  ·
    refine ⟨3300514388168544937012367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2200342925445696624674911 3300514388168544937012367)
    ·
      refine ⟨4950771582252817405518551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300514388168544937012367 4950771582252817405518551)
      ·
        refine ⟨7426157373379226108277827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950771582252817405518551 7426157373379226108277827)
        ·
          refine ⟨11139236060068839162416741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426157373379226108277827 11139236060068839162416741)
          ·
            refine ⟨2088606761262907342953139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11139236060068839162416741 2088606761262907342953139)
            ·
              refine ⟨3132910141894361014429709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088606761262907342953139 3132910141894361014429709)
              ·
                refine ⟨1174841303210385380411141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3132910141894361014429709 1174841303210385380411141)
                ·
                  refine ⟨220282744351947258827089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174841303210385380411141 220282744351947258827089)
                  ·
                    refine ⟨165212058263960444120317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220282744351947258827089 165212058263960444120317)
                    ·
                      refine ⟨61954521848985166545119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165212058263960444120317 61954521848985166545119)
                      ·
                        rfl

theorem cell23_120656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_120656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120656 prefixEnd_120656 := by exact prefixLift 120656
  have htrace : WordTrace (prefixWord ++ tailWord_120656) baseStart_120656 baseEnd_120656 := by
    simpa [prefixWord, tailWord_120656, baseEnd_120656] using wordTrace_append hprefix tailTrace_120656
  have hstable : (prefixWord ++ tailWord_120656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120656).length < 2 ^ (prefixWord ++ tailWord_120656).sum := by decide
  have hdescent : baseEnd_120656 < baseStart_120656 := by decide
  rcases family_descends (prefixWord ++ tailWord_120656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120714 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_120714 : Nat := 118140960795 + 120714 * 2 ^ 59
def prefixEnd_120714 : Nat := 4983230072969 + 3 ^ 40 * 120714 * 2
def baseEnd_120714 : Nat := 20661434575648646539951

theorem tailTrace_120714 : CollatzResearch.WordTrace tailWord_120714 prefixEnd_120714 20661434575648646539951 := by
  unfold tailWord_120714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100700321170317288740299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2935200856454179436640797 1100700321170317288740299)
  ·
    refine ⟨1651050481755475933110449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100700321170317288740299 1651050481755475933110449)
    ·
      refine ⟨1238287861316606949832837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651050481755475933110449 1238287861316606949832837)
      ·
        refine ⟨232178973996863803093657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1238287861316606949832837 232178973996863803093657)
        ·
          refine ⟨174134230497647852320243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232178973996863803093657 174134230497647852320243)
          ·
            refine ⟨261201345746471778480365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174134230497647852320243 261201345746471778480365)
            ·
              refine ⟨97950504654926916930137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261201345746471778480365 97950504654926916930137)
              ·
                refine ⟨73462878491195187697603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97950504654926916930137 73462878491195187697603)
                ·
                  refine ⟨110194317736792781546405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73462878491195187697603 110194317736792781546405)
                  ·
                    refine ⟨20661434575648646539951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110194317736792781546405 20661434575648646539951)
                    ·
                      rfl

theorem cell23_120714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_120714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120714 prefixEnd_120714 := by exact prefixLift 120714
  have htrace : WordTrace (prefixWord ++ tailWord_120714) baseStart_120714 baseEnd_120714 := by
    simpa [prefixWord, tailWord_120714, baseEnd_120714] using wordTrace_append hprefix tailTrace_120714
  have hstable : (prefixWord ++ tailWord_120714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120714).length < 2 ^ (prefixWord ++ tailWord_120714).sum := by decide
  have hdescent : baseEnd_120714 < baseStart_120714 := by decide
  rcases family_descends (prefixWord ++ tailWord_120714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120736 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_120736 : Nat := 118140960795 + 120736 * 2 ^ 59
def prefixEnd_120736 : Nat := 4983230072969 + 3 ^ 40 * 120736 * 2
def baseEnd_120736 : Nat := 20665200100448284514917

theorem tailTrace_120736 : CollatzResearch.WordTrace tailWord_120736 prefixEnd_120736 20665200100448284514917 := by
  unfold tailWord_120736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201801845300783456131031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2935735793734377941508041 2201801845300783456131031)
  ·
    refine ⟨3302702767951175184196547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201801845300783456131031 3302702767951175184196547)
    ·
      refine ⟨4954054151926762776294821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302702767951175184196547 4954054151926762776294821)
      ·
        refine ⟨928885153486268020555279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4954054151926762776294821 928885153486268020555279)
        ·
          refine ⟨1393327730229402030832919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928885153486268020555279 1393327730229402030832919)
          ·
            refine ⟨2089991595344103046249379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393327730229402030832919 2089991595344103046249379)
            ·
              refine ⟨3134987393016154569374069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089991595344103046249379 3134987393016154569374069)
              ·
                refine ⟨293905068095264490878819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3134987393016154569374069 293905068095264490878819)
                ·
                  refine ⟨440857602142896736318229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293905068095264490878819 440857602142896736318229)
                  ·
                    refine ⟨20665200100448284514917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 440857602142896736318229 20665200100448284514917)
                    ·
                      rfl

theorem cell23_120736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_120736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120736 prefixEnd_120736 := by exact prefixLift 120736
  have htrace : WordTrace (prefixWord ++ tailWord_120736) baseStart_120736 baseEnd_120736 := by
    simpa [prefixWord, tailWord_120736, baseEnd_120736] using wordTrace_append hprefix tailTrace_120736
  have hstable : (prefixWord ++ tailWord_120736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120736).length < 2 ^ (prefixWord ++ tailWord_120736).sum := by decide
  have hdescent : baseEnd_120736 < baseStart_120736 := by decide
  rcases family_descends (prefixWord ++ tailWord_120736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120740 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_120740 : Nat := 118140960795 + 120740 * 2 ^ 59
def prefixEnd_120740 : Nat := 4983230072969 + 3 ^ 40 * 120740 * 2
def baseEnd_120740 : Nat := 20665884741320945964911

theorem tailTrace_120740 : CollatzResearch.WordTrace tailWord_120740 prefixEnd_120740 20665884741320945964911 := by
  unfold tailWord_120740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201874791293537797703837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2935833055058050396938449 2201874791293537797703837)
  ·
    refine ⟨825703046735076674138939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2201874791293537797703837 825703046735076674138939)
    ·
      refine ⟨1238554570102615011208409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825703046735076674138939 1238554570102615011208409)
      ·
        refine ⟨928915927576961258406307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238554570102615011208409 928915927576961258406307)
        ·
          refine ⟨1393373891365441887609461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928915927576961258406307 1393373891365441887609461)
          ·
            refine ⟨130628802315510176963387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1393373891365441887609461 130628802315510176963387)
            ·
              refine ⟨195943203473265265445081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130628802315510176963387 195943203473265265445081)
              ·
                refine ⟨146957402604948949083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195943203473265265445081 146957402604948949083811)
                ·
                  refine ⟨220436103907423423625717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146957402604948949083811 220436103907423423625717)
                  ·
                    refine ⟨20665884741320945964911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220436103907423423625717 20665884741320945964911)
                    ·
                      rfl

theorem cell23_120740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_120740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120740 prefixEnd_120740 := by exact prefixLift 120740
  have htrace : WordTrace (prefixWord ++ tailWord_120740) baseStart_120740 baseEnd_120740 := by
    simpa [prefixWord, tailWord_120740, baseEnd_120740] using wordTrace_append hprefix tailTrace_120740
  have hstable : (prefixWord ++ tailWord_120740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120740).length < 2 ^ (prefixWord ++ tailWord_120740).sum := by decide
  have hdescent : baseEnd_120740 < baseStart_120740 := by decide
  rcases family_descends (prefixWord ++ tailWord_120740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120753 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_120753 : Nat := 118140960795 + 120753 * 2 ^ 59
def prefixEnd_120753 : Nat := 4983230072969 + 3 ^ 40 * 120753 * 2
def baseEnd_120753 : Nat := 20668109824157095677391

theorem tailTrace_120753 : CollatzResearch.WordTrace tailWord_120753 prefixEnd_120753 20668109824157095677391 := by
  unfold tailWord_120753
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404223731539978815630913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2936149154359985877087275 4404223731539978815630913)
  ·
    refine ⟨3303167798654984111723185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4404223731539978815630913 3303167798654984111723185)
    ·
      refine ⟨2477375848991238083792389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3303167798654984111723185 2477375848991238083792389)
      ·
        refine ⟨464507971685857140711073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2477375848991238083792389 464507971685857140711073)
        ·
          refine ⟨348380978764392855533305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464507971685857140711073 348380978764392855533305)
          ·
            refine ⟨261285734073294641649979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348380978764392855533305 261285734073294641649979)
            ·
              refine ⟨391928601109941962474969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261285734073294641649979 391928601109941962474969)
              ·
                refine ⟨293946450832456471856227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391928601109941962474969 293946450832456471856227)
                ·
                  refine ⟨440919676248684707784341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293946450832456471856227 440919676248684707784341)
                  ·
                    refine ⟨20668109824157095677391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 440919676248684707784341 20668109824157095677391)
                    ·
                      rfl

theorem cell23_120753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_120753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120753 prefixEnd_120753 := by exact prefixLift 120753
  have htrace : WordTrace (prefixWord ++ tailWord_120753) baseStart_120753 baseEnd_120753 := by
    simpa [prefixWord, tailWord_120753, baseEnd_120753] using wordTrace_append hprefix tailTrace_120753
  have hstable : (prefixWord ++ tailWord_120753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120753).length < 2 ^ (prefixWord ++ tailWord_120753).sum := by decide
  have hdescent : baseEnd_120753 < baseStart_120753 := by decide
  rcases family_descends (prefixWord ++ tailWord_120753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120760 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_120760 : Nat := 118140960795 + 120760 * 2 ^ 59
def prefixEnd_120760 : Nat := 4983230072969 + 3 ^ 40 * 120760 * 2
def baseEnd_120760 : Nat := 62007923837052759644641

theorem tailTrace_120760 : CollatzResearch.WordTrace tailWord_120760 prefixEnd_120760 62007923837052759644641 := by
  unfold tailWord_120760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202239521257309505567867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2936319361676412674090489 2202239521257309505567867)
  ·
    refine ⟨3303359281885964258351801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202239521257309505567867 3303359281885964258351801)
    ·
      refine ⟨2477519461414473193763851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3303359281885964258351801 2477519461414473193763851)
      ·
        refine ⟨3716279192121709790645777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477519461414473193763851 3716279192121709790645777)
        ·
          refine ⟨2787209394091282342984333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716279192121709790645777 2787209394091282342984333)
          ·
            refine ⟨1045203522784230878619125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787209394091282342984333 1045203522784230878619125)
            ·
              refine ⟨97987830261021644870543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1045203522784230878619125 97987830261021644870543)
              ·
                refine ⟨146981745391532467305815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97987830261021644870543 146981745391532467305815)
                ·
                  refine ⟨220472618087298700958723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146981745391532467305815 220472618087298700958723)
                  ·
                    refine ⟨330708927130948051438085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220472618087298700958723 330708927130948051438085)
                    ·
                      refine ⟨62007923837052759644641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 330708927130948051438085 62007923837052759644641)
                      ·
                        rfl

theorem cell23_120760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_120760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120760 prefixEnd_120760 := by exact prefixLift 120760
  have htrace : WordTrace (prefixWord ++ tailWord_120760) baseStart_120760 baseEnd_120760 := by
    simpa [prefixWord, tailWord_120760, baseEnd_120760] using wordTrace_append hprefix tailTrace_120760
  have hstable : (prefixWord ++ tailWord_120760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120760).length < 2 ^ (prefixWord ++ tailWord_120760).sum := by decide
  have hdescent : baseEnd_120760 < baseStart_120760 := by decide
  rcases family_descends (prefixWord ++ tailWord_120760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120766 : List Nat := [4, 2, 1, 1, 1, 14]
def baseStart_120766 : Nat := 118140960795 + 120766 * 2 ^ 59
def prefixEnd_120766 : Nat := 4983230072969 + 3 ^ 40 * 120766 * 2
def baseEnd_120766 : Nat := 255189319839422782591

theorem tailTrace_120766 : CollatzResearch.WordTrace tailWord_120766 prefixEnd_120766 255189319839422782591 := by
  unfold tailWord_120766
  simp only [CollatzResearch.WordTrace]
  refine ⟨550587235061610254481769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2936465253661921357236101 550587235061610254481769)
  ·
    refine ⟨412940426296207690861327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 550587235061610254481769 412940426296207690861327)
    ·
      refine ⟨619410639444311536291991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412940426296207690861327 619410639444311536291991)
      ·
        refine ⟨929115959166467304437987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619410639444311536291991 929115959166467304437987)
        ·
          refine ⟨1393673938749700956656981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929115959166467304437987 1393673938749700956656981)
          ·
            refine ⟨255189319839422782591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 1393673938749700956656981 255189319839422782591)
            ·
              rfl

theorem cell23_120766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 14].length) (baseStart_120766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120766 prefixEnd_120766 := by exact prefixLift 120766
  have htrace : WordTrace (prefixWord ++ tailWord_120766) baseStart_120766 baseEnd_120766 := by
    simpa [prefixWord, tailWord_120766, baseEnd_120766] using wordTrace_append hprefix tailTrace_120766
  have hstable : (prefixWord ++ tailWord_120766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120766).length < 2 ^ (prefixWord ++ tailWord_120766).sum := by decide
  have hdescent : baseEnd_120766 < baseStart_120766 := by decide
  rcases family_descends (prefixWord ++ tailWord_120766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120777 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 1, 2, 2]
def baseStart_120777 : Nat := 118140960795 + 120777 * 2 ^ 59
def prefixEnd_120777 : Nat := 4983230072969 + 3 ^ 40 * 120777 * 2
def baseEnd_120777 : Nat := 62016653008179193132063

theorem tailTrace_120777 : CollatzResearch.WordTrace tailWord_120777 prefixEnd_120777 62016653008179193132063 := by
  unfold tailWord_120777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405099083453030914504585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2936732722302020609669723 4405099083453030914504585)
  ·
    refine ⟨3303824312589773185878439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4405099083453030914504585 3303824312589773185878439)
    ·
      refine ⟨4955736468884659778817659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303824312589773185878439 4955736468884659778817659)
      ·
        refine ⟨7433604703326989668226489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955736468884659778817659 7433604703326989668226489)
        ·
          refine ⟨5575203527495242251169867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7433604703326989668226489 5575203527495242251169867)
          ·
            refine ⟨8362805291242863376754801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575203527495242251169867 8362805291242863376754801)
            ·
              refine ⟨6272103968432147532566101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362805291242863376754801 6272103968432147532566101)
              ·
                refine ⟨73501218380064228897259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6272103968432147532566101 73501218380064228897259)
                ·
                  refine ⟨110251827570096343345889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73501218380064228897259 110251827570096343345889)
                  ·
                    refine ⟨82688870677572257509417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110251827570096343345889 82688870677572257509417)
                    ·
                      refine ⟨62016653008179193132063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82688870677572257509417 62016653008179193132063)
                      ·
                        rfl

theorem cell23_120777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 2, 2].length) (baseStart_120777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120777 prefixEnd_120777 := by exact prefixLift 120777
  have htrace : WordTrace (prefixWord ++ tailWord_120777) baseStart_120777 baseEnd_120777 := by
    simpa [prefixWord, tailWord_120777, baseEnd_120777] using wordTrace_append hprefix tailTrace_120777
  have hstable : (prefixWord ++ tailWord_120777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120777).length < 2 ^ (prefixWord ++ tailWord_120777).sum := by decide
  have hdescent : baseEnd_120777 < baseStart_120777 := by decide
  rcases family_descends (prefixWord ++ tailWord_120777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120810 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_120810 : Nat := 118140960795 + 120810 * 2 ^ 59
def prefixEnd_120810 : Nat := 4983230072969 + 3 ^ 40 * 120810 * 2
def baseEnd_120810 : Nat := 62033597869777564019411

theorem tailTrace_120810 : CollatzResearch.WordTrace tailWord_120810 prefixEnd_120810 62033597869777564019411 := by
  unfold tailWord_120810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101575673083369387613971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2937535128222318366970589 1101575673083369387613971)
  ·
    refine ⟨1652363509625054081420957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101575673083369387613971 1652363509625054081420957)
    ·
      refine ⟨619636316109395280532859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1652363509625054081420957 619636316109395280532859)
      ·
        refine ⟨929454474164092920799289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619636316109395280532859 929454474164092920799289)
        ·
          refine ⟨697090855623069690599467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929454474164092920799289 697090855623069690599467)
          ·
            refine ⟨1045636283434604535899201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697090855623069690599467 1045636283434604535899201)
            ·
              refine ⟨784227212575953401924401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045636283434604535899201 784227212575953401924401)
              ·
                refine ⟨588170409431965051443301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784227212575953401924401 588170409431965051443301)
                ·
                  refine ⟨110281951768493447145619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588170409431965051443301 110281951768493447145619)
                  ·
                    refine ⟨165422927652740170718429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110281951768493447145619 165422927652740170718429)
                    ·
                      refine ⟨62033597869777564019411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165422927652740170718429 62033597869777564019411)
                      ·
                        rfl

theorem cell23_120810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_120810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120810 prefixEnd_120810 := by exact prefixLift 120810
  have htrace : WordTrace (prefixWord ++ tailWord_120810) baseStart_120810 baseEnd_120810 := by
    simpa [prefixWord, tailWord_120810, baseEnd_120810] using wordTrace_append hprefix tailTrace_120810
  have hstable : (prefixWord ++ tailWord_120810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120810).length < 2 ^ (prefixWord ++ tailWord_120810).sum := by decide
  have hdescent : baseEnd_120810 < baseStart_120810 := by decide
  rcases family_descends (prefixWord ++ tailWord_120810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120814 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_120814 : Nat := 118140960795 + 120814 * 2 ^ 59
def prefixEnd_120814 : Nat := 4983230072969 + 3 ^ 40 * 120814 * 2
def baseEnd_120814 : Nat := 62035651792395548369393

theorem tailTrace_120814 : CollatzResearch.WordTrace tailWord_120814 prefixEnd_120814 62035651792395548369393 := by
  unfold tailWord_120814
  simp only [CollatzResearch.WordTrace]
  refine ⟨550806073039873279200187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2937632389545990822400997 550806073039873279200187)
  ·
    refine ⟨826209109559809918800281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550806073039873279200187 826209109559809918800281)
    ·
      refine ⟨619656832169857439100211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 826209109559809918800281 619656832169857439100211)
      ·
        refine ⟨929485248254786158650317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619656832169857439100211 929485248254786158650317)
        ·
          refine ⟨348556968095544809493869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929485248254786158650317 348556968095544809493869)
          ·
            refine ⟨130708863035829303560201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348556968095544809493869 130708863035829303560201)
            ·
              refine ⟨98031647276871977670151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130708863035829303560201 98031647276871977670151)
              ·
                refine ⟨147047470915307966505227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98031647276871977670151 147047470915307966505227)
                ·
                  refine ⟨220571206372961949757841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147047470915307966505227 220571206372961949757841)
                  ·
                    refine ⟨165428404779721462318381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220571206372961949757841 165428404779721462318381)
                    ·
                      refine ⟨62035651792395548369393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165428404779721462318381 62035651792395548369393)
                      ·
                        rfl

theorem cell23_120814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_120814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120814 prefixEnd_120814 := by exact prefixLift 120814
  have htrace : WordTrace (prefixWord ++ tailWord_120814) baseStart_120814 baseEnd_120814 := by
    simpa [prefixWord, tailWord_120814, baseEnd_120814] using wordTrace_append hprefix tailTrace_120814
  have hstable : (prefixWord ++ tailWord_120814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120814).length < 2 ^ (prefixWord ++ tailWord_120814).sum := by decide
  have hdescent : baseEnd_120814 < baseStart_120814 := by decide
  rcases family_descends (prefixWord ++ tailWord_120814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120838 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_120838 : Nat := 118140960795 + 120838 * 2 ^ 59
def prefixEnd_120838 : Nat := 4983230072969 + 3 ^ 40 * 120838 * 2
def baseEnd_120838 : Nat := 20682658442701151489761

theorem tailTrace_120838 : CollatzResearch.WordTrace tailWord_120838 prefixEnd_120838 20682658442701151489761 := by
  unfold tailWord_120838
  simp only [CollatzResearch.WordTrace]
  refine ⟨137728873007251197889849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2938215957488025554983445 137728873007251197889849)
  ·
    refine ⟨103296654755438398417387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137728873007251197889849 103296654755438398417387)
    ·
      refine ⟨154944982133157597626081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103296654755438398417387 154944982133157597626081)
      ·
        refine ⟨116208736599868198219561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154944982133157597626081 116208736599868198219561)
        ·
          refine ⟨87156552449901148664671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116208736599868198219561 87156552449901148664671)
          ·
            refine ⟨130734828674851722997007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87156552449901148664671 130734828674851722997007)
            ·
              refine ⟨196102243012277584495511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130734828674851722997007 196102243012277584495511)
              ·
                refine ⟨294153364518416376743267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196102243012277584495511 294153364518416376743267)
                ·
                  refine ⟨441230046777624565114901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294153364518416376743267 441230046777624565114901)
                  ·
                    refine ⟨20682658442701151489761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 441230046777624565114901 20682658442701151489761)
                    ·
                      rfl

theorem cell23_120838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_120838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120838 prefixEnd_120838 := by exact prefixLift 120838
  have htrace : WordTrace (prefixWord ++ tailWord_120838) baseStart_120838 baseEnd_120838 := by
    simpa [prefixWord, tailWord_120838, baseEnd_120838] using wordTrace_append hprefix tailTrace_120838
  have hstable : (prefixWord ++ tailWord_120838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120838).length < 2 ^ (prefixWord ++ tailWord_120838).sum := by decide
  have hdescent : baseEnd_120838 < baseStart_120838 := by decide
  rcases family_descends (prefixWord ++ tailWord_120838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120883 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3]
def baseStart_120883 : Nat := 118140960795 + 120883 * 2 ^ 59
def prefixEnd_120883 : Nat := 4983230072969 + 3 ^ 40 * 120883 * 2
def baseEnd_120883 : Nat := 62071081957555778406575

theorem tailTrace_120883 : CollatzResearch.WordTrace tailWord_120883 prefixEnd_120883 62071081957555778406575 := by
  unfold tailWord_120883
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408965221069011017863303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2939310147379340678575535 4408965221069011017863303)
  ·
    refine ⟨6613447831603516526794955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4408965221069011017863303 6613447831603516526794955)
    ·
      refine ⟨9920171747405274790192433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6613447831603516526794955 9920171747405274790192433)
      ·
        refine ⟨7440128810553956092644325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9920171747405274790192433 7440128810553956092644325)
        ·
          refine ⟨1395024151978866767370811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7440128810553956092644325 1395024151978866767370811)
          ·
            refine ⟨2092536227968300151056217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395024151978866767370811 2092536227968300151056217)
            ·
              refine ⟨1569402170976225113292163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092536227968300151056217 1569402170976225113292163)
              ·
                refine ⟨2354103256464337669938245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569402170976225113292163 2354103256464337669938245)
                ·
                  refine ⟨441394360587063313113421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354103256464337669938245 441394360587063313113421)
                  ·
                    refine ⟨165522885220148742417533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441394360587063313113421 165522885220148742417533)
                    ·
                      refine ⟨62071081957555778406575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165522885220148742417533 62071081957555778406575)
                      ·
                        rfl

theorem cell23_120883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_120883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120883 prefixEnd_120883 := by exact prefixLift 120883
  have htrace : WordTrace (prefixWord ++ tailWord_120883) baseStart_120883 baseEnd_120883 := by
    simpa [prefixWord, tailWord_120883, baseEnd_120883] using wordTrace_append hprefix tailTrace_120883
  have hstable : (prefixWord ++ tailWord_120883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120883).length < 2 ^ (prefixWord ++ tailWord_120883).sum := by decide
  have hdescent : baseEnd_120883 < baseStart_120883 := by decide
  rcases family_descends (prefixWord ++ tailWord_120883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120903 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 4, 5]
def baseStart_120903 : Nat := 118140960795 + 120903 * 2 ^ 59
def prefixEnd_120903 : Nat := 4983230072969 + 3 ^ 40 * 120903 * 2
def baseEnd_120903 : Nat := 20693783856881900052161

theorem tailTrace_120903 : CollatzResearch.WordTrace tailWord_120903 prefixEnd_120903 20693783856881900052161 := by
  unfold tailWord_120903
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409694680996554433591363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2939796453997702955727575 4409694680996554433591363)
  ·
    refine ⟨6614542021494831650387045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409694680996554433591363 6614542021494831650387045)
    ·
      refine ⟨1240226629030280934447571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6614542021494831650387045 1240226629030280934447571)
      ·
        refine ⟨1860339943545421401671357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240226629030280934447571 1860339943545421401671357)
        ·
          refine ⟨697627478829533025626759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1860339943545421401671357 697627478829533025626759)
          ·
            refine ⟨1046441218244299538440139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697627478829533025626759 1046441218244299538440139)
            ·
              refine ⟨1569661827366449307660209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046441218244299538440139 1569661827366449307660209)
              ·
                refine ⟨1177246370524836980745157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569661827366449307660209 1177246370524836980745157)
                ·
                  refine ⟨220733694473406933889717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177246370524836980745157 220733694473406933889717)
                  ·
                    refine ⟨20693783856881900052161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220733694473406933889717 20693783856881900052161)
                    ·
                      rfl

theorem cell23_120903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_120903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120903 prefixEnd_120903 := by exact prefixLift 120903
  have htrace : WordTrace (prefixWord ++ tailWord_120903) baseStart_120903 baseEnd_120903 := by
    simpa [prefixWord, tailWord_120903, baseEnd_120903] using wordTrace_append hprefix tailTrace_120903
  have hstable : (prefixWord ++ tailWord_120903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120903).length < 2 ^ (prefixWord ++ tailWord_120903).sum := by decide
  have hdescent : baseEnd_120903 < baseStart_120903 := by decide
  rcases family_descends (prefixWord ++ tailWord_120903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120920 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_120920 : Nat := 118140960795 + 120920 * 2 ^ 59
def prefixEnd_120920 : Nat := 4983230072969 + 3 ^ 40 * 120920 * 2
def baseEnd_120920 : Nat := 20696693580590711214635

theorem tailTrace_120920 : CollatzResearch.WordTrace tailWord_120920 prefixEnd_120920 20696693580590711214635 := by
  unfold tailWord_120920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205157360967483168480107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2940209814623310891306809 2205157360967483168480107)
  ·
    refine ⟨3307736041451224752720161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2205157360967483168480107 3307736041451224752720161)
    ·
      refine ⟨2480802031088418564540121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307736041451224752720161 2480802031088418564540121)
      ·
        refine ⟨1860601523316313923405091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480802031088418564540121 1860601523316313923405091)
        ·
          refine ⟨2790902284974470885107637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860601523316313923405091 2790902284974470885107637)
          ·
            refine ⟨261647089216356645478841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2790902284974470885107637 261647089216356645478841)
            ·
              refine ⟨196235316912267484109131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261647089216356645478841 196235316912267484109131)
              ·
                refine ⟨294352975368401226163697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196235316912267484109131 294352975368401226163697)
                ·
                  refine ⟨220764731526300919622773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294352975368401226163697 220764731526300919622773)
                  ·
                    refine ⟨20696693580590711214635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220764731526300919622773 20696693580590711214635)
                    ·
                      rfl

theorem cell23_120920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_120920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120920 prefixEnd_120920 := by exact prefixLift 120920
  have htrace : WordTrace (prefixWord ++ tailWord_120920) baseStart_120920 baseEnd_120920 := by
    simpa [prefixWord, tailWord_120920, baseEnd_120920] using wordTrace_append hprefix tailTrace_120920
  have hstable : (prefixWord ++ tailWord_120920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120920).length < 2 ^ (prefixWord ++ tailWord_120920).sum := by decide
  have hdescent : baseEnd_120920 < baseStart_120920 := by decide
  rcases family_descends (prefixWord ++ tailWord_120920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120940 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_120940 : Nat := 118140960795 + 120940 * 2 ^ 59
def prefixEnd_120940 : Nat := 4983230072969 + 3 ^ 40 * 120940 * 2
def baseEnd_120940 : Nat := 62100350354862055393813

theorem tailTrace_120940 : CollatzResearch.WordTrace tailWord_120940 prefixEnd_120940 62100350354862055393813 := by
  unfold tailWord_120940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205522090931254876344137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2940696121241673168458849 2205522090931254876344137)
  ·
    refine ⟨1654141568198441157258103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2205522090931254876344137 1654141568198441157258103)
    ·
      refine ⟨2481212352297661735887155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654141568198441157258103 2481212352297661735887155)
      ·
        refine ⟨3721818528446492603830733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481212352297661735887155 3721818528446492603830733)
        ·
          refine ⟨1395681948167434726436525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3721818528446492603830733 1395681948167434726436525)
          ·
            refine ⟨523380730562788022413697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395681948167434726436525 523380730562788022413697)
            ·
              refine ⟨392535547922091016810273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523380730562788022413697 392535547922091016810273)
              ·
                refine ⟨294401660941568262607705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392535547922091016810273 294401660941568262607705)
                ·
                  refine ⟨220801245706176196955779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294401660941568262607705 220801245706176196955779)
                  ·
                    refine ⟨331201868559264295433669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220801245706176196955779 331201868559264295433669)
                    ·
                      refine ⟨62100350354862055393813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 331201868559264295433669 62100350354862055393813)
                      ·
                        rfl

theorem cell23_120940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_120940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120940 prefixEnd_120940 := by exact prefixLift 120940
  have htrace : WordTrace (prefixWord ++ tailWord_120940) baseStart_120940 baseEnd_120940 := by
    simpa [prefixWord, tailWord_120940, baseEnd_120940] using wordTrace_append hprefix tailTrace_120940
  have hstable : (prefixWord ++ tailWord_120940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120940).length < 2 ^ (prefixWord ++ tailWord_120940).sum := by decide
  have hdescent : baseEnd_120940 < baseStart_120940 := by decide
  rcases family_descends (prefixWord ++ tailWord_120940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120957 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_120957 : Nat := 118140960795 + 120957 * 2 ^ 59
def prefixEnd_120957 : Nat := 4983230072969 + 3 ^ 40 * 120957 * 2
def baseEnd_120957 : Nat := 62109079525988488881235

theorem tailTrace_120957 : CollatzResearch.WordTrace tailWord_120957 prefixEnd_120957 62109079525988488881235 := by
  unfold tailWord_120957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411664222800921656057125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2941109481867281104038083 4411664222800921656057125)
  ·
    refine ⟨827187041775172810510711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4411664222800921656057125 827187041775172810510711)
    ·
      refine ⟨1240780562662759215766067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827187041775172810510711 1240780562662759215766067)
      ·
        refine ⟨1861170843994138823649101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240780562662759215766067 1861170843994138823649101)
        ·
          refine ⟨697939066497802058868413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1861170843994138823649101 697939066497802058868413)
          ·
            refine ⟨261727149936675772075655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 697939066497802058868413 261727149936675772075655)
            ·
              refine ⟨392590724905013658113483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261727149936675772075655 392590724905013658113483)
              ·
                refine ⟨588886087357520487170225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392590724905013658113483 588886087357520487170225)
                ·
                  refine ⟨441664565518140365377669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588886087357520487170225 441664565518140365377669)
                  ·
                    refine ⟨82812106034651318508313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441664565518140365377669 82812106034651318508313)
                    ·
                      refine ⟨62109079525988488881235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82812106034651318508313 62109079525988488881235)
                      ·
                        rfl

theorem cell23_120957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_120957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120957 prefixEnd_120957 := by exact prefixLift 120957
  have htrace : WordTrace (prefixWord ++ tailWord_120957) baseStart_120957 baseEnd_120957 := by
    simpa [prefixWord, tailWord_120957, baseEnd_120957] using wordTrace_append hprefix tailTrace_120957
  have hstable : (prefixWord ++ tailWord_120957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120957).length < 2 ^ (prefixWord ++ tailWord_120957).sum := by decide
  have hdescent : baseEnd_120957 < baseStart_120957 := by decide
  rcases family_descends (prefixWord ++ tailWord_120957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120974 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_120974 : Nat := 118140960795 + 120974 * 2 ^ 59
def prefixEnd_120974 : Nat := 4983230072969 + 3 ^ 40 * 120974 * 2
def baseEnd_120974 : Nat := 62117808697114922368657

theorem tailTrace_120974 : CollatzResearch.WordTrace tailWord_120974 prefixEnd_120974 62117808697114922368657 := by
  unfold tailWord_120974
  simp only [CollatzResearch.WordTrace]
  refine ⟨551535532967416694928247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2941522842492889039617317 551535532967416694928247)
  ·
    refine ⟨827303299451125042392371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551535532967416694928247 827303299451125042392371)
    ·
      refine ⟨1240954949176687563588557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827303299451125042392371 1240954949176687563588557)
      ·
        refine ⟨465358105941257836345709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1240954949176687563588557 465358105941257836345709)
        ·
          refine ⟨174509289727971688629641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465358105941257836345709 174509289727971688629641)
          ·
            refine ⟨130881967295978766472231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174509289727971688629641 130881967295978766472231)
            ·
              refine ⟨196322950943968149708347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130881967295978766472231 196322950943968149708347)
              ·
                refine ⟨294484426415952224562521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196322950943968149708347 294484426415952224562521)
                ·
                  refine ⟨220863319811964168421891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294484426415952224562521 220863319811964168421891)
                  ·
                    refine ⟨331294979717946252632837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220863319811964168421891 331294979717946252632837)
                    ·
                      refine ⟨62117808697114922368657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 331294979717946252632837 62117808697114922368657)
                      ·
                        rfl

theorem cell23_120974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_120974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_120974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_120974 prefixEnd_120974 := by exact prefixLift 120974
  have htrace : WordTrace (prefixWord ++ tailWord_120974) baseStart_120974 baseEnd_120974 := by
    simpa [prefixWord, tailWord_120974, baseEnd_120974] using wordTrace_append hprefix tailTrace_120974
  have hstable : (prefixWord ++ tailWord_120974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120974).length < 2 ^ (prefixWord ++ tailWord_120974).sum := by decide
  have hdescent : baseEnd_120974 < baseStart_120974 := by decide
  rcases family_descends (prefixWord ++ tailWord_120974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_121043 : Nat := 118140960795 + 121043 * 2 ^ 59
def prefixEnd_121043 : Nat := 4983230072969 + 3 ^ 40 * 121043 * 2
def baseEnd_121043 : Nat := 62153238862275152405839

theorem tailTrace_121043 : CollatzResearch.WordTrace tailWord_121043 prefixEnd_121043 62153238862275152405839 := by
  unfold tailWord_121043
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414800900489358343687783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2943200600326238895791855 4414800900489358343687783)
  ·
    refine ⟨6622201350734037515531675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414800900489358343687783 6622201350734037515531675)
    ·
      refine ⟨9933302026101056273297513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622201350734037515531675 9933302026101056273297513)
      ·
        refine ⟨7449976519575792204973135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9933302026101056273297513 7449976519575792204973135)
        ·
          refine ⟨11174964779363688307459703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449976519575792204973135 11174964779363688307459703)
          ·
            refine ⟨16762447169045532461189555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174964779363688307459703 16762447169045532461189555)
            ·
              refine ⟨25143670753568298691784333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16762447169045532461189555 25143670753568298691784333)
              ·
                refine ⟨9428876532588112009419125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25143670753568298691784333 9428876532588112009419125)
                ·
                  refine ⟨883957174930135500883043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9428876532588112009419125 883957174930135500883043)
                  ·
                    refine ⟨1325935762395203251324565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883957174930135500883043 1325935762395203251324565)
                    ·
                      refine ⟨62153238862275152405839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1325935762395203251324565 62153238862275152405839)
                      ·
                        rfl

theorem cell23_121043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_121043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121043 prefixEnd_121043 := by exact prefixLift 121043
  have htrace : WordTrace (prefixWord ++ tailWord_121043) baseStart_121043 baseEnd_121043 := by
    simpa [prefixWord, tailWord_121043, baseEnd_121043] using wordTrace_append hprefix tailTrace_121043
  have hstable : (prefixWord ++ tailWord_121043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121043).length < 2 ^ (prefixWord ++ tailWord_121043).sum := by decide
  have hdescent : baseEnd_121043 < baseStart_121043 := by decide
  rcases family_descends (prefixWord ++ tailWord_121043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121050 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_121050 : Nat := 118140960795 + 121050 * 2 ^ 59
def prefixEnd_121050 : Nat := 4983230072969 + 3 ^ 40 * 121050 * 2
def baseEnd_121050 : Nat := 62156833226856625018307

theorem tailTrace_121050 : CollatzResearch.WordTrace tailWord_121050 prefixEnd_121050 62156833226856625018307 := by
  unfold tailWord_121050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103764052865999634798151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2943370807642665692795069 1103764052865999634798151)
  ·
    refine ⟨1655646079298999452197227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103764052865999634798151 1655646079298999452197227)
    ·
      refine ⟨2483469118948499178295841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655646079298999452197227 2483469118948499178295841)
      ·
        refine ⟨1862601839211374383721881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483469118948499178295841 1862601839211374383721881)
        ·
          refine ⟨1396951379408530787791411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862601839211374383721881 1396951379408530787791411)
          ·
            refine ⟨2095427069112796181687117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396951379408530787791411 2095427069112796181687117)
            ·
              refine ⟨785785150917298568132669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095427069112796181687117 785785150917298568132669)
              ·
                refine ⟨294669431593986963049751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785785150917298568132669 294669431593986963049751)
                ·
                  refine ⟨442004147390980444574627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294669431593986963049751 442004147390980444574627)
                  ·
                    refine ⟨663006221086470666861941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 442004147390980444574627 663006221086470666861941)
                    ·
                      refine ⟨62156833226856625018307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 663006221086470666861941 62156833226856625018307)
                      ·
                        rfl

theorem cell23_121050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_121050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121050 prefixEnd_121050 := by exact prefixLift 121050
  have htrace : WordTrace (prefixWord ++ tailWord_121050) baseStart_121050 baseEnd_121050 := by
    simpa [prefixWord, tailWord_121050, baseEnd_121050] using wordTrace_append hprefix tailTrace_121050
  have hstable : (prefixWord ++ tailWord_121050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121050).length < 2 ^ (prefixWord ++ tailWord_121050).sum := by decide
  have hdescent : baseEnd_121050 < baseStart_121050 := by decide
  rcases family_descends (prefixWord ++ tailWord_121050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121057 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_121057 : Nat := 118140960795 + 121057 * 2 ^ 59
def prefixEnd_121057 : Nat := 4983230072969 + 3 ^ 40 * 121057 * 2
def baseEnd_121057 : Nat := 20720142530479365876925

theorem tailTrace_121057 : CollatzResearch.WordTrace tailWord_121057 prefixEnd_121057 20720142530479365876925 := by
  unfold tailWord_121057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415311522438638734697425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2943541014959092489798283 4415311522438638734697425)
  ·
    refine ⟨3311483641828979051023069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4415311522438638734697425 3311483641828979051023069)
    ·
      refine ⟨1241806365685867144133651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3311483641828979051023069 1241806365685867144133651)
      ·
        refine ⟨1862709548528800716200477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241806365685867144133651 1862709548528800716200477)
        ·
          refine ⟨698516080698300268575179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1862709548528800716200477 698516080698300268575179)
          ·
            refine ⟨1047774121047450402862769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698516080698300268575179 1047774121047450402862769)
            ·
              refine ⟨785830590785587802147077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047774121047450402862769 785830590785587802147077)
              ·
                refine ⟨147343235772297712902577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785830590785587802147077 147343235772297712902577)
                ·
                  refine ⟨110507426829223284676933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147343235772297712902577 110507426829223284676933)
                  ·
                    refine ⟨20720142530479365876925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110507426829223284676933 20720142530479365876925)
                    ·
                      rfl

theorem cell23_121057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_121057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121057 prefixEnd_121057 := by exact prefixLift 121057
  have htrace : WordTrace (prefixWord ++ tailWord_121057) baseStart_121057 baseEnd_121057 := by
    simpa [prefixWord, tailWord_121057, baseEnd_121057] using wordTrace_append hprefix tailTrace_121057
  have hstable : (prefixWord ++ tailWord_121057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121057).length < 2 ^ (prefixWord ++ tailWord_121057).sum := by decide
  have hdescent : baseEnd_121057 < baseStart_121057 := by decide
  rcases family_descends (prefixWord ++ tailWord_121057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121074 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_121074 : Nat := 118140960795 + 121074 * 2 ^ 59
def prefixEnd_121074 : Nat := 4983230072969 + 3 ^ 40 * 121074 * 2
def baseEnd_121074 : Nat := 20723052254188177039399

theorem tailTrace_121074 : CollatzResearch.WordTrace tailWord_121074 prefixEnd_121074 20723052254188177039399 := by
  unfold tailWord_121074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103982890844262659516569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2943954375584700425377517 1103982890844262659516569)
  ·
    refine ⟨827987168133196994637427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1103982890844262659516569 827987168133196994637427)
    ·
      refine ⟨1241980752199795491956141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827987168133196994637427 1241980752199795491956141)
      ·
        refine ⟨465742782074923309483553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1241980752199795491956141 465742782074923309483553)
        ·
          refine ⟨349307086556192482112665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465742782074923309483553 349307086556192482112665)
          ·
            refine ⟨261980314917144361584499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349307086556192482112665 261980314917144361584499)
            ·
              refine ⟨392970472375716542376749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261980314917144361584499 392970472375716542376749)
              ·
                refine ⟨147363927140893703391281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392970472375716542376749 147363927140893703391281)
                ·
                  refine ⟨110522945355670277543461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147363927140893703391281 110522945355670277543461)
                  ·
                    refine ⟨20723052254188177039399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110522945355670277543461 20723052254188177039399)
                    ·
                      rfl

theorem cell23_121074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_121074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121074 prefixEnd_121074 := by exact prefixLift 121074
  have htrace : WordTrace (prefixWord ++ tailWord_121074) baseStart_121074 baseEnd_121074 := by
    simpa [prefixWord, tailWord_121074, baseEnd_121074] using wordTrace_append hprefix tailTrace_121074
  have hstable : (prefixWord ++ tailWord_121074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121074).length < 2 ^ (prefixWord ++ tailWord_121074).sum := by decide
  have hdescent : baseEnd_121074 < baseStart_121074 := by decide
  rcases family_descends (prefixWord ++ tailWord_121074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_121080 : Nat := 118140960795 + 121080 * 2 ^ 59
def prefixEnd_121080 : Nat := 4983230072969 + 3 ^ 40 * 121080 * 2
def baseEnd_121080 : Nat := 62172237646491507643169

theorem tailTrace_121080 : CollatzResearch.WordTrace tailWord_121080 prefixEnd_121080 62172237646491507643169 := by
  unfold tailWord_121080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208075200677656831392347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2944100267570209108523129 2208075200677656831392347)
  ·
    refine ⟨3312112801016485247088521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208075200677656831392347 3312112801016485247088521)
    ·
      refine ⟨2484084600762363935316391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3312112801016485247088521 2484084600762363935316391)
      ·
        refine ⟨3726126901143545902974587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484084600762363935316391 3726126901143545902974587)
        ·
          refine ⟨5589190351715318854461881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726126901143545902974587 5589190351715318854461881)
          ·
            refine ⟨4191892763786489140846411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5589190351715318854461881 4191892763786489140846411)
            ·
              refine ⟨6287839145679733711269617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191892763786489140846411 6287839145679733711269617)
              ·
                refine ⟨4715879359259800283452213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287839145679733711269617 4715879359259800283452213)
                ·
                  refine ⟨442113689930606276573645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715879359259800283452213 442113689930606276573645)
                  ·
                    refine ⟨165792633723977353715117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442113689930606276573645 165792633723977353715117)
                    ·
                      refine ⟨62172237646491507643169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165792633723977353715117 62172237646491507643169)
                      ·
                        rfl

theorem cell23_121080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_121080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121080 prefixEnd_121080 := by exact prefixLift 121080
  have htrace : WordTrace (prefixWord ++ tailWord_121080) baseStart_121080 baseEnd_121080 := by
    simpa [prefixWord, tailWord_121080, baseEnd_121080] using wordTrace_append hprefix tailTrace_121080
  have hstable : (prefixWord ++ tailWord_121080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121080).length < 2 ^ (prefixWord ++ tailWord_121080).sum := by decide
  have hdescent : baseEnd_121080 < baseStart_121080 := by decide
  rcases family_descends (prefixWord ++ tailWord_121080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121084 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_121084 : Nat := 118140960795 + 121084 * 2 ^ 59
def prefixEnd_121084 : Nat := 4983230072969 + 3 ^ 40 * 121084 * 2
def baseEnd_121084 : Nat := 62174291569109491993151

theorem tailTrace_121084 : CollatzResearch.WordTrace tailWord_121084 prefixEnd_121084 62174291569109491993151 := by
  unfold tailWord_121084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208148146670411172965153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2944197528893881563953537 2208148146670411172965153)
  ·
    refine ⟨1656111110002808379723865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2208148146670411172965153 1656111110002808379723865)
    ·
      refine ⟨1242083332502106284792899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656111110002808379723865 1242083332502106284792899)
      ·
        refine ⟨1863124998753159427189349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242083332502106284792899 1863124998753159427189349)
        ·
          refine ⟨349335937266217392598003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1863124998753159427189349 349335937266217392598003)
          ·
            refine ⟨524003905899326088897005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349335937266217392598003 524003905899326088897005)
            ·
              refine ⟨196501464712247283336377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524003905899326088897005 196501464712247283336377)
              ·
                refine ⟨147376098534185462502283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196501464712247283336377 147376098534185462502283)
                ·
                  refine ⟨221064147801278193753425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147376098534185462502283 221064147801278193753425)
                  ·
                    refine ⟨165798110850958645315069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221064147801278193753425 165798110850958645315069)
                    ·
                      refine ⟨62174291569109491993151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165798110850958645315069 62174291569109491993151)
                      ·
                        rfl

theorem cell23_121084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_121084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121084 prefixEnd_121084 := by exact prefixLift 121084
  have htrace : WordTrace (prefixWord ++ tailWord_121084) baseStart_121084 baseEnd_121084 := by
    simpa [prefixWord, tailWord_121084, baseEnd_121084] using wordTrace_append hprefix tailTrace_121084
  have hstable : (prefixWord ++ tailWord_121084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121084).length < 2 ^ (prefixWord ++ tailWord_121084).sum := by decide
  have hdescent : baseEnd_121084 < baseStart_121084 := by decide
  rcases family_descends (prefixWord ++ tailWord_121084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121097 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_121097 : Nat := 118140960795 + 121097 * 2 ^ 59
def prefixEnd_121097 : Nat := 4983230072969 + 3 ^ 40 * 121097 * 2
def baseEnd_121097 : Nat := 62180966817617941130591

theorem tailTrace_121097 : CollatzResearch.WordTrace tailWord_121097 prefixEnd_121097 62180966817617941130591 := by
  unfold tailWord_121097
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416770442293725566153545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2944513628195817044102363 4416770442293725566153545)
  ·
    refine ⟨3312577831720294174615159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4416770442293725566153545 3312577831720294174615159)
    ·
      refine ⟨4968866747580441261922739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312577831720294174615159 4968866747580441261922739)
      ·
        refine ⟨7453300121370661892884109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968866747580441261922739 7453300121370661892884109)
        ·
          refine ⟨2794987545513998209831541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7453300121370661892884109 2794987545513998209831541)
          ·
            refine ⟨262030082391937332171707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2794987545513998209831541 262030082391937332171707)
            ·
              refine ⟨393045123587905998257561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262030082391937332171707 393045123587905998257561)
              ·
                refine ⟨294783842690929498693171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393045123587905998257561 294783842690929498693171)
                ·
                  refine ⟨442175764036394248039757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294783842690929498693171 442175764036394248039757)
                  ·
                    refine ⟨165815911513647843014909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442175764036394248039757 165815911513647843014909)
                    ·
                      refine ⟨62180966817617941130591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165815911513647843014909 62180966817617941130591)
                      ·
                        rfl

theorem cell23_121097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_121097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121097 prefixEnd_121097 := by exact prefixLift 121097
  have htrace : WordTrace (prefixWord ++ tailWord_121097) baseStart_121097 baseEnd_121097 := by
    simpa [prefixWord, tailWord_121097, baseEnd_121097] using wordTrace_append hprefix tailTrace_121097
  have hstable : (prefixWord ++ tailWord_121097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121097).length < 2 ^ (prefixWord ++ tailWord_121097).sum := by decide
  have hdescent : baseEnd_121097 < baseStart_121097 := by decide
  rcases family_descends (prefixWord ++ tailWord_121097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121124 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_121124 : Nat := 118140960795 + 121124 * 2 ^ 59
def prefixEnd_121124 : Nat := 4983230072969 + 3 ^ 40 * 121124 * 2
def baseEnd_121124 : Nat := 62194830795289335492967

theorem tailTrace_121124 : CollatzResearch.WordTrace tailWord_121124 prefixEnd_121124 62194830795289335492967 := by
  unfold tailWord_121124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208877606597954588693213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2945170142130606118257617 2208877606597954588693213)
  ·
    refine ⟨828329102474232970759955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2208877606597954588693213 828329102474232970759955)
    ·
      refine ⟨1242493653711349456139933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828329102474232970759955 1242493653711349456139933)
      ·
        refine ⟨465935120141756046052475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1242493653711349456139933 465935120141756046052475)
        ·
          refine ⟨698902680212634069078713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465935120141756046052475 698902680212634069078713)
          ·
            refine ⟨524177010159475551809035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698902680212634069078713 524177010159475551809035)
            ·
              refine ⟨786265515239213327713553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524177010159475551809035 786265515239213327713553)
              ·
                refine ⟨589699136429409995785165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786265515239213327713553 589699136429409995785165)
                ·
                  refine ⟨221137176161028748419437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589699136429409995785165 221137176161028748419437)
                  ·
                    refine ⟨82926441060385780657289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221137176161028748419437 82926441060385780657289)
                    ·
                      refine ⟨62194830795289335492967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82926441060385780657289 62194830795289335492967)
                      ·
                        rfl

theorem cell23_121124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_121124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121124 prefixEnd_121124 := by exact prefixLift 121124
  have htrace : WordTrace (prefixWord ++ tailWord_121124) baseStart_121124 baseEnd_121124 := by
    simpa [prefixWord, tailWord_121124, baseEnd_121124] using wordTrace_append hprefix tailTrace_121124
  have hstable : (prefixWord ++ tailWord_121124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121124).length < 2 ^ (prefixWord ++ tailWord_121124).sum := by decide
  have hdescent : baseEnd_121124 < baseStart_121124 := by decide
  rcases family_descends (prefixWord ++ tailWord_121124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121182 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_121182 : Nat := 118140960795 + 121182 * 2 ^ 59
def prefixEnd_121182 : Nat := 4983230072969 + 3 ^ 40 * 121182 * 2
def baseEnd_121182 : Nat := 62224612673250108567701

theorem tailTrace_121182 : CollatzResearch.WordTrace tailWord_121182 prefixEnd_121182 62224612673250108567701 := by
  unfold tailWord_121182
  simp only [CollatzResearch.WordTrace]
  refine ⟨552483830873223135374725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2946580431323856721998533 552483830873223135374725)
  ·
    refine ⟨103590718288729337882761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 552483830873223135374725 103590718288729337882761)
    ·
      refine ⟨77693038716547003412071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103590718288729337882761 77693038716547003412071)
      ·
        refine ⟨116539558074820505118107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77693038716547003412071 116539558074820505118107)
        ·
          refine ⟨174809337112230757677161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116539558074820505118107 174809337112230757677161)
          ·
            refine ⟨131107002834173068257871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174809337112230757677161 131107002834173068257871)
            ·
              refine ⟨196660504251259602386807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131107002834173068257871 196660504251259602386807)
              ·
                refine ⟨294990756376889403580211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196660504251259602386807 294990756376889403580211)
                ·
                  refine ⟨442486134565334105370317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294990756376889403580211 442486134565334105370317)
                  ·
                    refine ⟨165932300462000289513869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442486134565334105370317 165932300462000289513869)
                    ·
                      refine ⟨62224612673250108567701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165932300462000289513869 62224612673250108567701)
                      ·
                        rfl

theorem cell23_121182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_121182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121182 prefixEnd_121182 := by exact prefixLift 121182
  have htrace : WordTrace (prefixWord ++ tailWord_121182) baseStart_121182 baseEnd_121182 := by
    simpa [prefixWord, tailWord_121182, baseEnd_121182] using wordTrace_append hprefix tailTrace_121182
  have hstable : (prefixWord ++ tailWord_121182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121182).length < 2 ^ (prefixWord ++ tailWord_121182).sum := by decide
  have hdescent : baseEnd_121182 < baseStart_121182 := by decide
  rcases family_descends (prefixWord ++ tailWord_121182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121187 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3]
def baseStart_121187 : Nat := 118140960795 + 121187 * 2 ^ 59
def prefixEnd_121187 : Nat := 4983230072969 + 3 ^ 40 * 121187 * 2
def baseEnd_121187 : Nat := 62227180076522589005177

theorem tailTrace_121187 : CollatzResearch.WordTrace tailWord_121187 prefixEnd_121187 62227180076522589005177 := by
  unfold tailWord_121187
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420053011967670936929815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2946702007978447291286543 4420053011967670936929815)
  ·
    refine ⟨6630079517951506405394723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4420053011967670936929815 6630079517951506405394723)
    ·
      refine ⟨9945119276927259608092085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630079517951506405394723 9945119276927259608092085)
      ·
        refine ⟨932354932211930588258633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9945119276927259608092085 932354932211930588258633)
        ·
          refine ⟨699266199158947941193975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932354932211930588258633 699266199158947941193975)
          ·
            refine ⟨1048899298738421911790963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699266199158947941193975 1048899298738421911790963)
            ·
              refine ⟨1573348948107632867686445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048899298738421911790963 1573348948107632867686445)
              ·
                refine ⟨590005855540362325382417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573348948107632867686445 590005855540362325382417)
                ·
                  refine ⟨442504391655271744036813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590005855540362325382417 442504391655271744036813)
                  ·
                    refine ⟨165939146870726904013805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442504391655271744036813 165939146870726904013805)
                    ·
                      refine ⟨62227180076522589005177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 165939146870726904013805 62227180076522589005177)
                      ·
                        rfl

theorem cell23_121187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_121187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121187 prefixEnd_121187 := by exact prefixLift 121187
  have htrace : WordTrace (prefixWord ++ tailWord_121187) baseStart_121187 baseEnd_121187 := by
    simpa [prefixWord, tailWord_121187, baseEnd_121187] using wordTrace_append hprefix tailTrace_121187
  have hstable : (prefixWord ++ tailWord_121187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121187).length < 2 ^ (prefixWord ++ tailWord_121187).sum := by decide
  have hdescent : baseEnd_121187 < baseStart_121187 := by decide
  rcases family_descends (prefixWord ++ tailWord_121187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121188 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_121188 : Nat := 118140960795 + 121188 * 2 ^ 59
def prefixEnd_121188 : Nat := 4983230072969 + 3 ^ 40 * 121188 * 2
def baseEnd_121188 : Nat := 62227693557177085092673

theorem tailTrace_121188 : CollatzResearch.WordTrace tailWord_121188 prefixEnd_121188 62227693557177085092673 := by
  unfold tailWord_121188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210044742482024053858109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2946726323309365405144145 2210044742482024053858109)
  ·
    refine ⟨828766778430759020196791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2210044742482024053858109 828766778430759020196791)
    ·
      refine ⟨1243150167646138530295187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828766778430759020196791 1243150167646138530295187)
      ·
        refine ⟨1864725251469207795442781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243150167646138530295187 1864725251469207795442781)
        ·
          refine ⟨699271969300952923291043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864725251469207795442781 699271969300952923291043)
          ·
            refine ⟨1048907953951429384936565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699271969300952923291043 1048907953951429384936565)
            ·
              refine ⟨98335120682946504837803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1048907953951429384936565 98335120682946504837803)
              ·
                refine ⟨147502681024419757256705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98335120682946504837803 147502681024419757256705)
                ·
                  refine ⟨110627010768314817942529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147502681024419757256705 110627010768314817942529)
                  ·
                    refine ⟨82970258076236113456897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110627010768314817942529 82970258076236113456897)
                    ·
                      refine ⟨62227693557177085092673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 82970258076236113456897 62227693557177085092673)
                      ·
                        rfl

theorem cell23_121188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_121188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121188 prefixEnd_121188 := by exact prefixLift 121188
  have htrace : WordTrace (prefixWord ++ tailWord_121188) baseStart_121188 baseEnd_121188 := by
    simpa [prefixWord, tailWord_121188, baseEnd_121188] using wordTrace_append hprefix tailTrace_121188
  have hstable : (prefixWord ++ tailWord_121188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121188).length < 2 ^ (prefixWord ++ tailWord_121188).sum := by decide
  have hdescent : baseEnd_121188 < baseStart_121188 := by decide
  rcases family_descends (prefixWord ++ tailWord_121188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121227 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4]
def baseStart_121227 : Nat := 118140960795 + 121227 * 2 ^ 59
def prefixEnd_121227 : Nat := 4983230072969 + 3 ^ 40 * 121227 * 2
def baseEnd_121227 : Nat := 62247719302702432504993

theorem tailTrace_121227 : CollatzResearch.WordTrace tailWord_121227 prefixEnd_121227 62247719302702432504993 := by
  unfold tailWord_121227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421511931822757768385935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2947674621215171845590623 4421511931822757768385935)
  ·
    refine ⟨6632267897734136652578903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421511931822757768385935 6632267897734136652578903)
    ·
      refine ⟨9948401846601204978868355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632267897734136652578903 9948401846601204978868355)
      ·
        refine ⟨14922602769901807468302533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948401846601204978868355 14922602769901807468302533)
        ·
          refine ⟨2797988019356588900306725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14922602769901807468302533 2797988019356588900306725)
          ·
            refine ⟨524622753629360418807511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2797988019356588900306725 524622753629360418807511)
            ·
              refine ⟨786934130444040628211267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524622753629360418807511 786934130444040628211267)
              ·
                refine ⟨1180401195666060942316901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786934130444040628211267 1180401195666060942316901)
                ·
                  refine ⟨221325224187386426684419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180401195666060942316901 221325224187386426684419)
                  ·
                    refine ⟨331987836281079640026629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221325224187386426684419 331987836281079640026629)
                    ·
                      refine ⟨62247719302702432504993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 331987836281079640026629 62247719302702432504993)
                      ·
                        rfl

theorem cell23_121227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_121227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121227 prefixEnd_121227 := by exact prefixLift 121227
  have htrace : WordTrace (prefixWord ++ tailWord_121227) baseStart_121227 baseEnd_121227 := by
    simpa [prefixWord, tailWord_121227, baseEnd_121227] using wordTrace_append hprefix tailTrace_121227
  have hstable : (prefixWord ++ tailWord_121227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121227).length < 2 ^ (prefixWord ++ tailWord_121227).sum := by decide
  have hdescent : baseEnd_121227 < baseStart_121227 := by decide
  rcases family_descends (prefixWord ++ tailWord_121227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121288 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 1, 4]
def baseStart_121288 : Nat := 118140960795 + 121288 * 2 ^ 59
def prefixEnd_121288 : Nat := 4983230072969 + 3 ^ 40 * 121288 * 2
def baseEnd_121288 : Nat := 20759680540875564614071

theorem tailTrace_121288 : CollatzResearch.WordTrace tailWord_121288 prefixEnd_121288 20759680540875564614071 := by
  unfold tailWord_121288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211868392300882593178259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2949157856401176790904345 2211868392300882593178259)
  ·
    refine ⟨3317802588451323889767389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211868392300882593178259 3317802588451323889767389)
    ·
      refine ⟨1244175970669246458662771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3317802588451323889767389 1244175970669246458662771)
      ·
        refine ⟨1866263956003869687994157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244175970669246458662771 1866263956003869687994157)
        ·
          refine ⟨699848983501451132997809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866263956003869687994157 699848983501451132997809)
          ·
            refine ⟨524886737626088349748357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699848983501451132997809 524886737626088349748357)
            ·
              refine ⟨98416263304891565577817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524886737626088349748357 98416263304891565577817)
              ·
                refine ⟨73812197478668674183363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98416263304891565577817 73812197478668674183363)
                ·
                  refine ⟨110718296218003011275045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73812197478668674183363 110718296218003011275045)
                  ·
                    refine ⟨20759680540875564614071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110718296218003011275045 20759680540875564614071)
                    ·
                      rfl

theorem cell23_121288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_121288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121288 prefixEnd_121288 := by exact prefixLift 121288
  have htrace : WordTrace (prefixWord ++ tailWord_121288) baseStart_121288 baseEnd_121288 := by
    simpa [prefixWord, tailWord_121288, baseEnd_121288] using wordTrace_append hprefix tailTrace_121288
  have hstable : (prefixWord ++ tailWord_121288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121288).length < 2 ^ (prefixWord ++ tailWord_121288).sum := by decide
  have hdescent : baseEnd_121288 < baseStart_121288 := by decide
  rcases family_descends (prefixWord ++ tailWord_121288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121304 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_121304 : Nat := 118140960795 + 121304 * 2 ^ 59
def prefixEnd_121304 : Nat := 4983230072969 + 3 ^ 40 * 121304 * 2
def baseEnd_121304 : Nat := 62287257313098631242139

theorem tailTrace_121304 : CollatzResearch.WordTrace tailWord_121304 prefixEnd_121304 62287257313098631242139 := by
  unfold tailWord_121304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212160176271899959469483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2949546901695866612625977 2212160176271899959469483)
  ·
    refine ⟨3318240264407849939204225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212160176271899959469483 3318240264407849939204225)
    ·
      refine ⟨2488680198305887454403169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3318240264407849939204225 2488680198305887454403169)
      ·
        refine ⟨1866510148729415590802377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488680198305887454403169 1866510148729415590802377)
        ·
          refine ⟨1399882611547061693101783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866510148729415590802377 1399882611547061693101783)
          ·
            refine ⟨2099823917320592539652675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399882611547061693101783 2099823917320592539652675)
            ·
              refine ⟨3149735875980888809479013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099823917320592539652675 3149735875980888809479013)
              ·
                refine ⟨590575476746416651777315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3149735875980888809479013 590575476746416651777315)
                ·
                  refine ⟨885863215119624977665973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590575476746416651777315 885863215119624977665973)
                  ·
                    refine ⟨83049676417464841656185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 885863215119624977665973 83049676417464841656185)
                    ·
                      refine ⟨62287257313098631242139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83049676417464841656185 62287257313098631242139)
                      ·
                        rfl

theorem cell23_121304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_121304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121304 prefixEnd_121304 := by exact prefixLift 121304
  have htrace : WordTrace (prefixWord ++ tailWord_121304) baseStart_121304 baseEnd_121304 := by
    simpa [prefixWord, tailWord_121304, baseEnd_121304] using wordTrace_append hprefix tailTrace_121304
  have hstable : (prefixWord ++ tailWord_121304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121304).length < 2 ^ (prefixWord ++ tailWord_121304).sum := by decide
  have hdescent : baseEnd_121304 < baseStart_121304 := by decide
  rcases family_descends (prefixWord ++ tailWord_121304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121311 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_121311 : Nat := 118140960795 + 121311 * 2 ^ 59
def prefixEnd_121311 : Nat := 4983230072969 + 3 ^ 40 * 121311 * 2
def baseEnd_121311 : Nat := 62290851677680103854607

theorem tailTrace_121311 : CollatzResearch.WordTrace tailWord_121311 prefixEnd_121311 62290851677680103854607 := by
  unfold tailWord_121311
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424575663518440114443787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949717109012293409629191 4424575663518440114443787)
  ·
    refine ⟨6636863495277660171665681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424575663518440114443787 6636863495277660171665681)
    ·
      refine ⟨4977647621458245128749261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6636863495277660171665681 4977647621458245128749261)
      ·
        refine ⟨1866617858046841923280973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4977647621458245128749261 1866617858046841923280973)
        ·
          refine ⟨699981696767565721230365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866617858046841923280973 699981696767565721230365)
          ·
            refine ⟨262493136287837145461387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699981696767565721230365 262493136287837145461387)
            ·
              refine ⟨393739704431755718192081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262493136287837145461387 393739704431755718192081)
              ·
                refine ⟨295304778323816788644061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393739704431755718192081 295304778323816788644061)
                ·
                  refine ⟨110739291871431295741523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295304778323816788644061 110739291871431295741523)
                  ·
                    refine ⟨166108937807146943612285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110739291871431295741523 166108937807146943612285)
                    ·
                      refine ⟨62290851677680103854607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166108937807146943612285 62290851677680103854607)
                      ·
                        rfl

theorem cell23_121311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_121311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121311 prefixEnd_121311 := by exact prefixLift 121311
  have htrace : WordTrace (prefixWord ++ tailWord_121311) baseStart_121311 baseEnd_121311 := by
    simpa [prefixWord, tailWord_121311, baseEnd_121311] using wordTrace_append hprefix tailTrace_121311
  have hstable : (prefixWord ++ tailWord_121311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121311).length < 2 ^ (prefixWord ++ tailWord_121311).sum := by decide
  have hdescent : baseEnd_121311 < baseStart_121311 := by decide
  rcases family_descends (prefixWord ++ tailWord_121311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121328 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 1, 1, 3]
def baseStart_121328 : Nat := 118140960795 + 121328 * 2 ^ 59
def prefixEnd_121328 : Nat := 4983230072969 + 3 ^ 40 * 121328 * 2
def baseEnd_121328 : Nat := 62299580848806537342029

theorem tailTrace_121328 : CollatzResearch.WordTrace tailWord_121328 prefixEnd_121328 62299580848806537342029 := by
  unfold tailWord_121328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212597852228426008906319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2950130469637901345208425 2212597852228426008906319)
  ·
    refine ⟨3318896778342639013359479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212597852228426008906319 3318896778342639013359479)
    ·
      refine ⟨4978345167513958520039219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318896778342639013359479 4978345167513958520039219)
      ·
        refine ⟨7467517751270937780058829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978345167513958520039219 7467517751270937780058829)
        ·
          refine ⟨2800319156726601667522061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7467517751270937780058829 2800319156726601667522061)
          ·
            refine ⟨1050119683772475625320773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2800319156726601667522061 1050119683772475625320773)
            ·
              refine ⟨196897440707339179747645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050119683772475625320773 196897440707339179747645)
              ·
                refine ⟨73836540265252192405367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196897440707339179747645 73836540265252192405367)
                ·
                  refine ⟨110754810397878288608051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73836540265252192405367 110754810397878288608051)
                  ·
                    refine ⟨166132215596817432912077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110754810397878288608051 166132215596817432912077)
                    ·
                      refine ⟨62299580848806537342029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166132215596817432912077 62299580848806537342029)
                      ·
                        rfl

theorem cell23_121328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 1, 3].length) (baseStart_121328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121328 prefixEnd_121328 := by exact prefixLift 121328
  have htrace : WordTrace (prefixWord ++ tailWord_121328) baseStart_121328 baseEnd_121328 := by
    simpa [prefixWord, tailWord_121328, baseEnd_121328] using wordTrace_append hprefix tailTrace_121328
  have hstable : (prefixWord ++ tailWord_121328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121328).length < 2 ^ (prefixWord ++ tailWord_121328).sum := by decide
  have hdescent : baseEnd_121328 < baseStart_121328 := by decide
  rcases family_descends (prefixWord ++ tailWord_121328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121347 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_121347 : Nat := 118140960795 + 121347 * 2 ^ 59
def prefixEnd_121347 : Nat := 4983230072969 + 3 ^ 40 * 121347 * 2
def baseEnd_121347 : Nat := 62309336981241963004441

theorem tailTrace_121347 : CollatzResearch.WordTrace tailWord_121347 prefixEnd_121347 62309336981241963004441 := by
  unfold tailWord_121347
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425888691388018262754295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2950592460925345508502863 4425888691388018262754295)
  ·
    refine ⟨6638833037082027394131443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425888691388018262754295 6638833037082027394131443)
    ·
      refine ⟨9958249555623041091197165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638833037082027394131443 9958249555623041091197165)
      ·
        refine ⟨3734343583358640409198937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9958249555623041091197165 3734343583358640409198937)
        ·
          refine ⟨2800757687518980306899203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3734343583358640409198937 2800757687518980306899203)
          ·
            refine ⟨4201136531278470460348805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800757687518980306899203 4201136531278470460348805)
            ·
              refine ⟨787713099614713211315401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4201136531278470460348805 787713099614713211315401)
              ·
                refine ⟨590784824711034908486551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787713099614713211315401 590784824711034908486551)
                ·
                  refine ⟨886177237066552362729827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590784824711034908486551 886177237066552362729827)
                  ·
                    refine ⟨1329265855599828544094741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 886177237066552362729827 1329265855599828544094741)
                    ·
                      refine ⟨62309336981241963004441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1329265855599828544094741 62309336981241963004441)
                      ·
                        rfl

theorem cell23_121347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_121347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121347 prefixEnd_121347 := by exact prefixLift 121347
  have htrace : WordTrace (prefixWord ++ tailWord_121347) baseStart_121347 baseEnd_121347 := by
    simpa [prefixWord, tailWord_121347, baseEnd_121347] using wordTrace_append hprefix tailTrace_121347
  have hstable : (prefixWord ++ tailWord_121347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121347).length < 2 ^ (prefixWord ++ tailWord_121347).sum := by decide
  have hdescent : baseEnd_121347 < baseStart_121347 := by decide
  rcases family_descends (prefixWord ++ tailWord_121347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121354 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_121354 : Nat := 118140960795 + 121354 * 2 ^ 59
def prefixEnd_121354 : Nat := 4983230072969 + 3 ^ 40 * 121354 * 2
def baseEnd_121354 : Nat := 62312931345823435616909

theorem tailTrace_121354 : CollatzResearch.WordTrace tailWord_121354 prefixEnd_121354 62312931345823435616909 := by
  unfold tailWord_121354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106536000590664614564779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2950762668241772305506077 1106536000590664614564779)
  ·
    refine ⟨1659804000885996921847169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106536000590664614564779 1659804000885996921847169)
    ·
      refine ⟨1244853000664497691385377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1659804000885996921847169 1244853000664497691385377)
      ·
        refine ⟨933639750498373268539033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244853000664497691385377 933639750498373268539033)
        ·
          refine ⟨700229812873779951404275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933639750498373268539033 700229812873779951404275)
          ·
            refine ⟨1050344719310669927106413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700229812873779951404275 1050344719310669927106413)
            ·
              refine ⟨393879269741501222664905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050344719310669927106413 393879269741501222664905)
              ·
                refine ⟨295409452306125916998679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393879269741501222664905 295409452306125916998679)
                ·
                  refine ⟨443114178459188875498019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295409452306125916998679 443114178459188875498019)
                  ·
                    refine ⟨664671267688783313247029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443114178459188875498019 664671267688783313247029)
                    ·
                      refine ⟨62312931345823435616909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 664671267688783313247029 62312931345823435616909)
                      ·
                        rfl

theorem cell23_121354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_121354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121354 prefixEnd_121354 := by exact prefixLift 121354
  have htrace : WordTrace (prefixWord ++ tailWord_121354) baseStart_121354 baseEnd_121354 := by
    simpa [prefixWord, tailWord_121354, baseEnd_121354] using wordTrace_append hprefix tailTrace_121354
  have hstable : (prefixWord ++ tailWord_121354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121354).length < 2 ^ (prefixWord ++ tailWord_121354).sum := by decide
  have hdescent : baseEnd_121354 < baseStart_121354 := by decide
  rcases family_descends (prefixWord ++ tailWord_121354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121368 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_121368 : Nat := 118140960795 + 121368 * 2 ^ 59
def prefixEnd_121368 : Nat := 4983230072969 + 3 ^ 40 * 121368 * 2
def baseEnd_121368 : Nat := 62320120074986380841845

theorem tailTrace_121368 : CollatzResearch.WordTrace tailWord_121368 prefixEnd_121368 62320120074986380841845 := by
  unfold tailWord_121368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213327312155969424634379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2951103082874625899512505 2213327312155969424634379)
  ·
    refine ⟨3319990968233954136951569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213327312155969424634379 3319990968233954136951569)
    ·
      refine ⟨2489993226175465602713677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319990968233954136951569 2489993226175465602713677)
      ·
        refine ⟨933747459815799601017629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2489993226175465602713677 933747459815799601017629)
        ·
          refine ⟨350155297430924850381611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933747459815799601017629 350155297430924850381611)
          ·
            refine ⟨525232946146387275572417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350155297430924850381611 525232946146387275572417)
            ·
              refine ⟨393924709609790456679313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525232946146387275572417 393924709609790456679313)
              ·
                refine ⟨295443532207342842509485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393924709609790456679313 295443532207342842509485)
                ·
                  refine ⟨110791324577753565941057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295443532207342842509485 110791324577753565941057)
                  ·
                    refine ⟨83093493433315174455793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110791324577753565941057 83093493433315174455793)
                    ·
                      refine ⟨62320120074986380841845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83093493433315174455793 62320120074986380841845)
                      ·
                        rfl

theorem cell23_121368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_121368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121368 prefixEnd_121368 := by exact prefixLift 121368
  have htrace : WordTrace (prefixWord ++ tailWord_121368) baseStart_121368 baseEnd_121368 := by
    simpa [prefixWord, tailWord_121368, baseEnd_121368] using wordTrace_append hprefix tailTrace_121368
  have hstable : (prefixWord ++ tailWord_121368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121368).length < 2 ^ (prefixWord ++ tailWord_121368).sum := by decide
  have hdescent : baseEnd_121368 < baseStart_121368 := by decide
  rcases family_descends (prefixWord ++ tailWord_121368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121401 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_121401 : Nat := 118140960795 + 121401 * 2 ^ 59
def prefixEnd_121401 : Nat := 4983230072969 + 3 ^ 40 * 121401 * 2
def baseEnd_121401 : Nat := 62337064936584751729193

theorem tailTrace_121401 : CollatzResearch.WordTrace tailWord_121401 prefixEnd_121401 62337064936584751729193 := by
  unfold tailWord_121401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427858233192385485220057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2951905488794923656813371 4427858233192385485220057)
  ·
    refine ⟨3320893674894289113915043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4427858233192385485220057 3320893674894289113915043)
    ·
      refine ⟨4981340512341433670872565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320893674894289113915043 4981340512341433670872565)
      ·
        refine ⟨467000673032009406644303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4981340512341433670872565 467000673032009406644303)
        ·
          refine ⟨700501009548014109966455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467000673032009406644303 700501009548014109966455)
          ·
            refine ⟨1050751514322021164949683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700501009548014109966455 1050751514322021164949683)
            ·
              refine ⟨1576127271483031747424525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050751514322021164949683 1576127271483031747424525)
              ·
                refine ⟨591047726806136905284197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576127271483031747424525 591047726806136905284197)
                ·
                  refine ⟨110821448776150669740787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591047726806136905284197 110821448776150669740787)
                  ·
                    refine ⟨166232173164226004611181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110821448776150669740787 166232173164226004611181)
                    ·
                      refine ⟨62337064936584751729193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166232173164226004611181 62337064936584751729193)
                      ·
                        rfl

theorem cell23_121401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_121401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121401 prefixEnd_121401 := by exact prefixLift 121401
  have htrace : WordTrace (prefixWord ++ tailWord_121401) baseStart_121401 baseEnd_121401 := by
    simpa [prefixWord, tailWord_121401, baseEnd_121401] using wordTrace_append hprefix tailTrace_121401
  have hstable : (prefixWord ++ tailWord_121401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121401).length < 2 ^ (prefixWord ++ tailWord_121401).sum := by decide
  have hdescent : baseEnd_121401 < baseStart_121401 := by decide
  rcases family_descends (prefixWord ++ tailWord_121401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121402 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_121402 : Nat := 118140960795 + 121402 * 2 ^ 59
def prefixEnd_121402 : Nat := 4983230072969 + 3 ^ 40 * 121402 * 2
def baseEnd_121402 : Nat := 62337578417239247816689

theorem tailTrace_121402 : CollatzResearch.WordTrace tailWord_121402 prefixEnd_121402 62337578417239247816689 := by
  unfold tailWord_121402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106973676547190664001615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2951929804125841770670973 1106973676547190664001615)
  ·
    refine ⟨1660460514820785996002423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106973676547190664001615 1660460514820785996002423)
    ·
      refine ⟨2490690772231178994003635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660460514820785996002423 2490690772231178994003635)
      ·
        refine ⟨3736036158346768491005453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490690772231178994003635 3736036158346768491005453)
        ·
          refine ⟨1401013559380038184127045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3736036158346768491005453 1401013559380038184127045)
          ·
            refine ⟨262690042383757159523821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1401013559380038184127045 262690042383757159523821)
            ·
              refine ⟨98508765893908934821433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262690042383757159523821 98508765893908934821433)
              ·
                refine ⟨73881574420431701116075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98508765893908934821433 73881574420431701116075)
                ·
                  refine ⟨110822361630647551674113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73881574420431701116075 110822361630647551674113)
                  ·
                    refine ⟨83116771222985663755585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110822361630647551674113 83116771222985663755585)
                    ·
                      refine ⟨62337578417239247816689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83116771222985663755585 62337578417239247816689)
                      ·
                        rfl

theorem cell23_121402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_121402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121402 prefixEnd_121402 := by exact prefixLift 121402
  have htrace : WordTrace (prefixWord ++ tailWord_121402) baseStart_121402 baseEnd_121402 := by
    simpa [prefixWord, tailWord_121402, baseEnd_121402] using wordTrace_append hprefix tailTrace_121402
  have hstable : (prefixWord ++ tailWord_121402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121402).length < 2 ^ (prefixWord ++ tailWord_121402).sum := by decide
  have hdescent : baseEnd_121402 < baseStart_121402 := by decide
  rcases family_descends (prefixWord ++ tailWord_121402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121412 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_121412 : Nat := 118140960795 + 121412 * 2 ^ 59
def prefixEnd_121412 : Nat := 4983230072969 + 3 ^ 40 * 121412 * 2
def baseEnd_121412 : Nat := 20780904407928069563881

theorem tailTrace_121412 : CollatzResearch.WordTrace tailWord_121412 prefixEnd_121412 20780904407928069563881 := by
  unfold tailWord_121412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214129718076267181935245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2952172957435022909246993 2214129718076267181935245)
  ·
    refine ⟨830298644278600193225717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2214129718076267181935245 830298644278600193225717)
    ·
      refine ⟨77840497901118768114911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 830298644278600193225717 77840497901118768114911)
      ·
        refine ⟨116760746851678152172367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77840497901118768114911 116760746851678152172367)
        ·
          refine ⟨175141120277517228258551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116760746851678152172367 175141120277517228258551)
          ·
            refine ⟨262711680416275842387827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175141120277517228258551 262711680416275842387827)
            ·
              refine ⟨394067520624413763581741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262711680416275842387827 394067520624413763581741)
              ·
                refine ⟨147775320234155161343153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394067520624413763581741 147775320234155161343153)
                ·
                  refine ⟨110831490175616371007365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147775320234155161343153 110831490175616371007365)
                  ·
                    refine ⟨20780904407928069563881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110831490175616371007365 20780904407928069563881)
                    ·
                      rfl

theorem cell23_121412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_121412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121412 prefixEnd_121412 := by exact prefixLift 121412
  have htrace : WordTrace (prefixWord ++ tailWord_121412) baseStart_121412 baseEnd_121412 := by
    simpa [prefixWord, tailWord_121412, baseEnd_121412] using wordTrace_append hprefix tailTrace_121412
  have hstable : (prefixWord ++ tailWord_121412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121412).length < 2 ^ (prefixWord ++ tailWord_121412).sum := by decide
  have hdescent : baseEnd_121412 < baseStart_121412 := by decide
  rcases family_descends (prefixWord ++ tailWord_121412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121418 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_121418 : Nat := 118140960795 + 121418 * 2 ^ 59
def prefixEnd_121418 : Nat := 4983230072969 + 3 ^ 40 * 121418 * 2
def baseEnd_121418 : Nat := 62345794107711185216615

theorem tailTrace_121418 : CollatzResearch.WordTrace tailWord_121418 prefixEnd_121418 62345794107711185216615 := by
  unfold tailWord_121418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107119568532699347147227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2952318849420531592392605 1107119568532699347147227)
  ·
    refine ⟨1660679352799049020720841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107119568532699347147227 1660679352799049020720841)
    ·
      refine ⟨1245509514599286765540631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660679352799049020720841 1245509514599286765540631)
      ·
        refine ⟨1868264271898930148310947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245509514599286765540631 1868264271898930148310947)
        ·
          refine ⟨2802396407848395222466421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868264271898930148310947 2802396407848395222466421)
          ·
            refine ⟨262724663235787052106227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2802396407848395222466421 262724663235787052106227)
            ·
              refine ⟨394086994853680578159341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262724663235787052106227 394086994853680578159341)
              ·
                refine ⟨147782623070130216809753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394086994853680578159341 147782623070130216809753)
                ·
                  refine ⟨110836967302597662607315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147782623070130216809753 110836967302597662607315)
                  ·
                    refine ⟨166255450953896493910973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110836967302597662607315 166255450953896493910973)
                    ·
                      refine ⟨62345794107711185216615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166255450953896493910973 62345794107711185216615)
                      ·
                        rfl

theorem cell23_121418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_121418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121418 prefixEnd_121418 := by exact prefixLift 121418
  have htrace : WordTrace (prefixWord ++ tailWord_121418) baseStart_121418 baseEnd_121418 := by
    simpa [prefixWord, tailWord_121418, baseEnd_121418] using wordTrace_append hprefix tailTrace_121418
  have hstable : (prefixWord ++ tailWord_121418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121418).length < 2 ^ (prefixWord ++ tailWord_121418).sum := by decide
  have hdescent : baseEnd_121418 < baseStart_121418 := by decide
  rcases family_descends (prefixWord ++ tailWord_121418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121428 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_121428 : Nat := 118140960795 + 121428 * 2 ^ 59
def prefixEnd_121428 : Nat := 4983230072969 + 3 ^ 40 * 121428 * 2
def baseEnd_121428 : Nat := 62350928914256146091569

theorem tailTrace_121428 : CollatzResearch.WordTrace tailWord_121428 prefixEnd_121428 62350928914256146091569 := by
  unfold tailWord_121428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214421502047284548226469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2952562002729712730968625 2214421502047284548226469)
  ·
    refine ⟨415204031633865852792463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2214421502047284548226469 415204031633865852792463)
    ·
      refine ⟨622806047450798779188695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415204031633865852792463 622806047450798779188695)
      ·
        refine ⟨934209071176198168783043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622806047450798779188695 934209071176198168783043)
        ·
          refine ⟨1401313606764297253174565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934209071176198168783043 1401313606764297253174565)
          ·
            refine ⟨262746301268305734970231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1401313606764297253174565 262746301268305734970231)
            ·
              refine ⟨394119451902458602455347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262746301268305734970231 394119451902458602455347)
              ·
                refine ⟨591179177853687903683021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394119451902458602455347 591179177853687903683021)
                ·
                  refine ⟨221692191695132963881133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591179177853687903683021 221692191695132963881133)
                  ·
                    refine ⟨83134571885674861455425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221692191695132963881133 83134571885674861455425)
                    ·
                      refine ⟨62350928914256146091569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83134571885674861455425 62350928914256146091569)
                      ·
                        rfl

theorem cell23_121428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_121428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121428 prefixEnd_121428 := by exact prefixLift 121428
  have htrace : WordTrace (prefixWord ++ tailWord_121428) baseStart_121428 baseEnd_121428 := by
    simpa [prefixWord, tailWord_121428, baseEnd_121428] using wordTrace_append hprefix tailTrace_121428
  have hstable : (prefixWord ++ tailWord_121428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121428).length < 2 ^ (prefixWord ++ tailWord_121428).sum := by decide
  have hdescent : baseEnd_121428 < baseStart_121428 := by decide
  rcases family_descends (prefixWord ++ tailWord_121428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121441 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_121441 : Nat := 118140960795 + 121441 * 2 ^ 59
def prefixEnd_121441 : Nat := 4983230072969 + 3 ^ 40 * 121441 * 2
def baseEnd_121441 : Nat := 62357604162764595229009

theorem tailTrace_121441 : CollatzResearch.WordTrace tailWord_121441 prefixEnd_121441 62357604162764595229009 := by
  unfold tailWord_121441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429317153047472316676177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2952878102031648211117451 4429317153047472316676177)
  ·
    refine ⟨3321987864785604237507133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4429317153047472316676177 3321987864785604237507133)
    ·
      refine ⟨1245745449294601589065175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3321987864785604237507133 1245745449294601589065175)
      ·
        refine ⟨1868618173941902383597763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245745449294601589065175 1868618173941902383597763)
        ·
          refine ⟨2802927260912853575396645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868618173941902383597763 2802927260912853575396645)
          ·
            refine ⟨525548861421160045386871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2802927260912853575396645 525548861421160045386871)
            ·
              refine ⟨788323292131740068080307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525548861421160045386871 788323292131740068080307)
              ·
                refine ⟨1182484938197610102120461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788323292131740068080307 1182484938197610102120461)
                ·
                  refine ⟨443431851824103788295173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182484938197610102120461 443431851824103788295173)
                  ·
                    refine ⟨83143472217019460305345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443431851824103788295173 83143472217019460305345)
                    ·
                      refine ⟨62357604162764595229009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83143472217019460305345 62357604162764595229009)
                      ·
                        rfl

theorem cell23_121441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_121441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121441 prefixEnd_121441 := by exact prefixLift 121441
  have htrace : WordTrace (prefixWord ++ tailWord_121441) baseStart_121441 baseEnd_121441 := by
    simpa [prefixWord, tailWord_121441, baseEnd_121441] using wordTrace_append hprefix tailTrace_121441
  have hstable : (prefixWord ++ tailWord_121441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121441).length < 2 ^ (prefixWord ++ tailWord_121441).sum := by decide
  have hdescent : baseEnd_121441 < baseStart_121441 := by decide
  rcases family_descends (prefixWord ++ tailWord_121441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121444 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_121444 : Nat := 118140960795 + 121444 * 2 ^ 59
def prefixEnd_121444 : Nat := 4983230072969 + 3 ^ 40 * 121444 * 2
def baseEnd_121444 : Nat := 62359144604728083491495

theorem tailTrace_121444 : CollatzResearch.WordTrace tailWord_121444 prefixEnd_121444 62359144604728083491495 := by
  unfold tailWord_121444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214713286018301914517693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2952951048024402552690257 2214713286018301914517693)
  ·
    refine ⟨830517482256863217944135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2214713286018301914517693 830517482256863217944135)
    ·
      refine ⟨1245776223385294826916203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830517482256863217944135 1245776223385294826916203)
      ·
        refine ⟨1868664335077942240374305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245776223385294826916203 1868664335077942240374305)
        ·
          refine ⟨1401498251308456680280729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868664335077942240374305 1401498251308456680280729)
          ·
            refine ⟨1051123688481342510210547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401498251308456680280729 1051123688481342510210547)
            ·
              refine ⟨1576685532722013765315821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051123688481342510210547 1576685532722013765315821)
              ·
                refine ⟨591257074770755161993433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576685532722013765315821 591257074770755161993433)
                ·
                  refine ⟨443442806078066371495075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591257074770755161993433 443442806078066371495075)
                  ·
                    refine ⟨665164209117099557242613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443442806078066371495075 665164209117099557242613)
                    ·
                      refine ⟨62359144604728083491495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 665164209117099557242613 62359144604728083491495)
                      ·
                        rfl

theorem cell23_121444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_121444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121444 prefixEnd_121444 := by exact prefixLift 121444
  have htrace : WordTrace (prefixWord ++ tailWord_121444) baseStart_121444 baseEnd_121444 := by
    simpa [prefixWord, tailWord_121444, baseEnd_121444] using wordTrace_append hprefix tailTrace_121444
  have hstable : (prefixWord ++ tailWord_121444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121444).length < 2 ^ (prefixWord ++ tailWord_121444).sum := by decide
  have hdescent : baseEnd_121444 < baseStart_121444 := by decide
  rcases family_descends (prefixWord ++ tailWord_121444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121526 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_121526 : Nat := 118140960795 + 121526 * 2 ^ 59
def prefixEnd_121526 : Nat := 4983230072969 + 3 ^ 40 * 121526 * 2
def baseEnd_121526 : Nat := 62401250018396762666119

theorem tailTrace_121526 : CollatzResearch.WordTrace tailWord_121526 prefixEnd_121526 62401250018396762666119 := by
  unfold tailWord_121526
  simp only [CollatzResearch.WordTrace]
  refine ⟨277026084858720739595027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2954944905159687889013621 277026084858720739595027)
  ·
    refine ⟨415539127288081109392541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277026084858720739595027 415539127288081109392541)
    ·
      refine ⟨155827172733030416022203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415539127288081109392541 155827172733030416022203)
      ·
        refine ⟨233740759099545624033305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155827172733030416022203 233740759099545624033305)
        ·
          refine ⟨175305569324659218024979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233740759099545624033305 175305569324659218024979)
          ·
            refine ⟨262958353986988827037469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175305569324659218024979 262958353986988827037469)
            ·
              refine ⟨98609382745120810139051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262958353986988827037469 98609382745120810139051)
              ·
                refine ⟨147914074117681215208577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98609382745120810139051 147914074117681215208577)
                ·
                  refine ⟨110935555588260911406433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147914074117681215208577 110935555588260911406433)
                  ·
                    refine ⟨83201666691195683554825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110935555588260911406433 83201666691195683554825)
                    ·
                      refine ⟨62401250018396762666119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83201666691195683554825 62401250018396762666119)
                      ·
                        rfl

theorem cell23_121526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_121526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121526 prefixEnd_121526 := by exact prefixLift 121526
  have htrace : WordTrace (prefixWord ++ tailWord_121526) baseStart_121526 baseEnd_121526 := by
    simpa [prefixWord, tailWord_121526, baseEnd_121526] using wordTrace_append hprefix tailTrace_121526
  have hstable : (prefixWord ++ tailWord_121526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121526).length < 2 ^ (prefixWord ++ tailWord_121526).sum := by decide
  have hdescent : baseEnd_121526 < baseStart_121526 := by decide
  rcases family_descends (prefixWord ++ tailWord_121526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121549 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 5]
def baseStart_121549 : Nat := 118140960795 + 121549 * 2 ^ 59
def prefixEnd_121549 : Nat := 4983230072969 + 3 ^ 40 * 121549 * 2
def baseEnd_121549 : Nat := 6934784452605574742057

theorem tailTrace_121549 : CollatzResearch.WordTrace tailWord_121549 prefixEnd_121549 6934784452605574742057 := by
  unfold tailWord_121549
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433256236656206761607701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2955504157770804507738467 4433256236656206761607701)
  ·
    refine ⟨207808886093259691950361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4433256236656206761607701 207808886093259691950361)
    ·
      refine ⟨155856664569944768962771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207808886093259691950361 155856664569944768962771)
      ·
        refine ⟨233784996854917153444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155856664569944768962771 233784996854917153444157)
        ·
          refine ⟨87669373820593932541559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233784996854917153444157 87669373820593932541559)
          ·
            refine ⟨131504060730890898812339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87669373820593932541559 131504060730890898812339)
            ·
              refine ⟨197256091096336348218509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131504060730890898812339 197256091096336348218509)
              ·
                refine ⟨73971034161126130581941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197256091096336348218509 73971034161126130581941)
                ·
                  refine ⟨6934784452605574742057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73971034161126130581941 6934784452605574742057)
                  ·
                    rfl

theorem cell23_121549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_121549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121549 prefixEnd_121549 := by exact prefixLift 121549
  have htrace : WordTrace (prefixWord ++ tailWord_121549) baseStart_121549 baseEnd_121549 := by
    simpa [prefixWord, tailWord_121549, baseEnd_121549] using wordTrace_append hprefix tailTrace_121549
  have hstable : (prefixWord ++ tailWord_121549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121549).length < 2 ^ (prefixWord ++ tailWord_121549).sum := by decide
  have hdescent : baseEnd_121549 < baseStart_121549 := by decide
  rcases family_descends (prefixWord ++ tailWord_121549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121571 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 8]
def baseStart_121571 : Nat := 118140960795 + 121571 * 2 ^ 59
def prefixEnd_121571 : Nat := 4983230072969 + 3 ^ 40 * 121571 * 2
def baseEnd_121571 : Nat := 6936039627538787400379

theorem tailTrace_121571 : CollatzResearch.WordTrace tailWord_121571 prefixEnd_121571 6936039627538787400379 := by
  unfold tailWord_121571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434058642576504518908567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2956039095051003012605711 4434058642576504518908567)
  ·
    refine ⟨6651087963864756778362851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434058642576504518908567 6651087963864756778362851)
    ·
      refine ⟨9976631945797135167544277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651087963864756778362851 9976631945797135167544277)
      ·
        refine ⟨233827311229620355489319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9976631945797135167544277 233827311229620355489319)
        ·
          refine ⟨350740966844430533233979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233827311229620355489319 350740966844430533233979)
          ·
            refine ⟨526111450266645799850969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350740966844430533233979 526111450266645799850969)
            ·
              refine ⟨394583587699984349888227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526111450266645799850969 394583587699984349888227)
              ·
                refine ⟨591875381549976524832341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394583587699984349888227 591875381549976524832341)
                ·
                  refine ⟨6936039627538787400379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 591875381549976524832341 6936039627538787400379)
                  ·
                    rfl

theorem cell23_121571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 8].length) (baseStart_121571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121571 prefixEnd_121571 := by exact prefixLift 121571
  have htrace : WordTrace (prefixWord ++ tailWord_121571) baseStart_121571 baseEnd_121571 := by
    simpa [prefixWord, tailWord_121571, baseEnd_121571] using wordTrace_append hprefix tailTrace_121571
  have hstable : (prefixWord ++ tailWord_121571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121571).length < 2 ^ (prefixWord ++ tailWord_121571).sum := by decide
  have hdescent : baseEnd_121571 < baseStart_121571 := by decide
  rcases family_descends (prefixWord ++ tailWord_121571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121615 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 1, 1, 3]
def baseStart_121615 : Nat := 118140960795 + 121615 * 2 ^ 59
def prefixEnd_121615 : Nat := 4983230072969 + 3 ^ 40 * 121615 * 2
def baseEnd_121615 : Nat := 62446949796646914453209

theorem tailTrace_121615 : CollatzResearch.WordTrace tailWord_121615 prefixEnd_121615 62446949796646914453209 := by
  unfold tailWord_121615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435663454417100033510299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2957108969611400022340199 4435663454417100033510299)
  ·
    refine ⟨6653495181625650050265449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435663454417100033510299 6653495181625650050265449)
    ·
      refine ⟨4990121386219237537699087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6653495181625650050265449 4990121386219237537699087)
      ·
        refine ⟨7485182079328856306548631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990121386219237537699087 7485182079328856306548631)
        ·
          refine ⟨11227773118993284459822947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485182079328856306548631 11227773118993284459822947)
          ·
            refine ⟨16841659678489926689734421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227773118993284459822947 16841659678489926689734421)
            ·
              refine ⟨789452797429215313581301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16841659678489926689734421 789452797429215313581301)
              ·
                refine ⟨74011199758988935648247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789452797429215313581301 74011199758988935648247)
                ·
                  refine ⟨111016799638483403472371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74011199758988935648247 111016799638483403472371)
                  ·
                    refine ⟨166525199457725105208557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111016799638483403472371 166525199457725105208557)
                    ·
                      refine ⟨62446949796646914453209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166525199457725105208557 62446949796646914453209)
                      ·
                        rfl

theorem cell23_121615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 1, 3].length) (baseStart_121615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121615 prefixEnd_121615 := by exact prefixLift 121615
  have htrace : WordTrace (prefixWord ++ tailWord_121615) baseStart_121615 baseEnd_121615 := by
    simpa [prefixWord, tailWord_121615, baseEnd_121615] using wordTrace_append hprefix tailTrace_121615
  have hstable : (prefixWord ++ tailWord_121615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121615).length < 2 ^ (prefixWord ++ tailWord_121615).sum := by decide
  have hdescent : baseEnd_121615 < baseStart_121615 := by decide
  rcases family_descends (prefixWord ++ tailWord_121615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121632 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 1, 1, 3]
def baseStart_121632 : Nat := 118140960795 + 121632 * 2 ^ 59
def prefixEnd_121632 : Nat := 4983230072969 + 3 ^ 40 * 121632 * 2
def baseEnd_121632 : Nat := 62455678967773347940631

theorem tailTrace_121632 : CollatzResearch.WordTrace tailWord_121632 prefixEnd_121632 62455678967773347940631 := by
  unfold tailWord_121632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218141747677755968439575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2957522330237007957919433 2218141747677755968439575)
  ·
    refine ⟨3327212621516633952659363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218141747677755968439575 3327212621516633952659363)
    ·
      refine ⟨4990818932274950928989045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327212621516633952659363 4990818932274950928989045)
      ·
        refine ⟨467889274900776649592723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4990818932274950928989045 467889274900776649592723)
        ·
          refine ⟨701833912351164974389085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467889274900776649592723 701833912351164974389085)
          ·
            refine ⟨263187717131686865395907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 701833912351164974389085 263187717131686865395907)
            ·
              refine ⟨394781575697530298093861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263187717131686865395907 394781575697530298093861)
              ·
                refine ⟨74021545443286930892599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394781575697530298093861 74021545443286930892599)
                ·
                  refine ⟨111032318164930396338899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74021545443286930892599 111032318164930396338899)
                  ·
                    refine ⟨166548477247395594508349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111032318164930396338899 166548477247395594508349)
                    ·
                      refine ⟨62455678967773347940631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166548477247395594508349 62455678967773347940631)
                      ·
                        rfl

theorem cell23_121632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_121632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121632 prefixEnd_121632 := by exact prefixLift 121632
  have htrace : WordTrace (prefixWord ++ tailWord_121632) baseStart_121632 baseEnd_121632 := by
    simpa [prefixWord, tailWord_121632, baseEnd_121632] using wordTrace_append hprefix tailTrace_121632
  have hstable : (prefixWord ++ tailWord_121632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121632).length < 2 ^ (prefixWord ++ tailWord_121632).sum := by decide
  have hdescent : baseEnd_121632 < baseStart_121632 := by decide
  rcases family_descends (prefixWord ++ tailWord_121632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121655 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_121655 : Nat := 118140960795 + 121655 * 2 ^ 59
def prefixEnd_121655 : Nat := 4983230072969 + 3 ^ 40 * 121655 * 2
def baseEnd_121655 : Nat := 62467489022826757953025

theorem tailTrace_121655 : CollatzResearch.WordTrace tailWord_121655 prefixEnd_121655 62467489022826757953025 := by
  unfold tailWord_121655
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437122374272186864966419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2958081582848124576644279 4437122374272186864966419)
  ·
    refine ⟨6655683561408280297449629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437122374272186864966419 6655683561408280297449629)
    ·
      refine ⟨2495881335528105111543611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6655683561408280297449629 2495881335528105111543611)
      ·
        refine ⟨3743822003292157667315417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495881335528105111543611 3743822003292157667315417)
        ·
          refine ⟨2807866502469118250486563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743822003292157667315417 2807866502469118250486563)
          ·
            refine ⟨4211799753703677375729845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807866502469118250486563 4211799753703677375729845)
            ·
              refine ⟨394856226909719753974673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4211799753703677375729845 394856226909719753974673)
              ·
                refine ⟨296142170182289815481005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394856226909719753974673 296142170182289815481005)
                ·
                  refine ⟨111053313818358680805377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296142170182289815481005 111053313818358680805377)
                  ·
                    refine ⟨83289985363769010604033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111053313818358680805377 83289985363769010604033)
                    ·
                      refine ⟨62467489022826757953025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83289985363769010604033 62467489022826757953025)
                      ·
                        rfl

theorem cell23_121655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_121655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121655 prefixEnd_121655 := by exact prefixLift 121655
  have htrace : WordTrace (prefixWord ++ tailWord_121655) baseStart_121655 baseEnd_121655 := by
    simpa [prefixWord, tailWord_121655, baseEnd_121655] using wordTrace_append hprefix tailTrace_121655
  have hstable : (prefixWord ++ tailWord_121655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121655).length < 2 ^ (prefixWord ++ tailWord_121655).sum := by decide
  have hdescent : baseEnd_121655 < baseStart_121655 := by decide
  rcases family_descends (prefixWord ++ tailWord_121655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121711 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_121711 : Nat := 118140960795 + 121711 * 2 ^ 59
def prefixEnd_121711 : Nat := 4983230072969 + 3 ^ 40 * 121711 * 2
def baseEnd_121711 : Nat := 62496243939478538852767

theorem tailTrace_121711 : CollatzResearch.WordTrace tailWord_121711 prefixEnd_121711 62496243939478538852767 := by
  unfold tailWord_121711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439164862069308429004987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2959443241379538952669991 4439164862069308429004987)
  ·
    refine ⟨6658747293103962643507481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439164862069308429004987 6658747293103962643507481)
    ·
      refine ⟨4994060469827971982630611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658747293103962643507481 4994060469827971982630611)
      ·
        refine ⟨7491090704741957973945917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994060469827971982630611 7491090704741957973945917)
        ·
          refine ⟨2809159014278234240229719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7491090704741957973945917 2809159014278234240229719)
          ·
            refine ⟨4213738521417351360344579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809159014278234240229719 4213738521417351360344579)
            ·
              refine ⟨6320607782126027040516869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213738521417351360344579 6320607782126027040516869)
              ·
                refine ⟨1185113959148630070096913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6320607782126027040516869 1185113959148630070096913)
                ·
                  refine ⟨888835469361472552572685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185113959148630070096913 888835469361472552572685)
                  ·
                    refine ⟨333313301010552207214757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888835469361472552572685 333313301010552207214757)
                    ·
                      refine ⟨62496243939478538852767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 333313301010552207214757 62496243939478538852767)
                      ·
                        rfl

theorem cell23_121711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_121711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121711 prefixEnd_121711 := by exact prefixLift 121711
  have htrace : WordTrace (prefixWord ++ tailWord_121711) baseStart_121711 baseEnd_121711 := by
    simpa [prefixWord, tailWord_121711, baseEnd_121711] using wordTrace_append hprefix tailTrace_121711
  have hstable : (prefixWord ++ tailWord_121711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121711).length < 2 ^ (prefixWord ++ tailWord_121711).sum := by decide
  have hdescent : baseEnd_121711 < baseStart_121711 := by decide
  rcases family_descends (prefixWord ++ tailWord_121711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121715 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 1, 3, 2]
def baseStart_121715 : Nat := 118140960795 + 121715 * 2 ^ 59
def prefixEnd_121715 : Nat := 4983230072969 + 3 ^ 40 * 121715 * 2
def baseEnd_121715 : Nat := 62498297862096523202749

theorem tailTrace_121715 : CollatzResearch.WordTrace tailWord_121715 prefixEnd_121715 62498297862096523202749 := by
  unfold tailWord_121715
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439310754054817112150599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2959540502703211408100399 4439310754054817112150599)
  ·
    refine ⟨6658966131082225668225899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439310754054817112150599 6658966131082225668225899)
    ·
      refine ⟨9988449196623338502338849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658966131082225668225899 9988449196623338502338849)
      ·
        refine ⟨7491336897467503876754137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9988449196623338502338849 7491336897467503876754137)
        ·
          refine ⟨5618502673100627907565603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7491336897467503876754137 5618502673100627907565603)
          ·
            refine ⟨8427754009650941861348405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618502673100627907565603 8427754009650941861348405)
            ·
              refine ⟨790101938404775799501413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8427754009650941861348405 790101938404775799501413)
              ·
                refine ⟨148144113450895462406515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790101938404775799501413 148144113450895462406515)
                ·
                  refine ⟨222216170176343193609773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148144113450895462406515 222216170176343193609773)
                  ·
                    refine ⟨83331063816128697603665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222216170176343193609773 83331063816128697603665)
                    ·
                      refine ⟨62498297862096523202749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83331063816128697603665 62498297862096523202749)
                      ·
                        rfl

theorem cell23_121715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3, 2].length) (baseStart_121715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121715 prefixEnd_121715 := by exact prefixLift 121715
  have htrace : WordTrace (prefixWord ++ tailWord_121715) baseStart_121715 baseEnd_121715 := by
    simpa [prefixWord, tailWord_121715, baseEnd_121715] using wordTrace_append hprefix tailTrace_121715
  have hstable : (prefixWord ++ tailWord_121715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121715).length < 2 ^ (prefixWord ++ tailWord_121715).sum := by decide
  have hdescent : baseEnd_121715 < baseStart_121715 := by decide
  rcases family_descends (prefixWord ++ tailWord_121715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121748 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_121748 : Nat := 118140960795 + 121748 * 2 ^ 59
def prefixEnd_121748 : Nat := 4983230072969 + 3 ^ 40 * 121748 * 2
def baseEnd_121748 : Nat := 62515242723694894090097

theorem tailTrace_121748 : CollatzResearch.WordTrace tailWord_121748 prefixEnd_121748 62515242723694894090097 := by
  unfold tailWord_121748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220257181467631874050949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2960342908623509165401265 2220257181467631874050949)
  ·
    refine ⟨416298221525180976384553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2220257181467631874050949 416298221525180976384553)
    ·
      refine ⟨312223666143885732288415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416298221525180976384553 312223666143885732288415)
      ·
        refine ⟨468335499215828598432623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312223666143885732288415 468335499215828598432623)
        ·
          refine ⟨702503248823742897648935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468335499215828598432623 702503248823742897648935)
          ·
            refine ⟨1053754873235614346473403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702503248823742897648935 1053754873235614346473403)
            ·
              refine ⟨1580632309853421519710105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053754873235614346473403 1580632309853421519710105)
              ·
                refine ⟨1185474232390066139782579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580632309853421519710105 1185474232390066139782579)
                ·
                  refine ⟨1778211348585099209673869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185474232390066139782579 1778211348585099209673869)
                  ·
                    refine ⟨666829255719412203627701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1778211348585099209673869 666829255719412203627701)
                    ·
                      refine ⟨62515242723694894090097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 666829255719412203627701 62515242723694894090097)
                      ·
                        rfl

theorem cell23_121748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_121748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121748 prefixEnd_121748 := by exact prefixLift 121748
  have htrace : WordTrace (prefixWord ++ tailWord_121748) baseStart_121748 baseEnd_121748 := by
    simpa [prefixWord, tailWord_121748, baseEnd_121748] using wordTrace_append hprefix tailTrace_121748
  have hstable : (prefixWord ++ tailWord_121748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121748).length < 2 ^ (prefixWord ++ tailWord_121748).sum := by decide
  have hdescent : baseEnd_121748 < baseStart_121748 := by decide
  rcases family_descends (prefixWord ++ tailWord_121748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121756 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_121756 : Nat := 118140960795 + 121756 * 2 ^ 59
def prefixEnd_121756 : Nat := 4983230072969 + 3 ^ 40 * 121756 * 2
def baseEnd_121756 : Nat := 62519350568930862790061

theorem tailTrace_121756 : CollatzResearch.WordTrace tailWord_121756 prefixEnd_121756 62519350568930862790061 := by
  unfold tailWord_121756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220403073453140557196561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2960537431270854076262081 2220403073453140557196561)
  ·
    refine ⟨1665302305089855417897421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2220403073453140557196561 1665302305089855417897421)
    ·
      refine ⟨624488364408695781711533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1665302305089855417897421 624488364408695781711533)
      ·
        refine ⟨234183136653260918141825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624488364408695781711533 234183136653260918141825)
        ·
          refine ⟨175637352489945688606369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234183136653260918141825 175637352489945688606369)
          ·
            refine ⟨131728014367459266454777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175637352489945688606369 131728014367459266454777)
            ·
              refine ⟨98796010775594449841083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131728014367459266454777 98796010775594449841083)
              ·
                refine ⟨148194016163391674761625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98796010775594449841083 148194016163391674761625)
                ·
                  refine ⟨111145512122543756071219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148194016163391674761625 111145512122543756071219)
                  ·
                    refine ⟨166718268183815634106829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111145512122543756071219 166718268183815634106829)
                    ·
                      refine ⟨62519350568930862790061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166718268183815634106829 62519350568930862790061)
                      ·
                        rfl

theorem cell23_121756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_121756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121756 prefixEnd_121756 := by exact prefixLift 121756
  have htrace : WordTrace (prefixWord ++ tailWord_121756) baseStart_121756 baseEnd_121756 := by
    simpa [prefixWord, tailWord_121756, baseEnd_121756] using wordTrace_append hprefix tailTrace_121756
  have hstable : (prefixWord ++ tailWord_121756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121756).length < 2 ^ (prefixWord ++ tailWord_121756).sum := by decide
  have hdescent : baseEnd_121756 < baseStart_121756 := by decide
  rcases family_descends (prefixWord ++ tailWord_121756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121778 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_121778 : Nat := 118140960795 + 121778 * 2 ^ 59
def prefixEnd_121778 : Nat := 4983230072969 + 3 ^ 40 * 121778 * 2
def baseEnd_121778 : Nat := 62530647143329776714959

theorem tailTrace_121778 : CollatzResearch.WordTrace tailWord_121778 prefixEnd_121778 62530647143329776714959 := by
  unfold tailWord_121778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110402138206644717923497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2961072368551052581129325 1110402138206644717923497)
  ·
    refine ⟨832801603654983538442623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1110402138206644717923497 832801603654983538442623)
    ·
      refine ⟨1249202405482475307663935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832801603654983538442623 1249202405482475307663935)
      ·
        refine ⟨1873803608223712961495903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249202405482475307663935 1873803608223712961495903)
        ·
          refine ⟨2810705412335569442243855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873803608223712961495903 2810705412335569442243855)
          ·
            refine ⟨4216058118503354163365783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810705412335569442243855 4216058118503354163365783)
            ·
              refine ⟨6324087177755031245048675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216058118503354163365783 6324087177755031245048675)
              ·
                refine ⟨9486130766632546867573013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324087177755031245048675 9486130766632546867573013)
                ·
                  refine ⟨444662379685900634417485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9486130766632546867573013 444662379685900634417485)
                  ·
                    refine ⟨166748392382212737906557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444662379685900634417485 166748392382212737906557)
                    ·
                      refine ⟨62530647143329776714959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 166748392382212737906557 62530647143329776714959)
                      ·
                        rfl

theorem cell23_121778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_121778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121778 prefixEnd_121778 := by exact prefixLift 121778
  have htrace : WordTrace (prefixWord ++ tailWord_121778) baseStart_121778 baseEnd_121778 := by
    simpa [prefixWord, tailWord_121778, baseEnd_121778] using wordTrace_append hprefix tailTrace_121778
  have hstable : (prefixWord ++ tailWord_121778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121778).length < 2 ^ (prefixWord ++ tailWord_121778).sum := by decide
  have hdescent : baseEnd_121778 < baseStart_121778 := by decide
  rcases family_descends (prefixWord ++ tailWord_121778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121801 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_121801 : Nat := 118140960795 + 121801 * 2 ^ 59
def prefixEnd_121801 : Nat := 4983230072969 + 3 ^ 40 * 121801 * 2
def baseEnd_121801 : Nat := 62542457198383186727353

theorem tailTrace_121801 : CollatzResearch.WordTrace tailWord_121801 prefixEnd_121801 62542457198383186727353 := by
  unfold tailWord_121801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442447431743253799781257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2961631621162169199854171 4442447431743253799781257)
  ·
    refine ⟨3331835573807440349835943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4442447431743253799781257 3331835573807440349835943)
    ·
      refine ⟨4997753360711160524753915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331835573807440349835943 4997753360711160524753915)
      ·
        refine ⟨7496630041066740787130873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4997753360711160524753915 7496630041066740787130873)
        ·
          refine ⟨5622472530800055590348155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7496630041066740787130873 5622472530800055590348155)
          ·
            refine ⟨8433708796200083385522233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622472530800055590348155 8433708796200083385522233)
            ·
              refine ⟨6325281597150062539141675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8433708796200083385522233 6325281597150062539141675)
              ·
                refine ⟨9487922395725093808712513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325281597150062539141675 9487922395725093808712513)
                ·
                  refine ⟨7115941796793820356534385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487922395725093808712513 7115941796793820356534385)
                  ·
                    refine ⟨5336956347595365267400789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7115941796793820356534385 5336956347595365267400789)
                    ·
                      refine ⟨62542457198383186727353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 5336956347595365267400789 62542457198383186727353)
                      ·
                        rfl

theorem cell23_121801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_121801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121801 prefixEnd_121801 := by exact prefixLift 121801
  have htrace : WordTrace (prefixWord ++ tailWord_121801) baseStart_121801 baseEnd_121801 := by
    simpa [prefixWord, tailWord_121801, baseEnd_121801] using wordTrace_append hprefix tailTrace_121801
  have hstable : (prefixWord ++ tailWord_121801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121801).length < 2 ^ (prefixWord ++ tailWord_121801).sum := by decide
  have hdescent : baseEnd_121801 < baseStart_121801 := by decide
  rcases family_descends (prefixWord ++ tailWord_121801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121905 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_121905 : Nat := 118140960795 + 121905 * 2 ^ 59
def prefixEnd_121905 : Nat := 4983230072969 + 3 ^ 40 * 121905 * 2
def baseEnd_121905 : Nat := 20865286395483593275625

theorem tailTrace_121905 : CollatzResearch.WordTrace tailWord_121905 prefixEnd_121905 20865286395483593275625 := by
  unfold tailWord_121905
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446240623366479561567169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2964160415577653041044779 4446240623366479561567169)
  ·
    refine ⟨3334680467524859671175377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446240623366479561567169 3334680467524859671175377)
    ·
      refine ⟨2501010350643644753381533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334680467524859671175377 2501010350643644753381533)
      ·
        refine ⟨937878881491366782518075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2501010350643644753381533 937878881491366782518075)
        ·
          refine ⟨1406818322237050173777113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937878881491366782518075 1406818322237050173777113)
          ·
            refine ⟨1055113741677787630332835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406818322237050173777113 1055113741677787630332835)
            ·
              refine ⟨1582670612516681445499253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055113741677787630332835 1582670612516681445499253)
              ·
                refine ⟨148375369923438885515555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582670612516681445499253 148375369923438885515555)
                ·
                  refine ⟨222563054885158328273333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148375369923438885515555 222563054885158328273333)
                  ·
                    refine ⟨20865286395483593275625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222563054885158328273333 20865286395483593275625)
                    ·
                      rfl

theorem cell23_121905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_121905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121905 prefixEnd_121905 := by exact prefixLift 121905
  have htrace : WordTrace (prefixWord ++ tailWord_121905) baseStart_121905 baseEnd_121905 := by
    simpa [prefixWord, tailWord_121905, baseEnd_121905] using wordTrace_append hprefix tailTrace_121905
  have hstable : (prefixWord ++ tailWord_121905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121905).length < 2 ^ (prefixWord ++ tailWord_121905).sum := by decide
  have hdescent : baseEnd_121905 < baseStart_121905 := by decide
  rcases family_descends (prefixWord ++ tailWord_121905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121912 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_121912 : Nat := 118140960795 + 121912 * 2 ^ 59
def prefixEnd_121912 : Nat := 4983230072969 + 3 ^ 40 * 121912 * 2
def baseEnd_121912 : Nat := 62599453551032252439343

theorem tailTrace_121912 : CollatzResearch.WordTrace tailWord_121912 prefixEnd_121912 62599453551032252439343 := by
  unfold tailWord_121912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223247967170559878535995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2964330622894079838047993 2223247967170559878535995)
  ·
    refine ⟨3334871950755839817803993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223247967170559878535995 3334871950755839817803993)
    ·
      refine ⟨2501153963066879863352995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334871950755839817803993 2501153963066879863352995)
      ·
        refine ⟨3751730944600319795029493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501153963066879863352995 3751730944600319795029493)
        ·
          refine ⟨351724776056279980784015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3751730944600319795029493 351724776056279980784015)
          ·
            refine ⟨527587164084419971176023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351724776056279980784015 527587164084419971176023)
            ·
              refine ⟨791380746126629956764035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527587164084419971176023 791380746126629956764035)
              ·
                refine ⟨1187071119189944935146053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791380746126629956764035 1187071119189944935146053)
                ·
                  refine ⟨222575834848114675339885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187071119189944935146053 222575834848114675339885)
                  ·
                    refine ⟨83465938068043003252457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222575834848114675339885 83465938068043003252457)
                    ·
                      refine ⟨62599453551032252439343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83465938068043003252457 62599453551032252439343)
                      ·
                        rfl

theorem cell23_121912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_121912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121912 prefixEnd_121912 := by exact prefixLift 121912
  have htrace : WordTrace (prefixWord ++ tailWord_121912) baseStart_121912 baseEnd_121912 := by
    simpa [prefixWord, tailWord_121912, baseEnd_121912] using wordTrace_append hprefix tailTrace_121912
  have hstable : (prefixWord ++ tailWord_121912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121912).length < 2 ^ (prefixWord ++ tailWord_121912).sum := by decide
  have hdescent : baseEnd_121912 < baseStart_121912 := by decide
  rcases family_descends (prefixWord ++ tailWord_121912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121926 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_121926 : Nat := 118140960795 + 121926 * 2 ^ 59
def prefixEnd_121926 : Nat := 4983230072969 + 3 ^ 40 * 121926 * 2
def baseEnd_121926 : Nat := 6956293586688355296031

theorem tailTrace_121926 : CollatzResearch.WordTrace tailWord_121926 prefixEnd_121926 6956293586688355296031 := by
  unfold tailWord_121926
  simp only [CollatzResearch.WordTrace]
  refine ⟨138968954884075004627551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2964671037526933432054421 138968954884075004627551)
  ·
    refine ⟨208453432326112506941327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138968954884075004627551 208453432326112506941327)
    ·
      refine ⟨312680148489168760411991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208453432326112506941327 312680148489168760411991)
      ·
        refine ⟨469020222733753140617987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312680148489168760411991 469020222733753140617987)
        ·
          refine ⟨703530334100629710926981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469020222733753140617987 703530334100629710926981)
          ·
            refine ⟨131911937643868070798809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 703530334100629710926981 131911937643868070798809)
            ·
              refine ⟨98933953232901053099107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131911937643868070798809 98933953232901053099107)
              ·
                refine ⟨148400929849351579648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98933953232901053099107 148400929849351579648661)
                ·
                  refine ⟨6956293586688355296031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148400929849351579648661 6956293586688355296031)
                  ·
                    rfl

theorem cell23_121926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_121926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121926 prefixEnd_121926 := by exact prefixLift 121926
  have htrace : WordTrace (prefixWord ++ tailWord_121926) baseStart_121926 baseEnd_121926 := by
    simpa [prefixWord, tailWord_121926, baseEnd_121926] using wordTrace_append hprefix tailTrace_121926
  have hstable : (prefixWord ++ tailWord_121926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121926).length < 2 ^ (prefixWord ++ tailWord_121926).sum := by decide
  have hdescent : baseEnd_121926 < baseStart_121926 := by decide
  rcases family_descends (prefixWord ++ tailWord_121926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121959 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_121959 : Nat := 118140960795 + 121959 * 2 ^ 59
def prefixEnd_121959 : Nat := 4983230072969 + 3 ^ 40 * 121959 * 2
def baseEnd_121959 : Nat := 62623587141793568551627

theorem tailTrace_121959 : CollatzResearch.WordTrace tailWord_121959 prefixEnd_121959 62623587141793568551627 := by
  unfold tailWord_121959
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448210165170846784032931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2965473443447231189355287 4448210165170846784032931)
  ·
    refine ⟨6672315247756270176049397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4448210165170846784032931 6672315247756270176049397)
    ·
      refine ⟨625529554477150329004631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6672315247756270176049397 625529554477150329004631)
      ·
        refine ⟨938294331715725493506947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625529554477150329004631 938294331715725493506947)
        ·
          refine ⟨1407441497573588240260421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938294331715725493506947 1407441497573588240260421)
          ·
            refine ⟨263895280795047795048829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1407441497573588240260421 263895280795047795048829)
            ·
              refine ⟨98960730298142923143311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263895280795047795048829 98960730298142923143311)
              ·
                refine ⟨148441095447214384714967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98960730298142923143311 148441095447214384714967)
                ·
                  refine ⟨222661643170821577072451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148441095447214384714967 222661643170821577072451)
                  ·
                    refine ⟨333992464756232365608677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222661643170821577072451 333992464756232365608677)
                    ·
                      refine ⟨62623587141793568551627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 333992464756232365608677 62623587141793568551627)
                      ·
                        rfl

theorem cell23_121959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_121959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121959 prefixEnd_121959 := by exact prefixLift 121959
  have htrace : WordTrace (prefixWord ++ tailWord_121959) baseStart_121959 baseEnd_121959 := by
    simpa [prefixWord, tailWord_121959, baseEnd_121959] using wordTrace_append hprefix tailTrace_121959
  have hstable : (prefixWord ++ tailWord_121959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121959).length < 2 ^ (prefixWord ++ tailWord_121959).sum := by decide
  have hdescent : baseEnd_121959 < baseStart_121959 := by decide
  rcases family_descends (prefixWord ++ tailWord_121959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121962 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_121962 : Nat := 118140960795 + 121962 * 2 ^ 59
def prefixEnd_121962 : Nat := 4983230072969 + 3 ^ 40 * 121962 * 2
def baseEnd_121962 : Nat := 62625127583757056814113

theorem tailTrace_121962 : CollatzResearch.WordTrace tailWord_121962 prefixEnd_121962 62625127583757056814113 := by
  unfold tailWord_121962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112079896039994574098035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2965546389439985530928093 1112079896039994574098035)
  ·
    refine ⟨1668119844059991861147053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112079896039994574098035 1668119844059991861147053)
    ·
      refine ⟨625544941522496947930145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1668119844059991861147053 625544941522496947930145)
      ·
        refine ⟨469158706141872710947609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625544941522496947930145 469158706141872710947609)
        ·
          refine ⟨351869029606404533210707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469158706141872710947609 351869029606404533210707)
          ·
            refine ⟨527803544409606799816061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351869029606404533210707 527803544409606799816061)
            ·
              refine ⟨197926329153602549931023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527803544409606799816061 197926329153602549931023)
              ·
                refine ⟨296889493730403824896535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197926329153602549931023 296889493730403824896535)
                ·
                  refine ⟨445334240595605737344803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296889493730403824896535 445334240595605737344803)
                  ·
                    refine ⟨668001360893408606017205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445334240595605737344803 668001360893408606017205)
                    ·
                      refine ⟨62625127583757056814113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 668001360893408606017205 62625127583757056814113)
                      ·
                        rfl

theorem cell23_121962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_121962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121962 prefixEnd_121962 := by exact prefixLift 121962
  have htrace : WordTrace (prefixWord ++ tailWord_121962) baseStart_121962 baseEnd_121962 := by
    simpa [prefixWord, tailWord_121962, baseEnd_121962] using wordTrace_append hprefix tailTrace_121962
  have hstable : (prefixWord ++ tailWord_121962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121962).length < 2 ^ (prefixWord ++ tailWord_121962).sum := by decide
  have hdescent : baseEnd_121962 < baseStart_121962 := by decide
  rcases family_descends (prefixWord ++ tailWord_121962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121975 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_121975 : Nat := 118140960795 + 121975 * 2 ^ 59
def prefixEnd_121975 : Nat := 4983230072969 + 3 ^ 40 * 121975 * 2
def baseEnd_121975 : Nat := 62631802832265505951553

theorem tailTrace_121975 : CollatzResearch.WordTrace tailWord_121975 prefixEnd_121975 62631802832265505951553 := by
  unfold tailWord_121975
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448793733112881516615379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2965862488741921011076919 4448793733112881516615379)
  ·
    refine ⟨6673190599669322274923069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4448793733112881516615379 6673190599669322274923069)
    ·
      refine ⟨2502446474875995853096151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6673190599669322274923069 2502446474875995853096151)
      ·
        refine ⟨3753669712313993779644227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502446474875995853096151 3753669712313993779644227)
        ·
          refine ⟨5630504568470990669466341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753669712313993779644227 5630504568470990669466341)
          ·
            refine ⟨1055719606588310750524939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5630504568470990669466341 1055719606588310750524939)
            ·
              refine ⟨1583579409882466125787409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055719606588310750524939 1583579409882466125787409)
              ·
                refine ⟨1187684557411849594340557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583579409882466125787409 1187684557411849594340557)
                ·
                  refine ⟨445381709029443597877709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187684557411849594340557 445381709029443597877709)
                  ·
                    refine ⟨167018140886041349204141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445381709029443597877709 167018140886041349204141)
                    ·
                      refine ⟨62631802832265505951553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167018140886041349204141 62631802832265505951553)
                      ·
                        rfl

theorem cell23_121975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_121975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_121975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_121975 prefixEnd_121975 := by exact prefixLift 121975
  have htrace : WordTrace (prefixWord ++ tailWord_121975) baseStart_121975 baseEnd_121975 := by
    simpa [prefixWord, tailWord_121975, baseEnd_121975] using wordTrace_append hprefix tailTrace_121975
  have hstable : (prefixWord ++ tailWord_121975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121975).length < 2 ^ (prefixWord ++ tailWord_121975).sum := by decide
  have hdescent : baseEnd_121975 < baseStart_121975 := by decide
  rcases family_descends (prefixWord ++ tailWord_121975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122026 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_122026 : Nat := 118140960795 + 122026 * 2 ^ 59
def prefixEnd_122026 : Nat := 4983230072969 + 3 ^ 40 * 122026 * 2
def baseEnd_122026 : Nat := 62657990345644806413819

theorem tailTrace_122026 : CollatzResearch.WordTrace tailWord_122026 prefixEnd_122026 62657990345644806413819 := by
  unfold tailWord_122026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112663463982029306680483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2967102570618744817814621 1112663463982029306680483)
  ·
    refine ⟨1668995195973043960020725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112663463982029306680483 1668995195973043960020725)
    ·
      refine ⟨156468299622472871251943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1668995195973043960020725 156468299622472871251943)
      ·
        refine ⟨234702449433709306877915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156468299622472871251943 234702449433709306877915)
        ·
          refine ⟨352053674150563960316873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234702449433709306877915 352053674150563960316873)
          ·
            refine ⟨264040255612922970237655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352053674150563960316873 264040255612922970237655)
            ·
              refine ⟨396060383419384455356483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264040255612922970237655 396060383419384455356483)
              ·
                refine ⟨594090575129076683034725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396060383419384455356483 594090575129076683034725)
                ·
                  refine ⟨111391982836701878069011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594090575129076683034725 111391982836701878069011)
                  ·
                    refine ⟨167087974255052817103517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111391982836701878069011 167087974255052817103517)
                    ·
                      refine ⟨62657990345644806413819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167087974255052817103517 62657990345644806413819)
                      ·
                        rfl

theorem cell23_122026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_122026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122026 prefixEnd_122026 := by exact prefixLift 122026
  have htrace : WordTrace (prefixWord ++ tailWord_122026) baseStart_122026 baseEnd_122026 := by
    simpa [prefixWord, tailWord_122026, baseEnd_122026] using wordTrace_append hprefix tailTrace_122026
  have hstable : (prefixWord ++ tailWord_122026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122026).length < 2 ^ (prefixWord ++ tailWord_122026).sum := by decide
  have hdescent : baseEnd_122026 < baseStart_122026 := by decide
  rcases family_descends (prefixWord ++ tailWord_122026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122035 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3]
def baseStart_122035 : Nat := 118140960795 + 122035 * 2 ^ 59
def prefixEnd_122035 : Nat := 4983230072969 + 3 ^ 40 * 122035 * 2
def baseEnd_122035 : Nat := 62662611671535271201277

theorem tailTrace_122035 : CollatzResearch.WordTrace tailWord_122035 prefixEnd_122035 62662611671535271201277 := by
  unfold tailWord_122035
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450982112895511763799559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2967321408597007842533039 4450982112895511763799559)
  ·
    refine ⟨6676473169343267645699339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4450982112895511763799559 6676473169343267645699339)
    ·
      refine ⟨10014709754014901468549009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676473169343267645699339 10014709754014901468549009)
      ·
        refine ⟨7511032315511176101411757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10014709754014901468549009 7511032315511176101411757)
        ·
          refine ⟨2816637118316691038029409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7511032315511176101411757 2816637118316691038029409)
          ·
            refine ⟨2112477838737518278522057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816637118316691038029409 2112477838737518278522057)
            ·
              refine ⟨1584358379053138708891543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112477838737518278522057 1584358379053138708891543)
              ·
                refine ⟨2376537568579708063337315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584358379053138708891543 2376537568579708063337315)
                ·
                  refine ⟨3564806352869562095005973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376537568579708063337315 3564806352869562095005973)
                  ·
                    refine ⟨167100297790760723203405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3564806352869562095005973 167100297790760723203405)
                    ·
                      refine ⟨62662611671535271201277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167100297790760723203405 62662611671535271201277)
                      ·
                        rfl

theorem cell23_122035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_122035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122035 prefixEnd_122035 := by exact prefixLift 122035
  have htrace : WordTrace (prefixWord ++ tailWord_122035) baseStart_122035 baseEnd_122035 := by
    simpa [prefixWord, tailWord_122035, baseEnd_122035] using wordTrace_append hprefix tailTrace_122035
  have hstable : (prefixWord ++ tailWord_122035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122035).length < 2 ^ (prefixWord ++ tailWord_122035).sum := by decide
  have hdescent : baseEnd_122035 < baseStart_122035 := by decide
  rcases family_descends (prefixWord ++ tailWord_122035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122102 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_122102 : Nat := 118140960795 + 122102 * 2 ^ 59
def prefixEnd_122102 : Nat := 4983230072969 + 3 ^ 40 * 122102 * 2
def baseEnd_122102 : Nat := 20899004958462169687823

theorem tailTrace_122102 : CollatzResearch.WordTrace tailWord_122102 prefixEnd_122102 20899004958462169687823 := by
  unfold tailWord_122102
  simp only [CollatzResearch.WordTrace]
  refine ⟨278339112728298887905535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2968950535768521470992373 278339112728298887905535)
  ·
    refine ⟨417508669092448331858303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278339112728298887905535 417508669092448331858303)
    ·
      refine ⟨626263003638672497787455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417508669092448331858303 626263003638672497787455)
      ·
        refine ⟨939394505458008746681183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626263003638672497787455 939394505458008746681183)
        ·
          refine ⟨1409091758187013120021775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939394505458008746681183 1409091758187013120021775)
          ·
            refine ⟨2113637637280519680032663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409091758187013120021775 2113637637280519680032663)
            ·
              refine ⟨3170456455920779520048995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113637637280519680032663 3170456455920779520048995)
              ·
                refine ⟨4755684683881169280073493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170456455920779520048995 4755684683881169280073493)
                ·
                  refine ⟨222922719556929810003445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4755684683881169280073493 222922719556929810003445)
                  ·
                    refine ⟨20899004958462169687823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222922719556929810003445 20899004958462169687823)
                    ·
                      rfl

theorem cell23_122102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_122102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122102 prefixEnd_122102 := by exact prefixLift 122102
  have htrace : WordTrace (prefixWord ++ tailWord_122102) baseStart_122102 baseEnd_122102 := by
    simpa [prefixWord, tailWord_122102, baseEnd_122102] using wordTrace_append hprefix tailTrace_122102
  have hstable : (prefixWord ++ tailWord_122102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122102).length < 2 ^ (prefixWord ++ tailWord_122102).sum := by decide
  have hdescent : baseEnd_122102 < baseStart_122102 := by decide
  rcases family_descends (prefixWord ++ tailWord_122102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122173 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_122173 : Nat := 118140960795 + 122173 * 2 ^ 59
def prefixEnd_122173 : Nat := 4983230072969 + 3 ^ 40 * 122173 * 2
def baseEnd_122173 : Nat := 62733472001855731275643

theorem tailTrace_122173 : CollatzResearch.WordTrace tailWord_122173 prefixEnd_122173 62733472001855731275643 := by
  unfold tailWord_122173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456015386395561332323173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2970676924263707554882115 4456015386395561332323173)
  ·
    refine ⟨835502884949167749810595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4456015386395561332323173 835502884949167749810595)
    ·
      refine ⟨1253254327423751624715893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835502884949167749810595 1253254327423751624715893)
      ·
        refine ⟨117492593195976714817115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1253254327423751624715893 117492593195976714817115)
        ·
          refine ⟨176238889793965072225673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117492593195976714817115 176238889793965072225673)
          ·
            refine ⟨132179167345473804169255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176238889793965072225673 132179167345473804169255)
            ·
              refine ⟨198268751018210706253883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132179167345473804169255 198268751018210706253883)
              ·
                refine ⟨297403126527316059380825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198268751018210706253883 297403126527316059380825)
                ·
                  refine ⟨223052344895487044535619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297403126527316059380825 223052344895487044535619)
                  ·
                    refine ⟨334578517343230566803429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223052344895487044535619 334578517343230566803429)
                    ·
                      refine ⟨62733472001855731275643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 334578517343230566803429 62733472001855731275643)
                      ·
                        rfl

theorem cell23_122173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_122173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122173 prefixEnd_122173 := by exact prefixLift 122173
  have htrace : WordTrace (prefixWord ++ tailWord_122173) baseStart_122173 baseEnd_122173 := by
    simpa [prefixWord, tailWord_122173, baseEnd_122173] using wordTrace_append hprefix tailTrace_122173
  have hstable : (prefixWord ++ tailWord_122173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122173).length < 2 ^ (prefixWord ++ tailWord_122173).sum := by decide
  have hdescent : baseEnd_122173 < baseStart_122173 := by decide
  rcases family_descends (prefixWord ++ tailWord_122173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122232 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_122232 : Nat := 118140960795 + 122232 * 2 ^ 59
def prefixEnd_122232 : Nat := 4983230072969 + 3 ^ 40 * 122232 * 2
def baseEnd_122232 : Nat := 62763767360471000437871

theorem tailTrace_122232 : CollatzResearch.WordTrace tailWord_122232 prefixEnd_122232 62763767360471000437871 := by
  unfold tailWord_122232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229083646590907204360475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2972111528787876272480633 2229083646590907204360475)
  ·
    refine ⟨3343625469886360806540713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229083646590907204360475 3343625469886360806540713)
    ·
      refine ⟨2507719102414770604905535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343625469886360806540713 2507719102414770604905535)
      ·
        refine ⟨3761578653622155907358303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507719102414770604905535 3761578653622155907358303)
        ·
          refine ⟨5642367980433233861037455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761578653622155907358303 5642367980433233861037455)
          ·
            refine ⟨8463551970649850791556183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642367980433233861037455 8463551970649850791556183)
            ·
              refine ⟨12695327955974776187334275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463551970649850791556183 12695327955974776187334275)
              ·
                refine ⟨19042991933962164281001413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12695327955974776187334275 19042991933962164281001413)
                ·
                  refine ⟨3570560987617905802687765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19042991933962164281001413 3570560987617905802687765)
                  ·
                    refine ⟨167370046294589334500989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3570560987617905802687765 167370046294589334500989)
                    ·
                      refine ⟨62763767360471000437871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167370046294589334500989 62763767360471000437871)
                      ·
                        rfl

theorem cell23_122232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_122232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122232 prefixEnd_122232 := by exact prefixLift 122232
  have htrace : WordTrace (prefixWord ++ tailWord_122232) baseStart_122232 baseEnd_122232 := by
    simpa [prefixWord, tailWord_122232, baseEnd_122232] using wordTrace_append hprefix tailTrace_122232
  have hstable : (prefixWord ++ tailWord_122232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122232).length < 2 ^ (prefixWord ++ tailWord_122232).sum := by decide
  have hdescent : baseEnd_122232 < baseStart_122232 := by decide
  rcases family_descends (prefixWord ++ tailWord_122232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122269 : List Nat := [1, 4, 2, 1, 3, 2, 2, 8]
def baseStart_122269 : Nat := 118140960795 + 122269 * 2 ^ 59
def prefixEnd_122269 : Nat := 4983230072969 + 3 ^ 40 * 122269 * 2
def baseEnd_122269 : Nat := 2325287634988420580563

theorem tailTrace_122269 : CollatzResearch.WordTrace tailWord_122269 prefixEnd_122269 2325287634988420580563 := by
  unfold tailWord_122269
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459516794047769727817861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2973011196031846485211907 4459516794047769727817861)
  ·
    refine ⟨836159398883956823965849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4459516794047769727817861 836159398883956823965849)
    ·
      refine ⟨627119549162967617974387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836159398883956823965849 627119549162967617974387)
      ·
        refine ⟨940679323744451426961581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627119549162967617974387 940679323744451426961581)
        ·
          refine ⟨352754746404169285110593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940679323744451426961581 352754746404169285110593)
          ·
            refine ⟨264566059803126963832945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352754746404169285110593 264566059803126963832945)
            ·
              refine ⟨198424544852345222874709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264566059803126963832945 198424544852345222874709)
              ·
                refine ⟨2325287634988420580563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 198424544852345222874709 2325287634988420580563)
                ·
                  rfl

theorem cell23_122269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 8].length) (baseStart_122269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122269 prefixEnd_122269 := by exact prefixLift 122269
  have htrace : WordTrace (prefixWord ++ tailWord_122269) baseStart_122269 baseEnd_122269 := by
    simpa [prefixWord, tailWord_122269, baseEnd_122269] using wordTrace_append hprefix tailTrace_122269
  have hstable : (prefixWord ++ tailWord_122269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122269).length < 2 ^ (prefixWord ++ tailWord_122269).sum := by decide
  have hdescent : baseEnd_122269 < baseStart_122269 := by decide
  rcases family_descends (prefixWord ++ tailWord_122269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122272 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_122272 : Nat := 118140960795 + 122272 * 2 ^ 59
def prefixEnd_122272 : Nat := 4983230072969 + 3 ^ 40 * 122272 * 2
def baseEnd_122272 : Nat := 62784306586650843937687

theorem tailTrace_122272 : CollatzResearch.WordTrace tailWord_122272 prefixEnd_122272 62784306586650843937687 := by
  unfold tailWord_122272
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229813106518450620088535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2973084142024600826784713 2229813106518450620088535)
  ·
    refine ⟨3344719659777675930132803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229813106518450620088535 3344719659777675930132803)
    ·
      refine ⟨5017079489666513895199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344719659777675930132803 5017079489666513895199205)
      ·
        refine ⟨940702404312471355349851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5017079489666513895199205 940702404312471355349851)
        ·
          refine ⟨1411053606468707033024777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940702404312471355349851 1411053606468707033024777)
          ·
            refine ⟨1058290204851530274768583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411053606468707033024777 1058290204851530274768583)
            ·
              refine ⟨1587435307277295412152875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058290204851530274768583 1587435307277295412152875)
              ·
                refine ⟨2381152960915943118229313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587435307277295412152875 2381152960915943118229313)
                ·
                  refine ⟨1785864720686957338671985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381152960915943118229313 1785864720686957338671985)
                  ·
                    refine ⟨1339398540515218004003989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785864720686957338671985 1339398540515218004003989)
                    ·
                      refine ⟨62784306586650843937687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1339398540515218004003989 62784306586650843937687)
                      ·
                        rfl

theorem cell23_122272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_122272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122272 prefixEnd_122272 := by exact prefixLift 122272
  have htrace : WordTrace (prefixWord ++ tailWord_122272) baseStart_122272 baseEnd_122272 := by
    simpa [prefixWord, tailWord_122272, baseEnd_122272] using wordTrace_append hprefix tailTrace_122272
  have hstable : (prefixWord ++ tailWord_122272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122272).length < 2 ^ (prefixWord ++ tailWord_122272).sum := by decide
  have hdescent : baseEnd_122272 < baseStart_122272 := by decide
  rcases family_descends (prefixWord ++ tailWord_122272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122280 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_122280 : Nat := 118140960795 + 122280 * 2 ^ 59
def prefixEnd_122280 : Nat := 4983230072969 + 3 ^ 40 * 122280 * 2
def baseEnd_122280 : Nat := 62788414431886812637651

theorem tailTrace_122280 : CollatzResearch.WordTrace tailWord_122280 prefixEnd_122280 62788414431886812637651 := by
  unfold tailWord_122280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229958998503959303234147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2973278664671945737645529 2229958998503959303234147)
  ·
    refine ⟨3344938497755938954851221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229958998503959303234147 3344938497755938954851221)
    ·
      refine ⟨156793992082309638508651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3344938497755938954851221 156793992082309638508651)
      ·
        refine ⟨235190988123464457762977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156793992082309638508651 235190988123464457762977)
        ·
          refine ⟨176393241092598343322233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235190988123464457762977 176393241092598343322233)
          ·
            refine ⟨132294930819448757491675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176393241092598343322233 132294930819448757491675)
            ·
              refine ⟨198442396229173136237513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132294930819448757491675 198442396229173136237513)
              ·
                refine ⟨148831797171879852178135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198442396229173136237513 148831797171879852178135)
                ·
                  refine ⟨223247695757819778267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148831797171879852178135 223247695757819778267203)
                  ·
                    refine ⟨334871543636729667400805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223247695757819778267203 334871543636729667400805)
                    ·
                      refine ⟨62788414431886812637651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 334871543636729667400805 62788414431886812637651)
                      ·
                        rfl

theorem cell23_122280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_122280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122280 prefixEnd_122280 := by exact prefixLift 122280
  have htrace : WordTrace (prefixWord ++ tailWord_122280) baseStart_122280 baseEnd_122280 := by
    simpa [prefixWord, tailWord_122280, baseEnd_122280] using wordTrace_append hprefix tailTrace_122280
  have hstable : (prefixWord ++ tailWord_122280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122280).length < 2 ^ (prefixWord ++ tailWord_122280).sum := by decide
  have hdescent : baseEnd_122280 < baseStart_122280 := by decide
  rcases family_descends (prefixWord ++ tailWord_122280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122300 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_122300 : Nat := 118140960795 + 122300 * 2 ^ 59
def prefixEnd_122300 : Nat := 4983230072969 + 3 ^ 40 * 122300 * 2
def baseEnd_122300 : Nat := 62798684044976734387559

theorem tailTrace_122300 : CollatzResearch.WordTrace tailWord_122300 prefixEnd_122300 62798684044976734387559 := by
  unfold tailWord_122300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230323728467731011098177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2973764971290308014797569 2230323728467731011098177)
  ·
    refine ⟨1672742796350798258323633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2230323728467731011098177 1672742796350798258323633)
    ·
      refine ⟨1254557097263098693742725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1672742796350798258323633 1254557097263098693742725)
      ·
        refine ⟨235229455736831005076761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1254557097263098693742725 235229455736831005076761)
        ·
          refine ⟨176422091802623253807571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235229455736831005076761 176422091802623253807571)
          ·
            refine ⟨264633137703934880711357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176422091802623253807571 264633137703934880711357)
            ·
              refine ⟨99237426638975580266759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264633137703934880711357 99237426638975580266759)
              ·
                refine ⟨148856139958463370400139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99237426638975580266759 148856139958463370400139)
                ·
                  refine ⟨223284209937695055600209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148856139958463370400139 223284209937695055600209)
                  ·
                    refine ⟨167463157453271291700157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223284209937695055600209 167463157453271291700157)
                    ·
                      refine ⟨62798684044976734387559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167463157453271291700157 62798684044976734387559)
                      ·
                        rfl

theorem cell23_122300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_122300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122300 prefixEnd_122300 := by exact prefixLift 122300
  have htrace : WordTrace (prefixWord ++ tailWord_122300) baseStart_122300 baseEnd_122300 := by
    simpa [prefixWord, tailWord_122300, baseEnd_122300] using wordTrace_append hprefix tailTrace_122300
  have hstable : (prefixWord ++ tailWord_122300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122300).length < 2 ^ (prefixWord ++ tailWord_122300).sum := by decide
  have hdescent : baseEnd_122300 < baseStart_122300 := by decide
  rcases family_descends (prefixWord ++ tailWord_122300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122329 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_122329 : Nat := 118140960795 + 122329 * 2 ^ 59
def prefixEnd_122329 : Nat := 4983230072969 + 3 ^ 40 * 122329 * 2
def baseEnd_122329 : Nat := 20937858327985706974975

theorem tailTrace_122329 : CollatzResearch.WordTrace tailWord_122329 prefixEnd_122329 20937858327985706974975 := by
  unfold tailWord_122329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461705173830399975002041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2974470115886933316668027 4461705173830399975002041)
  ·
    refine ⟨3346278880372799981251531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4461705173830399975002041 3346278880372799981251531)
    ·
      refine ⟨5019418320559199971877297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346278880372799981251531 5019418320559199971877297)
      ·
        refine ⟨3764563740419399978907973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019418320559199971877297 3764563740419399978907973)
        ·
          refine ⟨705855701328637496045245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3764563740419399978907973 705855701328637496045245)
          ·
            refine ⟨264695887998239061016967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705855701328637496045245 264695887998239061016967)
            ·
              refine ⟨397043831997358591525451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264695887998239061016967 397043831997358591525451)
              ·
                refine ⟨595565747996037887288177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397043831997358591525451 595565747996037887288177)
                ·
                  refine ⟨446674310997028415466133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595565747996037887288177 446674310997028415466133)
                  ·
                    refine ⟨20937858327985706974975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 446674310997028415466133 20937858327985706974975)
                    ·
                      rfl

theorem cell23_122329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_122329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122329 prefixEnd_122329 := by exact prefixLift 122329
  have htrace : WordTrace (prefixWord ++ tailWord_122329) baseStart_122329 baseEnd_122329 := by
    simpa [prefixWord, tailWord_122329, baseEnd_122329] using wordTrace_append hprefix tailTrace_122329
  have hstable : (prefixWord ++ tailWord_122329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122329).length < 2 ^ (prefixWord ++ tailWord_122329).sum := by decide
  have hdescent : baseEnd_122329 < baseStart_122329 := by decide
  rcases family_descends (prefixWord ++ tailWord_122329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122357 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_122357 : Nat := 118140960795 + 122357 * 2 ^ 59
def prefixEnd_122357 : Nat := 4983230072969 + 3 ^ 40 * 122357 * 2
def baseEnd_122357 : Nat := 62827952442283011374797

theorem tailTrace_122357 : CollatzResearch.WordTrace tailWord_122357 prefixEnd_122357 62827952442283011374797 := by
  unfold tailWord_122357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462726417728960757021325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2975150945152640504680883 4462726417728960757021325)
  ·
    refine ⟨1673522406648360283882997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4462726417728960757021325 1673522406648360283882997)
    ·
      refine ⟨156892725623283776614031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1673522406648360283882997 156892725623283776614031)
      ·
        refine ⟨235339088434925664921047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156892725623283776614031 235339088434925664921047)
        ·
          refine ⟨353008632652388497381571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235339088434925664921047 353008632652388497381571)
          ·
            refine ⟨529512948978582746072357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353008632652388497381571 529512948978582746072357)
            ·
              refine ⟨99283677933484264888567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 529512948978582746072357 99283677933484264888567)
              ·
                refine ⟨148925516900226397332851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99283677933484264888567 148925516900226397332851)
                ·
                  refine ⟨223388275350339595999277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148925516900226397332851 223388275350339595999277)
                  ·
                    refine ⟨83770603256377348499729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223388275350339595999277 83770603256377348499729)
                    ·
                      refine ⟨62827952442283011374797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83770603256377348499729 62827952442283011374797)
                      ·
                        rfl

theorem cell23_122357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_122357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122357 prefixEnd_122357 := by exact prefixLift 122357
  have htrace : WordTrace (prefixWord ++ tailWord_122357) baseStart_122357 baseEnd_122357 := by
    simpa [prefixWord, tailWord_122357, baseEnd_122357] using wordTrace_append hprefix tailTrace_122357
  have hstable : (prefixWord ++ tailWord_122357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122357).length < 2 ^ (prefixWord ++ tailWord_122357).sum := by decide
  have hdescent : baseEnd_122357 < baseStart_122357 := by decide
  rcases family_descends (prefixWord ++ tailWord_122357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122376 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 5]
def baseStart_122376 : Nat := 118140960795 + 122376 * 2 ^ 59
def prefixEnd_122376 : Nat := 4983230072969 + 3 ^ 40 * 122376 * 2
def baseEnd_122376 : Nat := 6981967619413159670801

theorem tailTrace_122376 : CollatzResearch.WordTrace tailWord_122376 prefixEnd_122376 6981967619413159670801 := by
  unfold tailWord_122376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231709702330063500981491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2975612936440084667975321 2231709702330063500981491)
  ·
    refine ⟨3347564553495095251472237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2231709702330063500981491 3347564553495095251472237)
    ·
      refine ⟨1255336707560660719302089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3347564553495095251472237 1255336707560660719302089)
      ·
        refine ⟨941502530670495539476567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255336707560660719302089 941502530670495539476567)
        ·
          refine ⟨1412253796005743309214851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941502530670495539476567 1412253796005743309214851)
          ·
            refine ⟨2118380694008614963822277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412253796005743309214851 2118380694008614963822277)
            ·
              refine ⟨397196380126615305716677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2118380694008614963822277 397196380126615305716677)
              ·
                refine ⟨74474321273740369821877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397196380126615305716677 74474321273740369821877)
                ·
                  refine ⟨6981967619413159670801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74474321273740369821877 6981967619413159670801)
                  ·
                    rfl

theorem cell23_122376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 5].length) (baseStart_122376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122376 prefixEnd_122376 := by exact prefixLift 122376
  have htrace : WordTrace (prefixWord ++ tailWord_122376) baseStart_122376 baseEnd_122376 := by
    simpa [prefixWord, tailWord_122376, baseEnd_122376] using wordTrace_append hprefix tailTrace_122376
  have hstable : (prefixWord ++ tailWord_122376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122376).length < 2 ^ (prefixWord ++ tailWord_122376).sum := by decide
  have hdescent : baseEnd_122376 < baseStart_122376 := by decide
  rcases family_descends (prefixWord ++ tailWord_122376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122389 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_122389 : Nat := 118140960795 + 122389 * 2 ^ 59
def prefixEnd_122389 : Nat := 4983230072969 + 3 ^ 40 * 122389 * 2
def baseEnd_122389 : Nat := 20948127941075628724883

theorem tailTrace_122389 : CollatzResearch.WordTrace tailWord_122389 prefixEnd_122389 20948127941075628724883 := by
  unfold tailWord_122389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463893553613030222186221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2975929035742020148124147 4463893553613030222186221)
  ·
    refine ⟨1673960082604886333319833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4463893553613030222186221 1673960082604886333319833)
    ·
      refine ⟨1255470061953664749989875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1673960082604886333319833 1255470061953664749989875)
      ·
        refine ⟨1883205092930497124984813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255470061953664749989875 1883205092930497124984813)
        ·
          refine ⟨706201909848936421869305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1883205092930497124984813 706201909848936421869305)
          ·
            refine ⟨529651432386702316401979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706201909848936421869305 529651432386702316401979)
            ·
              refine ⟨794477148580053474602969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529651432386702316401979 794477148580053474602969)
              ·
                refine ⟨595857861435040105952227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794477148580053474602969 595857861435040105952227)
                ·
                  refine ⟨893786792152560158928341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595857861435040105952227 893786792152560158928341)
                  ·
                    refine ⟨20948127941075628724883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 893786792152560158928341 20948127941075628724883)
                    ·
                      rfl

theorem cell23_122389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_122389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122389 prefixEnd_122389 := by exact prefixLift 122389
  have htrace : WordTrace (prefixWord ++ tailWord_122389) baseStart_122389 baseEnd_122389 := by
    simpa [prefixWord, tailWord_122389, baseEnd_122389] using wordTrace_append hprefix tailTrace_122389
  have hstable : (prefixWord ++ tailWord_122389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122389).length < 2 ^ (prefixWord ++ tailWord_122389).sum := by decide
  have hdescent : baseEnd_122389 < baseStart_122389 := by decide
  rcases family_descends (prefixWord ++ tailWord_122389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122426 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_122426 : Nat := 118140960795 + 122426 * 2 ^ 59
def prefixEnd_122426 : Nat := 4983230072969 + 3 ^ 40 * 122426 * 2
def baseEnd_122426 : Nat := 62863382607443241411979

theorem tailTrace_122426 : CollatzResearch.WordTrace tailWord_122426 prefixEnd_122426 62863382607443241411979 := by
  unfold tailWord_122426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116310763619746385320783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2976828702985990360855421 1116310763619746385320783)
  ·
    refine ⟨1674466145429619577981175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1116310763619746385320783 1674466145429619577981175)
    ·
      refine ⟨2511699218144429366971763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674466145429619577981175 2511699218144429366971763)
      ·
        refine ⟨3767548827216644050457645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511699218144429366971763 3767548827216644050457645)
        ·
          refine ⟨1412830810206241518921617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3767548827216644050457645 1412830810206241518921617)
          ·
            refine ⟨1059623107654681139191213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412830810206241518921617 1059623107654681139191213)
            ·
              refine ⟨397358665370505427196705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059623107654681139191213 397358665370505427196705)
              ·
                refine ⟨298018999027879070397529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397358665370505427196705 298018999027879070397529)
                ·
                  refine ⟨223514249270909302798147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298018999027879070397529 223514249270909302798147)
                  ·
                    refine ⟨335271373906363954197221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223514249270909302798147 335271373906363954197221)
                    ·
                      refine ⟨62863382607443241411979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 335271373906363954197221 62863382607443241411979)
                      ·
                        rfl

theorem cell23_122426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_122426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122426 prefixEnd_122426 := by exact prefixLift 122426
  have htrace : WordTrace (prefixWord ++ tailWord_122426) baseStart_122426 baseEnd_122426 := by
    simpa [prefixWord, tailWord_122426, baseEnd_122426] using wordTrace_append hprefix tailTrace_122426
  have hstable : (prefixWord ++ tailWord_122426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122426).length < 2 ^ (prefixWord ++ tailWord_122426).sum := by decide
  have hdescent : baseEnd_122426 < baseStart_122426 := by decide
  rcases family_descends (prefixWord ++ tailWord_122426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122438 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_122438 : Nat := 118140960795 + 122438 * 2 ^ 59
def prefixEnd_122438 : Nat := 4983230072969 + 3 ^ 40 * 122438 * 2
def baseEnd_122438 : Nat := 62869544375297194461925

theorem tailTrace_122438 : CollatzResearch.WordTrace tailWord_122438 prefixEnd_122438 62869544375297194461925 := by
  unfold tailWord_122438
  simp only [CollatzResearch.WordTrace]
  refine ⟨139552522826109737209999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2977120486957007727146645 139552522826109737209999)
  ·
    refine ⟨209328784239164605814999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139552522826109737209999 209328784239164605814999)
    ·
      refine ⟨313993176358746908722499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209328784239164605814999 313993176358746908722499)
      ·
        refine ⟨470989764538120363083749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313993176358746908722499 470989764538120363083749)
        ·
          refine ⟨88310580850897568078203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470989764538120363083749 88310580850897568078203)
          ·
            refine ⟨132465871276346352117305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88310580850897568078203 132465871276346352117305)
            ·
              refine ⟨99349403457259764087979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132465871276346352117305 99349403457259764087979)
              ·
                refine ⟨149024105185889646131969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99349403457259764087979 149024105185889646131969)
                ·
                  refine ⟨111768078889417234598977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149024105185889646131969 111768078889417234598977)
                  ·
                    refine ⟨83826059167062925949233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111768078889417234598977 83826059167062925949233)
                    ·
                      refine ⟨62869544375297194461925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83826059167062925949233 62869544375297194461925)
                      ·
                        rfl

theorem cell23_122438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_122438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122438 prefixEnd_122438 := by exact prefixLift 122438
  have htrace : WordTrace (prefixWord ++ tailWord_122438) baseStart_122438 baseEnd_122438 := by
    simpa [prefixWord, tailWord_122438, baseEnd_122438] using wordTrace_append hprefix tailTrace_122438
  have hstable : (prefixWord ++ tailWord_122438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122438).length < 2 ^ (prefixWord ++ tailWord_122438).sum := by decide
  have hdescent : baseEnd_122438 < baseStart_122438 := by decide
  rcases family_descends (prefixWord ++ tailWord_122438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122446 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_122446 : Nat := 118140960795 + 122446 * 2 ^ 59
def prefixEnd_122446 : Nat := 4983230072969 + 3 ^ 40 * 122446 * 2
def baseEnd_122446 : Nat := 62873652220533163161887

theorem tailTrace_122446 : CollatzResearch.WordTrace tailWord_122446 prefixEnd_122446 62873652220533163161887 := by
  unfold tailWord_122446
  simp only [CollatzResearch.WordTrace]
  refine ⟨558246564300816119626399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2977315009604352638007461 558246564300816119626399)
  ·
    refine ⟨837369846451224179439599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558246564300816119626399 837369846451224179439599)
    ·
      refine ⟨1256054769676836269159399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837369846451224179439599 1256054769676836269159399)
      ·
        refine ⟨1884082154515254403739099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256054769676836269159399 1884082154515254403739099)
        ·
          refine ⟨2826123231772881605608649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884082154515254403739099 2826123231772881605608649)
          ·
            refine ⟨2119592423829661204206487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826123231772881605608649 2119592423829661204206487)
            ·
              refine ⟨3179388635744491806309731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119592423829661204206487 3179388635744491806309731)
              ·
                refine ⟨4769082953616737709464597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179388635744491806309731 4769082953616737709464597)
                ·
                  refine ⟨223550763450784580131153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4769082953616737709464597 223550763450784580131153)
                  ·
                    refine ⟨167663072588088435098365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223550763450784580131153 167663072588088435098365)
                    ·
                      refine ⟨62873652220533163161887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167663072588088435098365 62873652220533163161887)
                      ·
                        rfl

theorem cell23_122446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_122446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122446 prefixEnd_122446 := by exact prefixLift 122446
  have htrace : WordTrace (prefixWord ++ tailWord_122446) baseStart_122446 baseEnd_122446 := by
    simpa [prefixWord, tailWord_122446, baseEnd_122446] using wordTrace_append hprefix tailTrace_122446
  have hstable : (prefixWord ++ tailWord_122446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122446).length < 2 ^ (prefixWord ++ tailWord_122446).sum := by decide
  have hdescent : baseEnd_122446 < baseStart_122446 := by decide
  rcases family_descends (prefixWord ++ tailWord_122446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122510 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_122510 : Nat := 118140960795 + 122510 * 2 ^ 59
def prefixEnd_122510 : Nat := 4983230072969 + 3 ^ 40 * 122510 * 2
def baseEnd_122510 : Nat := 62906514982420912761593

theorem tailTrace_122510 : CollatzResearch.WordTrace tailWord_122510 prefixEnd_122510 62906514982420912761593 := by
  unfold tailWord_122510
  simp only [CollatzResearch.WordTrace]
  refine ⟨558538348271833485917623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2978871190783111924893989 558538348271833485917623)
  ·
    refine ⟨837807522407750228876435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558538348271833485917623 837807522407750228876435)
    ·
      refine ⟨1256711283611625343314653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837807522407750228876435 1256711283611625343314653)
      ·
        refine ⟨471266731354359503742995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1256711283611625343314653 471266731354359503742995)
        ·
          refine ⟨706900097031539255614493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471266731354359503742995 706900097031539255614493)
          ·
            refine ⟨265087536386827220855435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706900097031539255614493 265087536386827220855435)
            ·
              refine ⟨397631304580240831283153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265087536386827220855435 397631304580240831283153)
              ·
                refine ⟨298223478435180623462365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397631304580240831283153 298223478435180623462365)
                ·
                  refine ⟨111833804413192733798387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298223478435180623462365 111833804413192733798387)
                  ·
                    refine ⟨167750706619789100697581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111833804413192733798387 167750706619789100697581)
                    ·
                      refine ⟨62906514982420912761593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167750706619789100697581 62906514982420912761593)
                      ·
                        rfl

theorem cell23_122510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_122510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122510 prefixEnd_122510 := by exact prefixLift 122510
  have htrace : WordTrace (prefixWord ++ tailWord_122510) baseStart_122510 baseEnd_122510 := by
    simpa [prefixWord, tailWord_122510, baseEnd_122510] using wordTrace_append hprefix tailTrace_122510
  have hstable : (prefixWord ++ tailWord_122510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122510).length < 2 ^ (prefixWord ++ tailWord_122510).sum := by decide
  have hdescent : baseEnd_122510 < baseStart_122510 := by decide
  rcases family_descends (prefixWord ++ tailWord_122510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122520 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_122520 : Nat := 118140960795 + 122520 * 2 ^ 59
def prefixEnd_122520 : Nat := 4983230072969 + 3 ^ 40 * 122520 * 2
def baseEnd_122520 : Nat := 62911649788965873636547

theorem tailTrace_122520 : CollatzResearch.WordTrace tailWord_122520 prefixEnd_122520 62911649788965873636547 := by
  unfold tailWord_122520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234335758069219797602507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2979114344092293063470009 2234335758069219797602507)
  ·
    refine ⟨3351503637103829696403761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234335758069219797602507 3351503637103829696403761)
    ·
      refine ⟨2513627727827872272302821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351503637103829696403761 2513627727827872272302821)
      ·
        refine ⟨471305198967726051056779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2513627727827872272302821 471305198967726051056779)
        ·
          refine ⟨706957798451589076585169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471305198967726051056779 706957798451589076585169)
          ·
            refine ⟨530218348838691807438877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706957798451589076585169 530218348838691807438877)
            ·
              refine ⟨198831880814509427789579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530218348838691807438877 198831880814509427789579)
              ·
                refine ⟨298247821221764141684369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198831880814509427789579 298247821221764141684369)
                ·
                  refine ⟨223685865916323106263277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298247821221764141684369 223685865916323106263277)
                  ·
                    refine ⟨83882199718621164848729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223685865916323106263277 83882199718621164848729)
                    ·
                      refine ⟨62911649788965873636547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83882199718621164848729 62911649788965873636547)
                      ·
                        rfl

theorem cell23_122520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_122520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122520 prefixEnd_122520 := by exact prefixLift 122520
  have htrace : WordTrace (prefixWord ++ tailWord_122520) baseStart_122520 baseEnd_122520 := by
    simpa [prefixWord, tailWord_122520, baseEnd_122520] using wordTrace_append hprefix tailTrace_122520
  have hstable : (prefixWord ++ tailWord_122520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122520).length < 2 ^ (prefixWord ++ tailWord_122520).sum := by decide
  have hdescent : baseEnd_122520 < baseStart_122520 := by decide
  rcases family_descends (prefixWord ++ tailWord_122520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122546 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_122546 : Nat := 118140960795 + 122546 * 2 ^ 59
def prefixEnd_122546 : Nat := 4983230072969 + 3 ^ 40 * 122546 * 2
def baseEnd_122546 : Nat := 62925000285982771911427

theorem tailTrace_122546 : CollatzResearch.WordTrace tailWord_122546 prefixEnd_122546 62925000285982771911427 := by
  unfold tailWord_122546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117404953511061508912873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2979746542696164023767661 1117404953511061508912873)
  ·
    refine ⟨838053715133296131684655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117404953511061508912873 838053715133296131684655)
    ·
      refine ⟨1257080572699944197526983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838053715133296131684655 1257080572699944197526983)
      ·
        refine ⟨1885620859049916296290475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257080572699944197526983 1885620859049916296290475)
        ·
          refine ⟨2828431288574874444435713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885620859049916296290475 2828431288574874444435713)
          ·
            refine ⟨2121323466431155833326785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828431288574874444435713 2121323466431155833326785)
            ·
              refine ⟨1590992599823366874995089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121323466431155833326785 1590992599823366874995089)
              ·
                refine ⟨1193244449867525156246317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590992599823366874995089 1193244449867525156246317)
                ·
                  refine ⟨447466668700321933592369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193244449867525156246317 447466668700321933592369)
                  ·
                    refine ⟨335600001525241450194277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 447466668700321933592369 335600001525241450194277)
                    ·
                      refine ⟨62925000285982771911427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 335600001525241450194277 62925000285982771911427)
                      ·
                        rfl

theorem cell23_122546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_122546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122546 prefixEnd_122546 := by exact prefixLift 122546
  have htrace : WordTrace (prefixWord ++ tailWord_122546) baseStart_122546 baseEnd_122546 := by
    simpa [prefixWord, tailWord_122546, baseEnd_122546] using wordTrace_append hprefix tailTrace_122546
  have hstable : (prefixWord ++ tailWord_122546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122546).length < 2 ^ (prefixWord ++ tailWord_122546).sum := by decide
  have hdescent : baseEnd_122546 < baseStart_122546 := by decide
  rcases family_descends (prefixWord ++ tailWord_122546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122560 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_122560 : Nat := 118140960795 + 122560 * 2 ^ 59
def prefixEnd_122560 : Nat := 4983230072969 + 3 ^ 40 * 122560 * 2
def baseEnd_122560 : Nat := 20977396338381905712121

theorem tailTrace_122560 : CollatzResearch.WordTrace tailWord_122560 prefixEnd_122560 20977396338381905712121 := by
  unfold tailWord_122560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235065217996763213330567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2980086957329017617774089 2235065217996763213330567)
  ·
    refine ⟨3352597826995144819995851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2235065217996763213330567 3352597826995144819995851)
    ·
      refine ⟨5028896740492717229993777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3352597826995144819995851 5028896740492717229993777)
      ·
        refine ⟨3771672555369537922495333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5028896740492717229993777 3771672555369537922495333)
        ·
          refine ⟨707188604131788360467875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3771672555369537922495333 707188604131788360467875)
          ·
            refine ⟨1060782906197682540701813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707188604131788360467875 1060782906197682540701813)
            ·
              refine ⟨99448397456032738190795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1060782906197682540701813 99448397456032738190795)
              ·
                refine ⟨149172596184049107286193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99448397456032738190795 149172596184049107286193)
                ·
                  refine ⟨111879447138036830464645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149172596184049107286193 111879447138036830464645)
                  ·
                    refine ⟨20977396338381905712121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111879447138036830464645 20977396338381905712121)
                    ·
                      rfl

theorem cell23_122560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_122560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122560 prefixEnd_122560 := by exact prefixLift 122560
  have htrace : WordTrace (prefixWord ++ tailWord_122560) baseStart_122560 baseEnd_122560 := by
    simpa [prefixWord, tailWord_122560, baseEnd_122560] using wordTrace_append hprefix tailTrace_122560
  have hstable : (prefixWord ++ tailWord_122560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122560).length < 2 ^ (prefixWord ++ tailWord_122560).sum := by decide
  have hdescent : baseEnd_122560 < baseStart_122560 := by decide
  rcases family_descends (prefixWord ++ tailWord_122560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122583 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_122583 : Nat := 118140960795 + 122583 * 2 ^ 59
def prefixEnd_122583 : Nat := 4983230072969 + 3 ^ 40 * 122583 * 2
def baseEnd_122583 : Nat := 62943999070199127148757

theorem tailTrace_122583 : CollatzResearch.WordTrace tailWord_122583 prefixEnd_122583 62943999070199127148757 := by
  unfold tailWord_122583
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470969314910201354748403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2980646209940134236498935 4470969314910201354748403)
  ·
    refine ⟨6706453972365302032122605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470969314910201354748403 6706453972365302032122605)
    ·
      refine ⟨2514920239636988262045977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6706453972365302032122605 2514920239636988262045977)
      ·
        refine ⟨1886190179727741196534483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514920239636988262045977 1886190179727741196534483)
        ·
          refine ⟨2829285269591611794801725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886190179727741196534483 2829285269591611794801725)
          ·
            refine ⟨1060981976096854423050647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2829285269591611794801725 1060981976096854423050647)
            ·
              refine ⟨1591472964145281634575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060981976096854423050647 1591472964145281634575971)
              ·
                refine ⟨2387209446217922451863957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591472964145281634575971 2387209446217922451863957)
                ·
                  refine ⟨111900442791465114931123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2387209446217922451863957 111900442791465114931123)
                  ·
                    refine ⟨167850664187197672396685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111900442791465114931123 167850664187197672396685)
                    ·
                      refine ⟨62943999070199127148757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167850664187197672396685 62943999070199127148757)
                      ·
                        rfl

theorem cell23_122583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_122583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122583 prefixEnd_122583 := by exact prefixLift 122583
  have htrace : WordTrace (prefixWord ++ tailWord_122583) baseStart_122583 baseEnd_122583 := by
    simpa [prefixWord, tailWord_122583, baseEnd_122583] using wordTrace_append hprefix tailTrace_122583
  have hstable : (prefixWord ++ tailWord_122583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122583).length < 2 ^ (prefixWord ++ tailWord_122583).sum := by decide
  have hdescent : baseEnd_122583 < baseStart_122583 := by decide
  rcases family_descends (prefixWord ++ tailWord_122583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122596 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_122596 : Nat := 118140960795 + 122596 * 2 ^ 59
def prefixEnd_122596 : Nat := 4983230072969 + 3 ^ 40 * 122596 * 2
def baseEnd_122596 : Nat := 62950674318707576286197

theorem tailTrace_122596 : CollatzResearch.WordTrace tailWord_122596 prefixEnd_122596 62950674318707576286197 := by
  unfold tailWord_122596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235721731931552287485821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2980962309242069716647761 2235721731931552287485821)
  ·
    refine ⟨838395649474332107807183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2235721731931552287485821 838395649474332107807183)
    ·
      refine ⟨1257593474211498161710775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838395649474332107807183 1257593474211498161710775)
      ·
        refine ⟨1886390211317247242566163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257593474211498161710775 1886390211317247242566163)
        ·
          refine ⟨2829585316975870863849245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886390211317247242566163 2829585316975870863849245)
          ·
            refine ⟨1061094493865951573943467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2829585316975870863849245 1061094493865951573943467)
            ·
              refine ⟨1591641740798927360915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061094493865951573943467 1591641740798927360915201)
              ·
                refine ⟨1193731305599195520686401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591641740798927360915201 1193731305599195520686401)
                ·
                  refine ⟨895298479199396640514801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193731305599195520686401 895298479199396640514801)
                  ·
                    refine ⟨671473859399547480386101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895298479199396640514801 671473859399547480386101)
                    ·
                      refine ⟨62950674318707576286197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 671473859399547480386101 62950674318707576286197)
                      ·
                        rfl

theorem cell23_122596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_122596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122596 prefixEnd_122596 := by exact prefixLift 122596
  have htrace : WordTrace (prefixWord ++ tailWord_122596) baseStart_122596 baseEnd_122596 := by
    simpa [prefixWord, tailWord_122596, baseEnd_122596] using wordTrace_append hprefix tailTrace_122596
  have hstable : (prefixWord ++ tailWord_122596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122596).length < 2 ^ (prefixWord ++ tailWord_122596).sum := by decide
  have hdescent : baseEnd_122596 < baseStart_122596 := by decide
  rcases family_descends (prefixWord ++ tailWord_122596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122600 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_122600 : Nat := 118140960795 + 122600 * 2 ^ 59
def prefixEnd_122600 : Nat := 4983230072969 + 3 ^ 40 * 122600 * 2
def baseEnd_122600 : Nat := 62952728241325560636179

theorem tailTrace_122600 : CollatzResearch.WordTrace tailWord_122600 prefixEnd_122600 62952728241325560636179 := by
  unfold tailWord_122600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235794677924306629058627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2981059570565742172078169 2235794677924306629058627)
  ·
    refine ⟨3353692016886459943587941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2235794677924306629058627 3353692016886459943587941)
    ·
      refine ⟨628817253166211239422739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3353692016886459943587941 628817253166211239422739)
      ·
        refine ⟨943225879749316859134109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628817253166211239422739 943225879749316859134109)
        ·
          refine ⟨353709704905993822175291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 943225879749316859134109 353709704905993822175291)
          ·
            refine ⟨530564557358990733262937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353709704905993822175291 530564557358990733262937)
            ·
              refine ⟨397923418019243049947203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530564557358990733262937 397923418019243049947203)
              ·
                refine ⟨596885127028864574920805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397923418019243049947203 596885127028864574920805)
                ·
                  refine ⟨111915961317912107797651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596885127028864574920805 111915961317912107797651)
                  ·
                    refine ⟨167873941976868161696477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111915961317912107797651 167873941976868161696477)
                    ·
                      refine ⟨62952728241325560636179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167873941976868161696477 62952728241325560636179)
                      ·
                        rfl

theorem cell23_122600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_122600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122600 prefixEnd_122600 := by exact prefixLift 122600
  have htrace : WordTrace (prefixWord ++ tailWord_122600) baseStart_122600 baseEnd_122600 := by
    simpa [prefixWord, tailWord_122600, baseEnd_122600] using wordTrace_append hprefix tailTrace_122600
  have hstable : (prefixWord ++ tailWord_122600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122600).length < 2 ^ (prefixWord ++ tailWord_122600).sum := by decide
  have hdescent : baseEnd_122600 < baseStart_122600 := by decide
  rcases family_descends (prefixWord ++ tailWord_122600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122610 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_122610 : Nat := 118140960795 + 122610 * 2 ^ 59
def prefixEnd_122610 : Nat := 4983230072969 + 3 ^ 40 * 122610 * 2
def baseEnd_122610 : Nat := 62957863047870521511133

theorem tailTrace_122610 : CollatzResearch.WordTrace tailWord_122610 prefixEnd_122610 62957863047870521511133 := by
  unfold tailWord_122610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117988521453096241495321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2981302723874923310654189 1117988521453096241495321)
  ·
    refine ⟨838491391089822181121491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117988521453096241495321 838491391089822181121491)
    ·
      refine ⟨1257737086634733271682237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838491391089822181121491 1257737086634733271682237)
      ·
        refine ⟨471651407488024976880839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1257737086634733271682237 471651407488024976880839)
        ·
          refine ⟨707477111232037465321259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471651407488024976880839 707477111232037465321259)
          ·
            refine ⟨1061215666848056197981889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707477111232037465321259 1061215666848056197981889)
            ·
              refine ⟨795911750136042148486417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061215666848056197981889 795911750136042148486417)
              ·
                refine ⟨596933812602031611364813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795911750136042148486417 596933812602031611364813)
                ·
                  refine ⟨223850179725761854261805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596933812602031611364813 223850179725761854261805)
                  ·
                    refine ⟨83943817397160695348177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223850179725761854261805 83943817397160695348177)
                    ·
                      refine ⟨62957863047870521511133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83943817397160695348177 62957863047870521511133)
                      ·
                        rfl

theorem cell23_122610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_122610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122610 prefixEnd_122610 := by exact prefixLift 122610
  have htrace : WordTrace (prefixWord ++ tailWord_122610) baseStart_122610 baseEnd_122610 := by
    simpa [prefixWord, tailWord_122610, baseEnd_122610] using wordTrace_append hprefix tailTrace_122610
  have hstable : (prefixWord ++ tailWord_122610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122610).length < 2 ^ (prefixWord ++ tailWord_122610).sum := by decide
  have hdescent : baseEnd_122610 < baseStart_122610 := by decide
  rcases family_descends (prefixWord ++ tailWord_122610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122657 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_122657 : Nat := 118140960795 + 122657 * 2 ^ 59
def prefixEnd_122657 : Nat := 4983230072969 + 3 ^ 40 * 122657 * 2
def baseEnd_122657 : Nat := 62981996638631837623417

theorem tailTrace_122657 : CollatzResearch.WordTrace tailWord_122657 prefixEnd_122657 62981996638631837623417 := by
  unfold tailWord_122657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473668316642111992942225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2982445544428074661961483 4473668316642111992942225)
  ·
    refine ⟨3355251237481583994706669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4473668316642111992942225 3355251237481583994706669)
    ·
      refine ⟨1258219214055593998015001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3355251237481583994706669 1258219214055593998015001)
      ·
        refine ⟨943664410541695498511251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258219214055593998015001 943664410541695498511251)
        ·
          refine ⟨1415496615812543247766877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943664410541695498511251 1415496615812543247766877)
          ·
            refine ⟨530811230929703717912579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1415496615812543247766877 530811230929703717912579)
            ·
              refine ⟨796216846394555576868869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530811230929703717912579 796216846394555576868869)
              ·
                refine ⟨149290658698979170662913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796216846394555576868869 149290658698979170662913)
                ·
                  refine ⟨111967994024234377997185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149290658698979170662913 111967994024234377997185)
                  ·
                    refine ⟨83975995518175783497889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111967994024234377997185 83975995518175783497889)
                    ·
                      refine ⟨62981996638631837623417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 83975995518175783497889 62981996638631837623417)
                      ·
                        rfl

theorem cell23_122657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_122657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122657 prefixEnd_122657 := by exact prefixLift 122657
  have htrace : WordTrace (prefixWord ++ tailWord_122657) baseStart_122657 baseEnd_122657 := by
    simpa [prefixWord, tailWord_122657, baseEnd_122657] using wordTrace_append hprefix tailTrace_122657
  have hstable : (prefixWord ++ tailWord_122657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122657).length < 2 ^ (prefixWord ++ tailWord_122657).sum := by decide
  have hdescent : baseEnd_122657 < baseStart_122657 := by decide
  rcases family_descends (prefixWord ++ tailWord_122657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122673 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_122673 : Nat := 118140960795 + 122673 * 2 ^ 59
def prefixEnd_122673 : Nat := 4983230072969 + 3 ^ 40 * 122673 * 2
def baseEnd_122673 : Nat := 62990212329103775023343

theorem tailTrace_122673 : CollatzResearch.WordTrace tailWord_122673 prefixEnd_122673 62990212329103775023343 := by
  unfold tailWord_122673
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474251884584146725524673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2982834589722764483683115 4474251884584146725524673)
  ·
    refine ⟨3355688913438110044143505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4474251884584146725524673 3355688913438110044143505)
    ·
      refine ⟨2516766685078582533107629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3355688913438110044143505 2516766685078582533107629)
      ·
        refine ⟨943787506904468449915361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2516766685078582533107629 943787506904468449915361)
        ·
          refine ⟨707840630178351337436521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943787506904468449915361 707840630178351337436521)
          ·
            refine ⟨530880472633763503077391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707840630178351337436521 530880472633763503077391)
            ·
              refine ⟨796320708950645254616087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530880472633763503077391 796320708950645254616087)
              ·
                refine ⟨1194481063425967881924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796320708950645254616087 1194481063425967881924131)
                ·
                  refine ⟨1791721595138951822886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194481063425967881924131 1791721595138951822886197)
                  ·
                    refine ⟨167973899544276733395581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1791721595138951822886197 167973899544276733395581)
                    ·
                      refine ⟨62990212329103775023343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 167973899544276733395581 62990212329103775023343)
                      ·
                        rfl

theorem cell23_122673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_122673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122673 prefixEnd_122673 := by exact prefixLift 122673
  have htrace : WordTrace (prefixWord ++ tailWord_122673) baseStart_122673 baseEnd_122673 := by
    simpa [prefixWord, tailWord_122673, baseEnd_122673] using wordTrace_append hprefix tailTrace_122673
  have hstable : (prefixWord ++ tailWord_122673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122673).length < 2 ^ (prefixWord ++ tailWord_122673).sum := by decide
  have hdescent : baseEnd_122673 < baseStart_122673 := by decide
  rcases family_descends (prefixWord ++ tailWord_122673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122713 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_122713 : Nat := 118140960795 + 122713 * 2 ^ 59
def prefixEnd_122713 : Nat := 4983230072969 + 3 ^ 40 * 122713 * 2
def baseEnd_122713 : Nat := 63010751555283618523159

theorem tailTrace_122713 : CollatzResearch.WordTrace tailWord_122713 prefixEnd_122713 63010751555283618523159 := by
  unfold tailWord_122713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475710804439233556980793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2983807202959489037987195 4475710804439233556980793)
  ·
    refine ⟨3356783103329425167735595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4475710804439233556980793 3356783103329425167735595)
    ·
      refine ⟨5035174654994137751603393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356783103329425167735595 5035174654994137751603393)
      ·
        refine ⟨3776380991245603313702545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5035174654994137751603393 3776380991245603313702545)
        ·
          refine ⟨2832285743434202485276909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3776380991245603313702545 2832285743434202485276909)
          ·
            refine ⟨1062107153787825931978841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2832285743434202485276909 1062107153787825931978841)
            ·
              refine ⟨796580365340869448984131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062107153787825931978841 796580365340869448984131)
              ·
                refine ⟨1194870548011304173476197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796580365340869448984131 1194870548011304173476197)
                ·
                  refine ⟨224038227752119532526787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194870548011304173476197 224038227752119532526787)
                  ·
                    refine ⟨336057341628179298790181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224038227752119532526787 336057341628179298790181)
                    ·
                      refine ⟨63010751555283618523159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 336057341628179298790181 63010751555283618523159)
                      ·
                        rfl

theorem cell23_122713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_122713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122713 prefixEnd_122713 := by exact prefixLift 122713
  have htrace : WordTrace (prefixWord ++ tailWord_122713) baseStart_122713 baseEnd_122713 := by
    simpa [prefixWord, tailWord_122713, baseEnd_122713] using wordTrace_append hprefix tailTrace_122713
  have hstable : (prefixWord ++ tailWord_122713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122713).length < 2 ^ (prefixWord ++ tailWord_122713).sum := by decide
  have hdescent : baseEnd_122713 < baseStart_122713 := by decide
  rcases family_descends (prefixWord ++ tailWord_122713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122770 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_122770 : Nat := 118140960795 + 122770 * 2 ^ 59
def prefixEnd_122770 : Nat := 4983230072969 + 3 ^ 40 * 122770 * 2
def baseEnd_122770 : Nat := 7004446661398877278933

theorem tailTrace_122770 : CollatzResearch.WordTrace tailWord_122770 prefixEnd_122770 7004446661398877278933 := by
  unfold tailWord_122770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119447441308183072951441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2985193176821821527870509 1119447441308183072951441)
  ·
    refine ⟨839585580981137304713581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119447441308183072951441 839585580981137304713581)
    ·
      refine ⟨314844592867926489267593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 839585580981137304713581 314844592867926489267593)
      ·
        refine ⟨236133444650944866950695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314844592867926489267593 236133444650944866950695)
        ·
          refine ⟨354200166976417300426043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236133444650944866950695 354200166976417300426043)
          ·
            refine ⟨531300250464625950639065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354200166976417300426043 531300250464625950639065)
            ·
              refine ⟨398475187848469462979299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531300250464625950639065 398475187848469462979299)
              ·
                refine ⟨597712781772704194468949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398475187848469462979299 597712781772704194468949)
                ·
                  refine ⟨7004446661398877278933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 597712781772704194468949 7004446661398877278933)
                  ·
                    rfl

theorem cell23_122770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_122770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122770 prefixEnd_122770 := by exact prefixLift 122770
  have htrace : WordTrace (prefixWord ++ tailWord_122770) baseStart_122770 baseEnd_122770 := by
    simpa [prefixWord, tailWord_122770, baseEnd_122770] using wordTrace_append hprefix tailTrace_122770
  have hstable : (prefixWord ++ tailWord_122770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122770).length < 2 ^ (prefixWord ++ tailWord_122770).sum := by decide
  have hdescent : baseEnd_122770 < baseStart_122770 := by decide
  rcases family_descends (prefixWord ++ tailWord_122770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122833 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_122833 : Nat := 118140960795 + 122833 * 2 ^ 59
def prefixEnd_122833 : Nat := 4983230072969 + 3 ^ 40 * 122833 * 2
def baseEnd_122833 : Nat := 63072369233823149022607

theorem tailTrace_122833 : CollatzResearch.WordTrace tailWord_122833 prefixEnd_122833 63072369233823149022607 := by
  unfold tailWord_122833
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480087564004494051349153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2986725042669662700899435 4480087564004494051349153)
  ·
    refine ⟨3360065673003370538511865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4480087564004494051349153 3360065673003370538511865)
    ·
      refine ⟨2520049254752527903883899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3360065673003370538511865 2520049254752527903883899)
      ·
        refine ⟨3780073882128791855825849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520049254752527903883899 3780073882128791855825849)
        ·
          refine ⟨2835055411596593891869387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780073882128791855825849 2835055411596593891869387)
          ·
            refine ⟨4252583117394890837804081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835055411596593891869387 4252583117394890837804081)
            ·
              refine ⟨3189437338046168128353061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252583117394890837804081 3189437338046168128353061)
              ·
                refine ⟨598019500883656524066199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3189437338046168128353061 598019500883656524066199)
                ·
                  refine ⟨897029251325484786099299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598019500883656524066199 897029251325484786099299)
                  ·
                    refine ⟨1345543876988227179148949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 897029251325484786099299 1345543876988227179148949)
                    ·
                      refine ⟨63072369233823149022607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1345543876988227179148949 63072369233823149022607)
                      ·
                        rfl

theorem cell23_122833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_122833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122833 prefixEnd_122833 := by exact prefixLift 122833
  have htrace : WordTrace (prefixWord ++ tailWord_122833) baseStart_122833 baseEnd_122833 := by
    simpa [prefixWord, tailWord_122833, baseEnd_122833] using wordTrace_append hprefix tailTrace_122833
  have hstable : (prefixWord ++ tailWord_122833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122833).length < 2 ^ (prefixWord ++ tailWord_122833).sum := by decide
  have hdescent : baseEnd_122833 < baseStart_122833 := by decide
  rcases family_descends (prefixWord ++ tailWord_122833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122840 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_122840 : Nat := 118140960795 + 122840 * 2 ^ 59
def prefixEnd_122840 : Nat := 4983230072969 + 3 ^ 40 * 122840 * 2
def baseEnd_122840 : Nat := 63075963598404621635075

theorem tailTrace_122840 : CollatzResearch.WordTrace tailWord_122840 prefixEnd_122840 63075963598404621635075 := by
  unfold tailWord_122840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240171437489567123426987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2986895249986089497902649 2240171437489567123426987)
  ·
    refine ⟨3360257156234350685140481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240171437489567123426987 3360257156234350685140481)
    ·
      refine ⟨2520192867175763013855361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3360257156234350685140481 2520192867175763013855361)
      ·
        refine ⟨1890144650381822260391521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520192867175763013855361 1890144650381822260391521)
        ·
          refine ⟨1417608487786366695293641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890144650381822260391521 1417608487786366695293641)
          ·
            refine ⟨1063206365839775021470231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417608487786366695293641 1063206365839775021470231)
            ·
              refine ⟨1594809548759662532205347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063206365839775021470231 1594809548759662532205347)
              ·
                refine ⟨2392214323139493798308021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594809548759662532205347 2392214323139493798308021)
                ·
                  refine ⟨224270092794327543591377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392214323139493798308021 224270092794327543591377)
                  ·
                    refine ⟨168202569595745657693533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224270092794327543591377 168202569595745657693533)
                    ·
                      refine ⟨63075963598404621635075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 168202569595745657693533 63075963598404621635075)
                      ·
                        rfl

theorem cell23_122840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_122840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122840 prefixEnd_122840 := by exact prefixLift 122840
  have htrace : WordTrace (prefixWord ++ tailWord_122840) baseStart_122840 baseEnd_122840 := by
    simpa [prefixWord, tailWord_122840, baseEnd_122840] using wordTrace_append hprefix tailTrace_122840
  have hstable : (prefixWord ++ tailWord_122840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122840).length < 2 ^ (prefixWord ++ tailWord_122840).sum := by decide
  have hdescent : baseEnd_122840 < baseStart_122840 := by decide
  rcases family_descends (prefixWord ++ tailWord_122840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122847 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 2, 4]
def baseStart_122847 : Nat := 118140960795 + 122847 * 2 ^ 59
def prefixEnd_122847 : Nat := 4983230072969 + 3 ^ 40 * 122847 * 2
def baseEnd_122847 : Nat := 21026519320995364749181

theorem tailTrace_122847 : CollatzResearch.WordTrace tailWord_122847 prefixEnd_122847 21026519320995364749181 := by
  unfold tailWord_122847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480598185953774442358795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2987065457302516294905863 4480598185953774442358795)
  ·
    refine ⟨6720897278930661663538193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4480598185953774442358795 6720897278930661663538193)
    ·
      refine ⟨5040672959197996247653645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6720897278930661663538193 5040672959197996247653645)
      ·
        refine ⟨1890252359699248592870117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5040672959197996247653645 1890252359699248592870117)
        ·
          refine ⟨354422317443609111163147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1890252359699248592870117 354422317443609111163147)
          ·
            refine ⟨531633476165413666744721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354422317443609111163147 531633476165413666744721)
            ·
              refine ⟨398725107124060250058541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531633476165413666744721 398725107124060250058541)
              ·
                refine ⟨149521915171522593771953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398725107124060250058541 149521915171522593771953)
                ·
                  refine ⟨112141436378641945328965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149521915171522593771953 112141436378641945328965)
                  ·
                    refine ⟨21026519320995364749181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112141436378641945328965 21026519320995364749181)
                    ·
                      rfl

theorem cell23_122847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_122847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122847 prefixEnd_122847 := by exact prefixLift 122847
  have htrace : WordTrace (prefixWord ++ tailWord_122847) baseStart_122847 baseEnd_122847 := by
    simpa [prefixWord, tailWord_122847, baseEnd_122847] using wordTrace_append hprefix tailTrace_122847
  have hstable : (prefixWord ++ tailWord_122847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122847).length < 2 ^ (prefixWord ++ tailWord_122847).sum := by decide
  have hdescent : baseEnd_122847 < baseStart_122847 := by decide
  rcases family_descends (prefixWord ++ tailWord_122847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122930 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_122930 : Nat := 118140960795 + 122930 * 2 ^ 59
def prefixEnd_122930 : Nat := 4983230072969 + 3 ^ 40 * 122930 * 2
def baseEnd_122930 : Nat := 63122176857309269509661

theorem tailTrace_122930 : CollatzResearch.WordTrace tailWord_122930 prefixEnd_122930 63122176857309269509661 := by
  unfold tailWord_122930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120906361163269904407561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2989083629768719745086829 1120906361163269904407561)
  ·
    refine ⟨840679770872452428305671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1120906361163269904407561 840679770872452428305671)
    ·
      refine ⟨1261019656308678642458507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840679770872452428305671 1261019656308678642458507)
      ·
        refine ⟨1891529484463017963687761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261019656308678642458507 1891529484463017963687761)
        ·
          refine ⟨1418647113347263472765821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891529484463017963687761 1418647113347263472765821)
          ·
            refine ⟨531992667505223802287183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418647113347263472765821 531992667505223802287183)
            ·
              refine ⟨797989001257835703430775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531992667505223802287183 797989001257835703430775)
              ·
                refine ⟨1196983501886753555146163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797989001257835703430775 1196983501886753555146163)
                ·
                  refine ⟨1795475252830130332719245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196983501886753555146163 1795475252830130332719245)
                  ·
                    refine ⟨673303219811298874769717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795475252830130332719245 673303219811298874769717)
                    ·
                      refine ⟨63122176857309269509661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 673303219811298874769717 63122176857309269509661)
                      ·
                        rfl

theorem cell23_122930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_122930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122930 prefixEnd_122930 := by exact prefixLift 122930
  have htrace : WordTrace (prefixWord ++ tailWord_122930) baseStart_122930 baseEnd_122930 := by
    simpa [prefixWord, tailWord_122930, baseEnd_122930] using wordTrace_append hprefix tailTrace_122930
  have hstable : (prefixWord ++ tailWord_122930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122930).length < 2 ^ (prefixWord ++ tailWord_122930).sum := by decide
  have hdescent : baseEnd_122930 < baseStart_122930 := by decide
  rcases family_descends (prefixWord ++ tailWord_122930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122944 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2]
def baseStart_122944 : Nat := 118140960795 + 122944 * 2 ^ 59
def prefixEnd_122944 : Nat := 4983230072969 + 3 ^ 40 * 122944 * 2
def baseEnd_122944 : Nat := 63129365586472214734597

theorem tailTrace_122944 : CollatzResearch.WordTrace tailWord_122944 prefixEnd_122944 63129365586472214734597 := by
  unfold tailWord_122944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242068033301180004319943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2989424044401573339093257 2242068033301180004319943)
  ·
    refine ⟨3363102049951770006479915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242068033301180004319943 3363102049951770006479915)
    ·
      refine ⟨5044653074927655009719873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363102049951770006479915 5044653074927655009719873)
      ·
        refine ⟨3783489806195741257289905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5044653074927655009719873 3783489806195741257289905)
        ·
          refine ⟨2837617354646805942967429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3783489806195741257289905 2837617354646805942967429)
          ·
            refine ⟨532053253996276114306393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2837617354646805942967429 532053253996276114306393)
            ·
              refine ⟨399039940497207085729795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532053253996276114306393 399039940497207085729795)
              ·
                refine ⟨598559910745810628594693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399039940497207085729795 598559910745810628594693)
                ·
                  refine ⟨112229983264839492861505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598559910745810628594693 112229983264839492861505)
                  ·
                    refine ⟨84172487448629619646129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112229983264839492861505 84172487448629619646129)
                    ·
                      refine ⟨63129365586472214734597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84172487448629619646129 63129365586472214734597)
                      ·
                        rfl

theorem cell23_122944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_122944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122944 prefixEnd_122944 := by exact prefixLift 122944
  have htrace : WordTrace (prefixWord ++ tailWord_122944) baseStart_122944 baseEnd_122944 := by
    simpa [prefixWord, tailWord_122944, baseEnd_122944] using wordTrace_append hprefix tailTrace_122944
  have hstable : (prefixWord ++ tailWord_122944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122944).length < 2 ^ (prefixWord ++ tailWord_122944).sum := by decide
  have hdescent : baseEnd_122944 < baseStart_122944 := by decide
  rcases family_descends (prefixWord ++ tailWord_122944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122957 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_122957 : Nat := 118140960795 + 122957 * 2 ^ 59
def prefixEnd_122957 : Nat := 4983230072969 + 3 ^ 40 * 122957 * 2
def baseEnd_122957 : Nat := 63136040834980663872037

theorem tailTrace_122957 : CollatzResearch.WordTrace tailWord_122957 prefixEnd_122957 63136040834980663872037 := by
  unfold tailWord_122957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484610215555263228863125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2989740143703508819242083 4484610215555263228863125)
  ·
    refine ⟨210216103854152963852959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4484610215555263228863125 210216103854152963852959)
    ·
      refine ⟨315324155781229445779439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210216103854152963852959 315324155781229445779439)
      ·
        refine ⟨472986233671844168669159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315324155781229445779439 472986233671844168669159)
        ·
          refine ⟨709479350507766253003739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472986233671844168669159 709479350507766253003739)
          ·
            refine ⟨1064219025761649379505609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709479350507766253003739 1064219025761649379505609)
            ·
              refine ⟨798164269321237034629207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064219025761649379505609 798164269321237034629207)
              ·
                refine ⟨1197246403981855551943811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798164269321237034629207 1197246403981855551943811)
                ·
                  refine ⟨1795869605972783327915717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197246403981855551943811 1795869605972783327915717)
                  ·
                    refine ⟨336725551119896873984197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795869605972783327915717 336725551119896873984197)
                    ·
                      refine ⟨63136040834980663872037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 336725551119896873984197 63136040834980663872037)
                      ·
                        rfl

theorem cell23_122957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_122957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122957 prefixEnd_122957 := by exact prefixLift 122957
  have htrace : WordTrace (prefixWord ++ tailWord_122957) baseStart_122957 baseEnd_122957 := by
    simpa [prefixWord, tailWord_122957, baseEnd_122957] using wordTrace_append hprefix tailTrace_122957
  have hstable : (prefixWord ++ tailWord_122957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122957).length < 2 ^ (prefixWord ++ tailWord_122957).sum := by decide
  have hdescent : baseEnd_122957 < baseStart_122957 := by decide
  rcases family_descends (prefixWord ++ tailWord_122957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122980 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_122980 : Nat := 118140960795 + 122980 * 2 ^ 59
def prefixEnd_122980 : Nat := 4983230072969 + 3 ^ 40 * 122980 * 2
def baseEnd_122980 : Nat := 21049283630011357961477

theorem tailTrace_122980 : CollatzResearch.WordTrace tailWord_122980 prefixEnd_122980 21049283630011357961477 := by
  unfold tailWord_122980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242724547235969078475197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2990299396314625437966929 2242724547235969078475197)
  ·
    refine ⟨841021705213488404428199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2242724547235969078475197 841021705213488404428199)
    ·
      refine ⟨1261532557820232606642299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841021705213488404428199 1261532557820232606642299)
      ·
        refine ⟨1892298836730348909963449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261532557820232606642299 1892298836730348909963449)
        ·
          refine ⟨1419224127547761682472587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892298836730348909963449 1419224127547761682472587)
          ·
            refine ⟨2128836191321642523708881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419224127547761682472587 2128836191321642523708881)
            ·
              refine ⟨1596627143491231892781661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128836191321642523708881 1596627143491231892781661)
              ·
                refine ⟨598735178809211959793123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596627143491231892781661 598735178809211959793123)
                ·
                  refine ⟨898102768213817939689685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598735178809211959793123 898102768213817939689685)
                  ·
                    refine ⟨21049283630011357961477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 898102768213817939689685 21049283630011357961477)
                    ·
                      rfl

theorem cell23_122980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_122980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_122980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_122980 prefixEnd_122980 := by exact prefixLift 122980
  have htrace : WordTrace (prefixWord ++ tailWord_122980) baseStart_122980 baseEnd_122980 := by
    simpa [prefixWord, tailWord_122980, baseEnd_122980] using wordTrace_append hprefix tailTrace_122980
  have hstable : (prefixWord ++ tailWord_122980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122980).length < 2 ^ (prefixWord ++ tailWord_122980).sum := by decide
  have hdescent : baseEnd_122980 < baseStart_122980 := by decide
  rcases family_descends (prefixWord ++ tailWord_122980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123000 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_123000 : Nat := 118140960795 + 123000 * 2 ^ 59
def prefixEnd_123000 : Nat := 4983230072969 + 3 ^ 40 * 123000 * 2
def baseEnd_123000 : Nat := 63158120503123995634339

theorem tailTrace_123000 : CollatzResearch.WordTrace tailWord_123000 prefixEnd_123000 63158120503123995634339 := by
  unfold tailWord_123000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243089277199740786339227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2990785702932987715118969 2243089277199740786339227)
  ·
    refine ⟨3364633915799611179508841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2243089277199740786339227 3364633915799611179508841)
    ·
      refine ⟨2523475436849708384631631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364633915799611179508841 2523475436849708384631631)
      ·
        refine ⟨3785213155274562576947447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523475436849708384631631 3785213155274562576947447)
        ·
          refine ⟨5677819732911843865421171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785213155274562576947447 5677819732911843865421171)
          ·
            refine ⟨8516729599367765798131757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677819732911843865421171 8516729599367765798131757)
            ·
              refine ⟨3193773599762912174299409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8516729599367765798131757 3193773599762912174299409)
              ·
                refine ⟨2395330199822184130724557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193773599762912174299409 2395330199822184130724557)
                ·
                  refine ⟨898248824933319049021709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2395330199822184130724557 898248824933319049021709)
                  ·
                    refine ⟨336843309349994643383141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898248824933319049021709 336843309349994643383141)
                    ·
                      refine ⟨63158120503123995634339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 336843309349994643383141 63158120503123995634339)
                      ·
                        rfl

theorem cell23_123000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_123000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123000 prefixEnd_123000 := by exact prefixLift 123000
  have htrace : WordTrace (prefixWord ++ tailWord_123000) baseStart_123000 baseEnd_123000 := by
    simpa [prefixWord, tailWord_123000, baseEnd_123000] using wordTrace_append hprefix tailTrace_123000
  have hstable : (prefixWord ++ tailWord_123000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123000).length < 2 ^ (prefixWord ++ tailWord_123000).sum := by decide
  have hdescent : baseEnd_123000 < baseStart_123000 := by decide
  rcases family_descends (prefixWord ++ tailWord_123000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123001 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 5]
def baseStart_123001 : Nat := 118140960795 + 123001 * 2 ^ 59
def prefixEnd_123001 : Nat := 4983230072969 + 3 ^ 40 * 123001 * 2
def baseEnd_123001 : Nat := 7017625998197610191315

theorem tailTrace_123001 : CollatzResearch.WordTrace tailWord_123001 prefixEnd_123001 7017625998197610191315 := by
  unfold tailWord_123001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486215027395858743464857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2990810018263905828976571 4486215027395858743464857)
  ·
    refine ⟨3364661270546894057598643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4486215027395858743464857 3364661270546894057598643)
    ·
      refine ⟨5046991905820341086397965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364661270546894057598643 5046991905820341086397965)
      ·
        refine ⟨1892621964682627907399237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5046991905820341086397965 1892621964682627907399237)
        ·
          refine ⟨354866618377992732637357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1892621964682627907399237 354866618377992732637357)
          ·
            refine ⟨133074981891747274739009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354866618377992732637357 133074981891747274739009)
            ·
              refine ⟨99806236418810456054257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133074981891747274739009 99806236418810456054257)
              ·
                refine ⟨74854677314107842040693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99806236418810456054257 74854677314107842040693)
                ·
                  refine ⟨7017625998197610191315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74854677314107842040693 7017625998197610191315)
                  ·
                    rfl

theorem cell23_123001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 5].length) (baseStart_123001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123001 prefixEnd_123001 := by exact prefixLift 123001
  have htrace : WordTrace (prefixWord ++ tailWord_123001) baseStart_123001 baseEnd_123001 := by
    simpa [prefixWord, tailWord_123001, baseEnd_123001] using wordTrace_append hprefix tailTrace_123001
  have hstable : (prefixWord ++ tailWord_123001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123001).length < 2 ^ (prefixWord ++ tailWord_123001).sum := by decide
  have hdescent : baseEnd_123001 < baseStart_123001 := by decide
  rcases family_descends (prefixWord ++ tailWord_123001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123031 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 2, 5]
def baseStart_123031 : Nat := 118140960795 + 123031 * 2 ^ 59
def prefixEnd_123031 : Nat := 4983230072969 + 3 ^ 40 * 123031 * 2
def baseEnd_123031 : Nat := 21058012801137791448899

theorem tailTrace_123031 : CollatzResearch.WordTrace tailWord_123031 prefixEnd_123031 21058012801137791448899 := by
  unfold tailWord_123031
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487309217287173867056947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2991539478191449244704631 4487309217287173867056947)
  ·
    refine ⟨6730963825930760800585421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487309217287173867056947 6730963825930760800585421)
    ·
      refine ⟨2524111434724035300219533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6730963825930760800585421 2524111434724035300219533)
      ·
        refine ⟨946541788021513237582325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524111434724035300219533 946541788021513237582325)
        ·
          refine ⟨88738292627016866023343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 946541788021513237582325 88738292627016866023343)
          ·
            refine ⟨133107438940525299035015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88738292627016866023343 133107438940525299035015)
            ·
              refine ⟨199661158410787948552523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133107438940525299035015 199661158410787948552523)
              ·
                refine ⟨299491737616181922828785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199661158410787948552523 299491737616181922828785)
                ·
                  refine ⟨224618803212136442121589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299491737616181922828785 224618803212136442121589)
                  ·
                    refine ⟨21058012801137791448899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224618803212136442121589 21058012801137791448899)
                    ·
                      rfl

theorem cell23_123031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_123031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123031 prefixEnd_123031 := by exact prefixLift 123031
  have htrace : WordTrace (prefixWord ++ tailWord_123031) baseStart_123031 baseEnd_123031 := by
    simpa [prefixWord, tailWord_123031, baseEnd_123031] using wordTrace_append hprefix tailTrace_123031
  have hstable : (prefixWord ++ tailWord_123031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123031).length < 2 ^ (prefixWord ++ tailWord_123031).sum := by decide
  have hdescent : baseEnd_123031 < baseStart_123031 := by decide
  rcases family_descends (prefixWord ++ tailWord_123031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123034 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_123034 : Nat := 118140960795 + 123034 * 2 ^ 59
def prefixEnd_123034 : Nat := 4983230072969 + 3 ^ 40 * 123034 * 2
def baseEnd_123034 : Nat := 63175578845376862609183

theorem tailTrace_123034 : CollatzResearch.WordTrace tailWord_123034 prefixEnd_123034 63175578845376862609183 := by
  unfold tailWord_123034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121854659069076344854039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2991612424184203586277437 1121854659069076344854039)
  ·
    refine ⟨1682781988603614517281059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121854659069076344854039 1682781988603614517281059)
    ·
      refine ⟨2524172982905421775921589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682781988603614517281059 2524172982905421775921589)
      ·
        refine ⟨236641217147383291492649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2524172982905421775921589 236641217147383291492649)
        ·
          refine ⟨177480912860537468619487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236641217147383291492649 177480912860537468619487)
          ·
            refine ⟨266221369290806202929231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177480912860537468619487 266221369290806202929231)
            ·
              refine ⟨399332053936209304393847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266221369290806202929231 399332053936209304393847)
              ·
                refine ⟨598998080904313956590771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399332053936209304393847 598998080904313956590771)
                ·
                  refine ⟨898497121356470934886157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598998080904313956590771 898497121356470934886157)
                  ·
                    refine ⟨336936420508676600582309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898497121356470934886157 336936420508676600582309)
                    ·
                      refine ⟨63175578845376862609183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 336936420508676600582309 63175578845376862609183)
                      ·
                        rfl

theorem cell23_123034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_123034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123034 prefixEnd_123034 := by exact prefixLift 123034
  have htrace : WordTrace (prefixWord ++ tailWord_123034) baseStart_123034 baseEnd_123034 := by
    simpa [prefixWord, tailWord_123034, baseEnd_123034] using wordTrace_append hprefix tailTrace_123034
  have hstable : (prefixWord ++ tailWord_123034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123034).length < 2 ^ (prefixWord ++ tailWord_123034).sum := by decide
  have hdescent : baseEnd_123034 < baseStart_123034 := by decide
  rcases family_descends (prefixWord ++ tailWord_123034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123111 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_123111 : Nat := 118140960795 + 123111 * 2 ^ 59
def prefixEnd_123111 : Nat := 4983230072969 + 3 ^ 40 * 123111 * 2
def baseEnd_123111 : Nat := 63215116855773061346329

theorem tailTrace_123111 : CollatzResearch.WordTrace tailWord_123111 prefixEnd_123111 63215116855773061346329 := by
  unfold tailWord_123111
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490227056997347529969187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2993484704664898353312791 4490227056997347529969187)
  ·
    refine ⟨6735340585496021294953781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490227056997347529969187 6735340585496021294953781)
    ·
      refine ⟨631438179890251996401917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6735340585496021294953781 631438179890251996401917)
      ·
        refine ⟨236789317458844498650719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631438179890251996401917 236789317458844498650719)
        ·
          refine ⟨355183976188266747976079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236789317458844498650719 355183976188266747976079)
          ·
            refine ⟨532775964282400121964119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355183976188266747976079 532775964282400121964119)
            ·
              refine ⟨799163946423600182946179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532775964282400121964119 799163946423600182946179)
              ·
                refine ⟨1198745919635400274419269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799163946423600182946179 1198745919635400274419269)
                ·
                  refine ⟨224764859931637551453613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198745919635400274419269 224764859931637551453613)
                  ·
                    refine ⟨84286822474364081795105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224764859931637551453613 84286822474364081795105)
                    ·
                      refine ⟨63215116855773061346329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84286822474364081795105 63215116855773061346329)
                      ·
                        rfl

theorem cell23_123111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_123111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123111 prefixEnd_123111 := by exact prefixLift 123111
  have htrace : WordTrace (prefixWord ++ tailWord_123111) baseStart_123111 baseEnd_123111 := by
    simpa [prefixWord, tailWord_123111, baseEnd_123111] using wordTrace_append hprefix tailTrace_123111
  have hstable : (prefixWord ++ tailWord_123111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123111).length < 2 ^ (prefixWord ++ tailWord_123111).sum := by decide
  have hdescent : baseEnd_123111 < baseStart_123111 := by decide
  rcases family_descends (prefixWord ++ tailWord_123111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123134 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_123134 : Nat := 118140960795 + 123134 * 2 ^ 59
def prefixEnd_123134 : Nat := 4983230072969 + 3 ^ 40 * 123134 * 2
def baseEnd_123134 : Nat := 21075642303608823786241

theorem tailTrace_123134 : CollatzResearch.WordTrace tailWord_123134 prefixEnd_123134 21075642303608823786241 := by
  unfold tailWord_123134
  simp only [CollatzResearch.WordTrace]
  refine ⟨561383241989252807257057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2994043957276014972037637 561383241989252807257057)
  ·
    refine ⟨421037431491939605442793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 561383241989252807257057 421037431491939605442793)
    ·
      refine ⟨315778073618954704082095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421037431491939605442793 315778073618954704082095)
      ·
        refine ⟨473667110428432056123143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315778073618954704082095 473667110428432056123143)
        ·
          refine ⟨710500665642648084184715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473667110428432056123143 710500665642648084184715)
          ·
            refine ⟨1065750998463972126277073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710500665642648084184715 1065750998463972126277073)
            ·
              refine ⟨799313248847979094707805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065750998463972126277073 799313248847979094707805)
              ·
                refine ⟨299742468317992160515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799313248847979094707805 299742468317992160515427)
                ·
                  refine ⟨449613702476988240773141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299742468317992160515427 449613702476988240773141)
                  ·
                    refine ⟨21075642303608823786241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 449613702476988240773141 21075642303608823786241)
                    ·
                      rfl

theorem cell23_123134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_123134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123134 prefixEnd_123134 := by exact prefixLift 123134
  have htrace : WordTrace (prefixWord ++ tailWord_123134) baseStart_123134 baseEnd_123134 := by
    simpa [prefixWord, tailWord_123134, baseEnd_123134] using wordTrace_append hprefix tailTrace_123134
  have hstable : (prefixWord ++ tailWord_123134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123134).length < 2 ^ (prefixWord ++ tailWord_123134).sum := by decide
  have hdescent : baseEnd_123134 < baseStart_123134 := by decide
  rcases family_descends (prefixWord ++ tailWord_123134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123137 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_123137 : Nat := 118140960795 + 123137 * 2 ^ 59
def prefixEnd_123137 : Nat := 4983230072969 + 3 ^ 40 * 123137 * 2
def baseEnd_123137 : Nat := 63228467352789959621209

theorem tailTrace_123137 : CollatzResearch.WordTrace tailWord_123137 prefixEnd_123137 63228467352789959621209 := by
  unfold tailWord_123137
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491175354903153970415665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2994116903268769313610443 4491175354903153970415665)
  ·
    refine ⟨3368381516177365477811749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4491175354903153970415665 3368381516177365477811749)
    ·
      refine ⟨631571534283256027089703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3368381516177365477811749 631571534283256027089703)
      ·
        refine ⟨947357301424884040634555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631571534283256027089703 947357301424884040634555)
        ·
          refine ⟨1421035952137326060951833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947357301424884040634555 1421035952137326060951833)
          ·
            refine ⟨1065776964102994545713875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421035952137326060951833 1065776964102994545713875)
            ·
              refine ⟨1598665446154491818570813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065776964102994545713875 1598665446154491818570813)
              ·
                refine ⟨599499542307934431964055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598665446154491818570813 599499542307934431964055)
                ·
                  refine ⟨899249313461901647946083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599499542307934431964055 899249313461901647946083)
                  ·
                    refine ⟨1348873970192852471919125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 899249313461901647946083 1348873970192852471919125)
                    ·
                      refine ⟨63228467352789959621209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1348873970192852471919125 63228467352789959621209)
                      ·
                        rfl

theorem cell23_123137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_123137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123137 prefixEnd_123137 := by exact prefixLift 123137
  have htrace : WordTrace (prefixWord ++ tailWord_123137) baseStart_123137 baseEnd_123137 := by
    simpa [prefixWord, tailWord_123137, baseEnd_123137] using wordTrace_append hprefix tailTrace_123137
  have hstable : (prefixWord ++ tailWord_123137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123137).length < 2 ^ (prefixWord ++ tailWord_123137).sum := by decide
  have hdescent : baseEnd_123137 < baseStart_123137 := by decide
  rcases family_descends (prefixWord ++ tailWord_123137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123138 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_123138 : Nat := 118140960795 + 123138 * 2 ^ 59
def prefixEnd_123138 : Nat := 4983230072969 + 3 ^ 40 * 123138 * 2
def baseEnd_123138 : Nat := 21076326944481485236235

theorem tailTrace_123138 : CollatzResearch.WordTrace tailWord_123138 prefixEnd_123138 21076326944481485236235 := by
  unfold tailWord_123138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122802956974882785300517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2994141218599687427468045 1122802956974882785300517)
  ·
    refine ⟨210525554432790522243847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1122802956974882785300517 210525554432790522243847)
    ·
      refine ⟨315788331649185783365771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210525554432790522243847 315788331649185783365771)
      ·
        refine ⟨473682497473778675048657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315788331649185783365771 473682497473778675048657)
        ·
          refine ⟨355261873105334006286493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473682497473778675048657 355261873105334006286493)
          ·
            refine ⟨133223202414500252357435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355261873105334006286493 133223202414500252357435)
            ·
              refine ⟨199834803621750378536153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133223202414500252357435 199834803621750378536153)
              ·
                refine ⟨149876102716312783902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199834803621750378536153 149876102716312783902115)
                ·
                  refine ⟨224814154074469175853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149876102716312783902115 224814154074469175853173)
                  ·
                    refine ⟨21076326944481485236235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224814154074469175853173 21076326944481485236235)
                    ·
                      rfl

theorem cell23_123138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_123138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123138 prefixEnd_123138 := by exact prefixLift 123138
  have htrace : WordTrace (prefixWord ++ tailWord_123138) baseStart_123138 baseEnd_123138 := by
    simpa [prefixWord, tailWord_123138, baseEnd_123138] using wordTrace_append hprefix tailTrace_123138
  have hstable : (prefixWord ++ tailWord_123138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123138).length < 2 ^ (prefixWord ++ tailWord_123138).sum := by decide
  have hdescent : baseEnd_123138 < baseStart_123138 := by decide
  rcases family_descends (prefixWord ++ tailWord_123138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123207 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 8]
def baseStart_123207 : Nat := 118140960795 + 123207 * 2 ^ 59
def prefixEnd_123207 : Nat := 4983230072969 + 3 ^ 40 * 123207 * 2
def baseEnd_123207 : Nat := 21088136999534895248629

theorem tailTrace_123207 : CollatzResearch.WordTrace tailWord_123207 prefixEnd_123207 21088136999534895248629 := by
  unfold tailWord_123207
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493728464649555925463875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2995818976433037283642583 4493728464649555925463875)
  ·
    refine ⟨6740592696974333888195813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493728464649555925463875 6740592696974333888195813)
    ·
      refine ⟨1263861130682687604036715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6740592696974333888195813 1263861130682687604036715)
      ·
        refine ⟨1895791696024031406055073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263861130682687604036715 1895791696024031406055073)
        ·
          refine ⟨1421843772018023554541305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895791696024031406055073 1421843772018023554541305)
          ·
            refine ⟨1066382829013517665905979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421843772018023554541305 1066382829013517665905979)
            ·
              refine ⟨1599574243520276498858969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066382829013517665905979 1599574243520276498858969)
              ·
                refine ⟨1199680682640207374144227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599574243520276498858969 1199680682640207374144227)
                ·
                  refine ⟨1799521023960311061216341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199680682640207374144227 1799521023960311061216341)
                  ·
                    refine ⟨21088136999534895248629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1799521023960311061216341 21088136999534895248629)
                    ·
                      rfl

theorem cell23_123207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_123207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123207 prefixEnd_123207 := by exact prefixLift 123207
  have htrace : WordTrace (prefixWord ++ tailWord_123207) baseStart_123207 baseEnd_123207 := by
    simpa [prefixWord, tailWord_123207, baseEnd_123207] using wordTrace_append hprefix tailTrace_123207
  have hstable : (prefixWord ++ tailWord_123207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123207).length < 2 ^ (prefixWord ++ tailWord_123207).sum := by decide
  have hdescent : baseEnd_123207 < baseStart_123207 := by decide
  rcases family_descends (prefixWord ++ tailWord_123207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123248 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2]
def baseStart_123248 : Nat := 118140960795 + 123248 * 2 ^ 59
def prefixEnd_123248 : Nat := 4983230072969 + 3 ^ 40 * 123248 * 2
def baseEnd_123248 : Nat := 63285463705439025333199

theorem tailTrace_123248 : CollatzResearch.WordTrace tailWord_123248 prefixEnd_123248 63285463705439025333199 := by
  unfold tailWord_123248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247611928750509963853199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2996815905000679951804265 2247611928750509963853199)
  ·
    refine ⟨3371417893125764945779799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247611928750509963853199 3371417893125764945779799)
    ·
      refine ⟨5057126839688647418669699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371417893125764945779799 5057126839688647418669699)
      ·
        refine ⟨7585690259532971128004549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057126839688647418669699 7585690259532971128004549)
        ·
          refine ⟨1422316923662432086500853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7585690259532971128004549 1422316923662432086500853)
          ·
            refine ⟨133342211593353008109455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1422316923662432086500853 133342211593353008109455)
            ·
              refine ⟨200013317390029512164183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133342211593353008109455 200013317390029512164183)
              ·
                refine ⟨300019976085044268246275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200013317390029512164183 300019976085044268246275)
                ·
                  refine ⟨450029964127566402369413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300019976085044268246275 450029964127566402369413)
                  ·
                    refine ⟨84380618273918700444265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450029964127566402369413 84380618273918700444265)
                    ·
                      refine ⟨63285463705439025333199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84380618273918700444265 63285463705439025333199)
                      ·
                        rfl

theorem cell23_123248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2].length) (baseStart_123248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123248 prefixEnd_123248 := by exact prefixLift 123248
  have htrace : WordTrace (prefixWord ++ tailWord_123248) baseStart_123248 baseEnd_123248 := by
    simpa [prefixWord, tailWord_123248, baseEnd_123248] using wordTrace_append hprefix tailTrace_123248
  have hstable : (prefixWord ++ tailWord_123248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123248).length < 2 ^ (prefixWord ++ tailWord_123248).sum := by decide
  have hdescent : baseEnd_123248 < baseStart_123248 := by decide
  rcases family_descends (prefixWord ++ tailWord_123248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123321 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_123321 : Nat := 118140960795 + 123321 * 2 ^ 59
def prefixEnd_123321 : Nat := 4983230072969 + 3 ^ 40 * 123321 * 2
def baseEnd_123321 : Nat := 63322947793217239720363

theorem tailTrace_123321 : CollatzResearch.WordTrace tailWord_123321 prefixEnd_123321 63322947793217239720363 := by
  unfold tailWord_123321
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497886386236553395113817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2998590924157702263409211 4497886386236553395113817)
  ·
    refine ⟨3373414789677415046335363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4497886386236553395113817 3373414789677415046335363)
    ·
      refine ⟨5060122184516122569503045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373414789677415046335363 5060122184516122569503045)
      ·
        refine ⟨948772909596772981781821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5060122184516122569503045 948772909596772981781821)
        ·
          refine ⟨355789841098789868168183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 948772909596772981781821 355789841098789868168183)
          ·
            refine ⟨533684761648184802252275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355789841098789868168183 533684761648184802252275)
            ·
              refine ⟨800527142472277203378413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533684761648184802252275 800527142472277203378413)
              ·
                refine ⟨300197678427103951266905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 800527142472277203378413 300197678427103951266905)
                ·
                  refine ⟨225148258820327963450179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300197678427103951266905 225148258820327963450179)
                  ·
                    refine ⟨337722388230491945175269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225148258820327963450179 337722388230491945175269)
                    ·
                      refine ⟨63322947793217239720363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 337722388230491945175269 63322947793217239720363)
                      ·
                        rfl

theorem cell23_123321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_123321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123321 prefixEnd_123321 := by exact prefixLift 123321
  have htrace : WordTrace (prefixWord ++ tailWord_123321) baseStart_123321 baseEnd_123321 := by
    simpa [prefixWord, tailWord_123321, baseEnd_123321] using wordTrace_append hprefix tailTrace_123321
  have hstable : (prefixWord ++ tailWord_123321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123321).length < 2 ^ (prefixWord ++ tailWord_123321).sum := by decide
  have hdescent : baseEnd_123321 < baseStart_123321 := by decide
  rcases family_descends (prefixWord ++ tailWord_123321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123391 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 1, 5]
def baseStart_123391 : Nat := 118140960795 + 123391 * 2 ^ 59
def prefixEnd_123391 : Nat := 4983230072969 + 3 ^ 40 * 123391 * 2
def baseEnd_123391 : Nat := 21119630479677321948347

theorem tailTrace_123391 : CollatzResearch.WordTrace tailWord_123391 prefixEnd_123391 21119630479677321948347 := by
  unfold tailWord_123391
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500439495982955350162027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3000292997321970233441351 4500439495982955350162027)
  ·
    refine ⟨6750659243974433025243041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4500439495982955350162027 6750659243974433025243041)
    ·
      refine ⟨5062994432980824768932281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6750659243974433025243041 5062994432980824768932281)
      ·
        refine ⟨3797245824735618576699211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062994432980824768932281 3797245824735618576699211)
        ·
          refine ⟨5695868737103427865048817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797245824735618576699211 5695868737103427865048817)
          ·
            refine ⟨4271901552827570898786613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695868737103427865048817 4271901552827570898786613)
            ·
              refine ⟨400490770577584771761245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4271901552827570898786613 400490770577584771761245)
              ·
                refine ⟨150184038966594289410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400490770577584771761245 150184038966594289410467)
                ·
                  refine ⟨225276058449891434115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150184038966594289410467 225276058449891434115701)
                  ·
                    refine ⟨21119630479677321948347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225276058449891434115701 21119630479677321948347)
                    ·
                      rfl

theorem cell23_123391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_123391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123391 prefixEnd_123391 := by exact prefixLift 123391
  have htrace : WordTrace (prefixWord ++ tailWord_123391) baseStart_123391 baseEnd_123391 := by
    simpa [prefixWord, tailWord_123391, baseEnd_123391] using wordTrace_append hprefix tailTrace_123391
  have hstable : (prefixWord ++ tailWord_123391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123391).length < 2 ^ (prefixWord ++ tailWord_123391).sum := by decide
  have hdescent : baseEnd_123391 < baseStart_123391 := by decide
  rcases family_descends (prefixWord ++ tailWord_123391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123441 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_123441 : Nat := 118140960795 + 123441 * 2 ^ 59
def prefixEnd_123441 : Nat := 4983230072969 + 3 ^ 40 * 123441 * 2
def baseEnd_123441 : Nat := 63384565471756770219811

theorem tailTrace_123441 : CollatzResearch.WordTrace tailWord_123441 prefixEnd_123441 63384565471756770219811 := by
  unfold tailWord_123441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502263145801813889482177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3001508763867875926321451 4502263145801813889482177)
  ·
    refine ⟨3376697359351360417111633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4502263145801813889482177 3376697359351360417111633)
    ·
      refine ⟨2532523019513520312833725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376697359351360417111633 2532523019513520312833725)
      ·
        refine ⟨949696132317570117312647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2532523019513520312833725 949696132317570117312647)
        ·
          refine ⟨1424544198476355175968971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949696132317570117312647 1424544198476355175968971)
          ·
            refine ⟨2136816297714532763953457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424544198476355175968971 2136816297714532763953457)
            ·
              refine ⟨1602612223285899572965093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136816297714532763953457 1602612223285899572965093)
              ·
                refine ⟨300489791866106169930955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1602612223285899572965093 300489791866106169930955)
                ·
                  refine ⟨450734687799159254896433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300489791866106169930955 450734687799159254896433)
                  ·
                    refine ⟨338051015849369441172325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450734687799159254896433 338051015849369441172325)
                    ·
                      refine ⟨63384565471756770219811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 338051015849369441172325 63384565471756770219811)
                      ·
                        rfl

theorem cell23_123441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_123441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123441 prefixEnd_123441 := by exact prefixLift 123441
  have htrace : WordTrace (prefixWord ++ tailWord_123441) baseStart_123441 baseEnd_123441 := by
    simpa [prefixWord, tailWord_123441, baseEnd_123441] using wordTrace_append hprefix tailTrace_123441
  have hstable : (prefixWord ++ tailWord_123441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123441).length < 2 ^ (prefixWord ++ tailWord_123441).sum := by decide
  have hdescent : baseEnd_123441 < baseStart_123441 := by decide
  rcases family_descends (prefixWord ++ tailWord_123441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123448 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_123448 : Nat := 118140960795 + 123448 * 2 ^ 59
def prefixEnd_123448 : Nat := 4983230072969 + 3 ^ 40 * 123448 * 2
def baseEnd_123448 : Nat := 63388159836338242832279

theorem tailTrace_123448 : CollatzResearch.WordTrace tailWord_123448 prefixEnd_123448 63388159836338242832279 := by
  unfold tailWord_123448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251259228388227042493499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3001678971184302723324665 2251259228388227042493499)
  ·
    refine ⟨3376888842582340563740249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251259228388227042493499 3376888842582340563740249)
    ·
      refine ⟨2532666631936755422805187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376888842582340563740249 2532666631936755422805187)
      ·
        refine ⟨3798999947905133134207781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532666631936755422805187 3798999947905133134207781)
        ·
          refine ⟨712312490232212462663959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3798999947905133134207781 712312490232212462663959)
          ·
            refine ⟨1068468735348318693995939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712312490232212462663959 1068468735348318693995939)
            ·
              refine ⟨1602703103022478040993909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068468735348318693995939 1602703103022478040993909)
              ·
                refine ⟨150253415908357316343179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1602703103022478040993909 150253415908357316343179)
                ·
                  refine ⟨225380123862535974514769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150253415908357316343179 225380123862535974514769)
                  ·
                    refine ⟨169035092896901980886077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225380123862535974514769 169035092896901980886077)
                    ·
                      refine ⟨63388159836338242832279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 169035092896901980886077 63388159836338242832279)
                      ·
                        rfl

theorem cell23_123448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_123448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123448 prefixEnd_123448 := by exact prefixLift 123448
  have htrace : WordTrace (prefixWord ++ tailWord_123448) baseStart_123448 baseEnd_123448 := by
    simpa [prefixWord, tailWord_123448, baseEnd_123448] using wordTrace_append hprefix tailTrace_123448
  have hstable : (prefixWord ++ tailWord_123448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123448).length < 2 ^ (prefixWord ++ tailWord_123448).sum := by decide
  have hdescent : baseEnd_123448 < baseStart_123448 := by decide
  rcases family_descends (prefixWord ++ tailWord_123448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123569 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_123569 : Nat := 118140960795 + 123569 * 2 ^ 59
def prefixEnd_123569 : Nat := 4983230072969 + 3 ^ 40 * 123569 * 2
def baseEnd_123569 : Nat := 63450290995532269419223

theorem tailTrace_123569 : CollatzResearch.WordTrace tailWord_123569 prefixEnd_123569 63450290995532269419223 := by
  unfold tailWord_123569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506931689338091750141761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3004621126225394500094507 4506931689338091750141761)
  ·
    refine ⟨3380198767003568812606321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4506931689338091750141761 3380198767003568812606321)
    ·
      refine ⟨2535149075252676609454741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380198767003568812606321 2535149075252676609454741)
      ·
        refine ⟨118835112902469216068191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2535149075252676609454741 118835112902469216068191)
        ·
          refine ⟨178252669353703824102287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118835112902469216068191 178252669353703824102287)
          ·
            refine ⟨267379004030555736153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178252669353703824102287 267379004030555736153431)
            ·
              refine ⟨401068506045833604230147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267379004030555736153431 401068506045833604230147)
              ·
                refine ⟨601602759068750406345221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401068506045833604230147 601602759068750406345221)
                ·
                  refine ⟨112800517325390701189729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601602759068750406345221 112800517325390701189729)
                  ·
                    refine ⟨84600387994043025892297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112800517325390701189729 84600387994043025892297)
                    ·
                      refine ⟨63450290995532269419223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84600387994043025892297 63450290995532269419223)
                      ·
                        rfl

theorem cell23_123569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_123569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123569 prefixEnd_123569 := by exact prefixLift 123569
  have htrace : WordTrace (prefixWord ++ tailWord_123569) baseStart_123569 baseEnd_123569 := by
    simpa [prefixWord, tailWord_123569, baseEnd_123569] using wordTrace_append hprefix tailTrace_123569
  have hstable : (prefixWord ++ tailWord_123569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123569).length < 2 ^ (prefixWord ++ tailWord_123569).sum := by decide
  have hdescent : baseEnd_123569 < baseStart_123569 := by decide
  rcases family_descends (prefixWord ++ tailWord_123569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123588 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_123588 : Nat := 118140960795 + 123588 * 2 ^ 59
def prefixEnd_123588 : Nat := 4983230072969 + 3 ^ 40 * 123588 * 2
def baseEnd_123588 : Nat := 21153349042655898360545

theorem tailTrace_123588 : CollatzResearch.WordTrace tailWord_123588 prefixEnd_123588 21153349042655898360545 := by
  unfold tailWord_123588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253812338134628997541709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3005083117512838663388945 2253812338134628997541709)
  ·
    refine ⟨845179626800485874078141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2253812338134628997541709 845179626800485874078141)
    ·
      refine ⟨316942360050182202779303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 845179626800485874078141 316942360050182202779303)
      ·
        refine ⟨475413540075273304168955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316942360050182202779303 475413540075273304168955)
        ·
          refine ⟨713120310112909956253433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475413540075273304168955 713120310112909956253433)
          ·
            refine ⟨534840232584682467190075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713120310112909956253433 534840232584682467190075)
            ·
              refine ⟨802260348877023700785113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534840232584682467190075 802260348877023700785113)
              ·
                refine ⟨601695261657767775588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802260348877023700785113 601695261657767775588835)
                ·
                  refine ⟨902542892486651663383253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601695261657767775588835 902542892486651663383253)
                  ·
                    refine ⟨21153349042655898360545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 902542892486651663383253 21153349042655898360545)
                    ·
                      rfl

theorem cell23_123588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_123588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123588 prefixEnd_123588 := by exact prefixLift 123588
  have htrace : WordTrace (prefixWord ++ tailWord_123588) baseStart_123588 baseEnd_123588 := by
    simpa [prefixWord, tailWord_123588, baseEnd_123588] using wordTrace_append hprefix tailTrace_123588
  have hstable : (prefixWord ++ tailWord_123588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123588).length < 2 ^ (prefixWord ++ tailWord_123588).sum := by decide
  have hdescent : baseEnd_123588 < baseStart_123588 := by decide
  rcases family_descends (prefixWord ++ tailWord_123588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123601 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_123601 : Nat := 118140960795 + 123601 * 2 ^ 59
def prefixEnd_123601 : Nat := 4983230072969 + 3 ^ 40 * 123601 * 2
def baseEnd_123601 : Nat := 21155574125492048073025

theorem tailTrace_123601 : CollatzResearch.WordTrace tailWord_123601 prefixEnd_123601 21155574125492048073025 := by
  unfold tailWord_123601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508098825222161215306657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3005399216814774143537771 4508098825222161215306657)
  ·
    refine ⟨3381074118916620911479993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4508098825222161215306657 3381074118916620911479993)
    ·
      refine ⟨2535805589187465683609995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381074118916620911479993 2535805589187465683609995)
      ·
        refine ⟨3803708383781198525414993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535805589187465683609995 3803708383781198525414993)
        ·
          refine ⟨2852781287835898894061245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803708383781198525414993 2852781287835898894061245)
          ·
            refine ⟨1069792982938462085272967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2852781287835898894061245 1069792982938462085272967)
            ·
              refine ⟨1604689474407693127909451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069792982938462085272967 1604689474407693127909451)
              ·
                refine ⟨2407034211611539691864177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604689474407693127909451 2407034211611539691864177)
                ·
                  refine ⟨1805275658708654768898133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407034211611539691864177 1805275658708654768898133)
                  ·
                    refine ⟨21155574125492048073025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1805275658708654768898133 21155574125492048073025)
                    ·
                      rfl

theorem cell23_123601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_123601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123601 prefixEnd_123601 := by exact prefixLift 123601
  have htrace : WordTrace (prefixWord ++ tailWord_123601) baseStart_123601 baseEnd_123601 := by
    simpa [prefixWord, tailWord_123601, baseEnd_123601] using wordTrace_append hprefix tailTrace_123601
  have hstable : (prefixWord ++ tailWord_123601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123601).length < 2 ^ (prefixWord ++ tailWord_123601).sum := by decide
  have hdescent : baseEnd_123601 < baseStart_123601 := by decide
  rcases family_descends (prefixWord ++ tailWord_123601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123608 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_123608 : Nat := 118140960795 + 123608 * 2 ^ 59
def prefixEnd_123608 : Nat := 4983230072969 + 3 ^ 40 * 123608 * 2
def baseEnd_123608 : Nat := 63470316741057616831543

theorem tailTrace_123608 : CollatzResearch.WordTrace tailWord_123608 prefixEnd_123608 63470316741057616831543 := by
  unfold tailWord_123608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254177068098400705405739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3005569424131200940540985 2254177068098400705405739)
  ·
    refine ⟨3381265602147601058108609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2254177068098400705405739 3381265602147601058108609)
    ·
      refine ⟨2535949201610700793581457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381265602147601058108609 2535949201610700793581457)
      ·
        refine ⟨1901961901208025595186093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535949201610700793581457 1901961901208025595186093)
        ·
          refine ⟨713235712953009598194785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901961901208025595186093 713235712953009598194785)
          ·
            refine ⟨534926784714757198646089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713235712953009598194785 534926784714757198646089)
            ·
              refine ⟨401195088536067898984567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534926784714757198646089 401195088536067898984567)
              ·
                refine ⟨601792632804101848476851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401195088536067898984567 601792632804101848476851)
                ·
                  refine ⟨902688949206152772715277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601792632804101848476851 902688949206152772715277)
                  ·
                    refine ⟨338508355952307289768229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902688949206152772715277 338508355952307289768229)
                    ·
                      refine ⟨63470316741057616831543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 338508355952307289768229 63470316741057616831543)
                      ·
                        rfl

theorem cell23_123608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_123608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123608 prefixEnd_123608 := by exact prefixLift 123608
  have htrace : WordTrace (prefixWord ++ tailWord_123608) baseStart_123608 baseEnd_123608 := by
    simpa [prefixWord, tailWord_123608, baseEnd_123608] using wordTrace_append hprefix tailTrace_123608
  have hstable : (prefixWord ++ tailWord_123608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123608).length < 2 ^ (prefixWord ++ tailWord_123608).sum := by decide
  have hdescent : baseEnd_123608 < baseStart_123608 := by decide
  rcases family_descends (prefixWord ++ tailWord_123608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123637 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_123637 : Nat := 118140960795 + 123637 * 2 ^ 59
def prefixEnd_123637 : Nat := 4983230072969 + 3 ^ 40 * 123637 * 2
def baseEnd_123637 : Nat := 63485207680038003368911

theorem tailTrace_123637 : CollatzResearch.WordTrace tailWord_123637 prefixEnd_123637 63485207680038003368911 := by
  unfold tailWord_123637
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509411853091739363617165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3006274568727826242411443 4509411853091739363617165)
  ·
    refine ⟨1691029444909402261356437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4509411853091739363617165 1691029444909402261356437)
    ·
      refine ⟨79267005230128231001083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1691029444909402261356437 79267005230128231001083)
      ·
        refine ⟨118900507845192346501625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79267005230128231001083 118900507845192346501625)
        ·
          refine ⟨89175380883894259876219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118900507845192346501625 89175380883894259876219)
          ·
            refine ⟨133763071325841389814329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89175380883894259876219 133763071325841389814329)
            ·
              refine ⟨100322303494381042360747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133763071325841389814329 100322303494381042360747)
              ·
                refine ⟨150483455241571563541121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100322303494381042360747 150483455241571563541121)
                ·
                  refine ⟨112862591431178672655841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150483455241571563541121 112862591431178672655841)
                  ·
                    refine ⟨84646943573384004491881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112862591431178672655841 84646943573384004491881)
                    ·
                      refine ⟨63485207680038003368911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84646943573384004491881 63485207680038003368911)
                      ·
                        rfl

theorem cell23_123637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_123637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123637 prefixEnd_123637 := by exact prefixLift 123637
  have htrace : WordTrace (prefixWord ++ tailWord_123637) baseStart_123637 baseEnd_123637 := by
    simpa [prefixWord, tailWord_123637, baseEnd_123637] using wordTrace_append hprefix tailTrace_123637
  have hstable : (prefixWord ++ tailWord_123637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123637).length < 2 ^ (prefixWord ++ tailWord_123637).sum := by decide
  have hdescent : baseEnd_123637 < baseStart_123637 := by decide
  rcases family_descends (prefixWord ++ tailWord_123637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123709 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_123709 : Nat := 118140960795 + 123709 * 2 ^ 59
def prefixEnd_123709 : Nat := 4983230072969 + 3 ^ 40 * 123709 * 2
def baseEnd_123709 : Nat := 63522178287161721668579

theorem tailTrace_123709 : CollatzResearch.WordTrace tailWord_123709 prefixEnd_123709 63522178287161721668579 := by
  unfold tailWord_123709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512037908830895660238181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3008025272553930440158787 4512037908830895660238181)
  ·
    refine ⟨846007107905792936294659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4512037908830895660238181 846007107905792936294659)
    ·
      refine ⟨1269010661858689404441989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846007107905792936294659 1269010661858689404441989)
      ·
        refine ⟨237939499098504263332873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1269010661858689404441989 237939499098504263332873)
        ·
          refine ⟨178454624323878197499655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237939499098504263332873 178454624323878197499655)
          ·
            refine ⟨267681936485817296249483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178454624323878197499655 267681936485817296249483)
            ·
              refine ⟨401522904728725944374225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267681936485817296249483 401522904728725944374225)
              ·
                refine ⟨301142178546544458280669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401522904728725944374225 301142178546544458280669)
                ·
                  refine ⟨112928316954954171855251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301142178546544458280669 112928316954954171855251)
                  ·
                    refine ⟨169392475432431257782877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112928316954954171855251 169392475432431257782877)
                    ·
                      refine ⟨63522178287161721668579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 169392475432431257782877 63522178287161721668579)
                      ·
                        rfl

theorem cell23_123709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_123709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123709 prefixEnd_123709 := by exact prefixLift 123709
  have htrace : WordTrace (prefixWord ++ tailWord_123709) baseStart_123709 baseEnd_123709 := by
    simpa [prefixWord, tailWord_123709, baseEnd_123709] using wordTrace_append hprefix tailTrace_123709
  have hstable : (prefixWord ++ tailWord_123709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123709).length < 2 ^ (prefixWord ++ tailWord_123709).sum := by decide
  have hdescent : baseEnd_123709 < baseStart_123709 := by decide
  rcases family_descends (prefixWord ++ tailWord_123709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123715 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 4]
def baseStart_123715 : Nat := 118140960795 + 123715 * 2 ^ 59
def prefixEnd_123715 : Nat := 4983230072969 + 3 ^ 40 * 123715 * 2
def baseEnd_123715 : Nat := 63525259171088698193551

theorem tailTrace_123715 : CollatzResearch.WordTrace tailWord_123715 prefixEnd_123715 63525259171088698193551 := by
  unfold tailWord_123715
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512256746809158684956599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3008171164539439123304399 4512256746809158684956599)
  ·
    refine ⟨6768385120213738027434899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512256746809158684956599 6768385120213738027434899)
    ·
      refine ⟨10152577680320607041152349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768385120213738027434899 10152577680320607041152349)
      ·
        refine ⟨3807216630120227640432131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10152577680320607041152349 3807216630120227640432131)
        ·
          refine ⟨5710824945180341460648197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807216630120227640432131 5710824945180341460648197)
          ·
            refine ⟨1070779677221314023871537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5710824945180341460648197 1070779677221314023871537)
            ·
              refine ⟨803084757915985517903653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070779677221314023871537 803084757915985517903653)
              ·
                refine ⟨150578392109247284606935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803084757915985517903653 150578392109247284606935)
                ·
                  refine ⟨225867588163870926910403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150578392109247284606935 225867588163870926910403)
                  ·
                    refine ⟨338801382245806390365605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225867588163870926910403 338801382245806390365605)
                    ·
                      refine ⟨63525259171088698193551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 338801382245806390365605 63525259171088698193551)
                      ·
                        rfl

theorem cell23_123715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_123715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123715 prefixEnd_123715 := by exact prefixLift 123715
  have htrace : WordTrace (prefixWord ++ tailWord_123715) baseStart_123715 baseEnd_123715 := by
    simpa [prefixWord, tailWord_123715, baseEnd_123715] using wordTrace_append hprefix tailTrace_123715
  have hstable : (prefixWord ++ tailWord_123715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123715).length < 2 ^ (prefixWord ++ tailWord_123715).sum := by decide
  have hdescent : baseEnd_123715 < baseStart_123715 := by decide
  rcases family_descends (prefixWord ++ tailWord_123715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123729 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_123729 : Nat := 118140960795 + 123729 * 2 ^ 59
def prefixEnd_123729 : Nat := 4983230072969 + 3 ^ 40 * 123729 * 2
def baseEnd_123729 : Nat := 21177482633417214472829

theorem tailTrace_123729 : CollatzResearch.WordTrace tailWord_123729 prefixEnd_123729 21177482633417214472829 := by
  unfold tailWord_123729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512767368758439075966241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3008511579172292717310827 4512767368758439075966241)
  ·
    refine ⟨3384575526568829306974681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512767368758439075966241 3384575526568829306974681)
    ·
      refine ⟨2538431644926621980231011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384575526568829306974681 2538431644926621980231011)
      ·
        refine ⟨3807647467389932970346517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538431644926621980231011 3807647467389932970346517)
        ·
          refine ⟨178483475033903107984993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3807647467389932970346517 178483475033903107984993)
          ·
            refine ⟨133862606275427330988745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178483475033903107984993 133862606275427330988745)
            ·
              refine ⟨100396954706570498241559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133862606275427330988745 100396954706570498241559)
              ·
                refine ⟨150595432059855747362339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100396954706570498241559 150595432059855747362339)
                ·
                  refine ⟨225893148089783621043509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150595432059855747362339 225893148089783621043509)
                  ·
                    refine ⟨21177482633417214472829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225893148089783621043509 21177482633417214472829)
                    ·
                      rfl

theorem cell23_123729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_123729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123729 prefixEnd_123729 := by exact prefixLift 123729
  have htrace : WordTrace (prefixWord ++ tailWord_123729) baseStart_123729 baseEnd_123729 := by
    simpa [prefixWord, tailWord_123729, baseEnd_123729] using wordTrace_append hprefix tailTrace_123729
  have hstable : (prefixWord ++ tailWord_123729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123729).length < 2 ^ (prefixWord ++ tailWord_123729).sum := by decide
  have hdescent : baseEnd_123729 < baseStart_123729 := by decide
  rcases family_descends (prefixWord ++ tailWord_123729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123738 : List Nat := [3, 1, 1, 2, 1, 5, 10]
def baseStart_123738 : Nat := 118140960795 + 123738 * 2 ^ 59
def prefixEnd_123738 : Nat := 4983230072969 + 3 ^ 40 * 123738 * 2
def baseEnd_123738 : Nat := 784408262051137138345

theorem tailTrace_123738 : CollatzResearch.WordTrace tailWord_123738 prefixEnd_123738 784408262051137138345 := by
  unfold tailWord_123738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128273906431458403260967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3008730417150555742029245 1128273906431458403260967)
  ·
    refine ⟨1692410859647187604891451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128273906431458403260967 1692410859647187604891451)
    ·
      refine ⟨2538616289470781407337177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692410859647187604891451 2538616289470781407337177)
      ·
        refine ⟨1903962217103086055502883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2538616289470781407337177 1903962217103086055502883)
        ·
          refine ⟨2855943325654629083254325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903962217103086055502883 2855943325654629083254325)
          ·
            refine ⟨267744686780121476555093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2855943325654629083254325 267744686780121476555093)
            ·
              refine ⟨784408262051137138345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 267744686780121476555093 784408262051137138345)
              ·
                rfl

theorem cell23_123738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 10].length) (baseStart_123738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123738 prefixEnd_123738 := by exact prefixLift 123738
  have htrace : WordTrace (prefixWord ++ tailWord_123738) baseStart_123738 baseEnd_123738 := by
    simpa [prefixWord, tailWord_123738, baseEnd_123738] using wordTrace_append hprefix tailTrace_123738
  have hstable : (prefixWord ++ tailWord_123738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123738).length < 2 ^ (prefixWord ++ tailWord_123738).sum := by decide
  have hdescent : baseEnd_123738 < baseStart_123738 := by decide
  rcases family_descends (prefixWord ++ tailWord_123738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123766 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_123766 : Nat := 118140960795 + 123766 * 2 ^ 59
def prefixEnd_123766 : Nat := 4983230072969 + 3 ^ 40 * 123766 * 2
def baseEnd_123766 : Nat := 63551446684467998655817

theorem tailTrace_123766 : CollatzResearch.WordTrace tailWord_123766 prefixEnd_123766 63551446684467998655817 := by
  unfold tailWord_123766
  simp only [CollatzResearch.WordTrace]
  refine ⟨282132304351524649691447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3009411246416262930042101 282132304351524649691447)
  ·
    refine ⟨423198456527286974537171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282132304351524649691447 423198456527286974537171)
    ·
      refine ⟨634797684790930461805757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423198456527286974537171 634797684790930461805757)
      ·
        refine ⟨238049131796598923177159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634797684790930461805757 238049131796598923177159)
        ·
          refine ⟨357073697694898384765739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238049131796598923177159 357073697694898384765739)
          ·
            refine ⟨535610546542347577148609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357073697694898384765739 535610546542347577148609)
            ·
              refine ⟨401707909906760682861457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535610546542347577148609 401707909906760682861457)
              ·
                refine ⟨301280932430070512146093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401707909906760682861457 301280932430070512146093)
                ·
                  refine ⟨112980349661276442054785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301280932430070512146093 112980349661276442054785)
                  ·
                    refine ⟨84735262245957331541089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112980349661276442054785 84735262245957331541089)
                    ·
                      refine ⟨63551446684467998655817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84735262245957331541089 63551446684467998655817)
                      ·
                        rfl

theorem cell23_123766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_123766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123766 prefixEnd_123766 := by exact prefixLift 123766
  have htrace : WordTrace (prefixWord ++ tailWord_123766) baseStart_123766 baseEnd_123766 := by
    simpa [prefixWord, tailWord_123766, baseEnd_123766] using wordTrace_append hprefix tailTrace_123766
  have hstable : (prefixWord ++ tailWord_123766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123766).length < 2 ^ (prefixWord ++ tailWord_123766).sum := by decide
  have hdescent : baseEnd_123766 < baseStart_123766 := by decide
  rcases family_descends (prefixWord ++ tailWord_123766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123783 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_123783 : Nat := 118140960795 + 123783 * 2 ^ 59
def prefixEnd_123783 : Nat := 4983230072969 + 3 ^ 40 * 123783 * 2
def baseEnd_123783 : Nat := 63560175855594432143239

theorem tailTrace_123783 : CollatzResearch.WordTrace tailWord_123783 prefixEnd_123783 63560175855594432143239 := by
  unfold tailWord_123783
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514736910562806298432003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3009824607041870865621335 4514736910562806298432003)
  ·
    refine ⟨6772105365844209447648005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4514736910562806298432003 6772105365844209447648005)
    ·
      refine ⟨1269769756095789271434001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6772105365844209447648005 1269769756095789271434001)
      ·
        refine ⟨952327317071841953575501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269769756095789271434001 952327317071841953575501)
        ·
          refine ⟨357122743901940732590813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952327317071841953575501 357122743901940732590813)
          ·
            refine ⟨133921028963227774721555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357122743901940732590813 133921028963227774721555)
            ·
              refine ⟨200881543444841662082333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133921028963227774721555 200881543444841662082333)
              ·
                refine ⟨75330578791815623280875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200881543444841662082333 75330578791815623280875)
                ·
                  refine ⟨112995868187723434921313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75330578791815623280875 112995868187723434921313)
                  ·
                    refine ⟨84746901140792576190985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112995868187723434921313 84746901140792576190985)
                    ·
                      refine ⟨63560175855594432143239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84746901140792576190985 63560175855594432143239)
                      ·
                        rfl

theorem cell23_123783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_123783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123783 prefixEnd_123783 := by exact prefixLift 123783
  have htrace : WordTrace (prefixWord ++ tailWord_123783) baseStart_123783 baseEnd_123783 := by
    simpa [prefixWord, tailWord_123783, baseEnd_123783] using wordTrace_append hprefix tailTrace_123783
  have hstable : (prefixWord ++ tailWord_123783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123783).length < 2 ^ (prefixWord ++ tailWord_123783).sum := by decide
  have hdescent : baseEnd_123783 < baseStart_123783 := by decide
  rcases family_descends (prefixWord ++ tailWord_123783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123805 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_123805 : Nat := 118140960795 + 123805 * 2 ^ 59
def prefixEnd_123805 : Nat := 4983230072969 + 3 ^ 40 * 123805 * 2
def baseEnd_123805 : Nat := 63571472429993346068137

theorem tailTrace_123805 : CollatzResearch.WordTrace tailWord_123805 prefixEnd_123805 63571472429993346068137 := by
  unfold tailWord_123805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515539316483104055732869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3010359544322069370488579 4515539316483104055732869)
  ·
    refine ⟨846663621840582010449913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4515539316483104055732869 846663621840582010449913)
    ·
      refine ⟨634997716380436507837435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 846663621840582010449913 634997716380436507837435)
      ·
        refine ⟨952496574570654761756153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634997716380436507837435 952496574570654761756153)
        ·
          refine ⟨714372430927991071317115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952496574570654761756153 714372430927991071317115)
          ·
            refine ⟨1071558646391986606975673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714372430927991071317115 1071558646391986606975673)
            ·
              refine ⟨803668984793989955231755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071558646391986606975673 803668984793989955231755)
              ·
                refine ⟨1205503477190984932847633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803668984793989955231755 1205503477190984932847633)
                ·
                  refine ⟨904127607893238699635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205503477190984932847633 904127607893238699635725)
                  ·
                    refine ⟨339047852959964512363397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904127607893238699635725 339047852959964512363397)
                    ·
                      refine ⟨63571472429993346068137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 339047852959964512363397 63571472429993346068137)
                      ·
                        rfl

theorem cell23_123805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_123805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123805 prefixEnd_123805 := by exact prefixLift 123805
  have htrace : WordTrace (prefixWord ++ tailWord_123805) baseStart_123805 baseEnd_123805 := by
    simpa [prefixWord, tailWord_123805, baseEnd_123805] using wordTrace_append hprefix tailTrace_123805
  have hstable : (prefixWord ++ tailWord_123805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123805).length < 2 ^ (prefixWord ++ tailWord_123805).sum := by decide
  have hdescent : baseEnd_123805 < baseStart_123805 := by decide
  rcases family_descends (prefixWord ++ tailWord_123805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123875 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 7]
def baseStart_123875 : Nat := 118140960795 + 123875 * 2 ^ 59
def prefixEnd_123875 : Nat := 4983230072969 + 3 ^ 40 * 123875 * 2
def baseEnd_123875 : Nat := 21202472025269357397605

theorem tailTrace_123875 : CollatzResearch.WordTrace tailWord_123875 prefixEnd_123875 21202472025269357397605 := by
  unfold tailWord_123875
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518092426229506010781079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3012061617486337340520719 4518092426229506010781079)
  ·
    refine ⟨6777138639344259016171619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518092426229506010781079 6777138639344259016171619)
    ·
      refine ⟨10165707959016388524257429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777138639344259016171619 10165707959016388524257429)
      ·
        refine ⟨476517560578893212074567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10165707959016388524257429 476517560578893212074567)
        ·
          refine ⟨714776340868339818111851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476517560578893212074567 714776340868339818111851)
          ·
            refine ⟨1072164511302509727167777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714776340868339818111851 1072164511302509727167777)
            ·
              refine ⟨804123383476882295375833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072164511302509727167777 804123383476882295375833)
              ·
                refine ⟨603092537607661721531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804123383476882295375833 603092537607661721531875)
                ·
                  refine ⟨904638806411492582297813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603092537607661721531875 904638806411492582297813)
                  ·
                    refine ⟨21202472025269357397605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 904638806411492582297813 21202472025269357397605)
                    ·
                      rfl

theorem cell23_123875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_123875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123875 prefixEnd_123875 := by exact prefixLift 123875
  have htrace : WordTrace (prefixWord ++ tailWord_123875) baseStart_123875 baseEnd_123875 := by
    simpa [prefixWord, tailWord_123875, baseEnd_123875] using wordTrace_append hprefix tailTrace_123875
  have hstable : (prefixWord ++ tailWord_123875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123875).length < 2 ^ (prefixWord ++ tailWord_123875).sum := by decide
  have hdescent : baseEnd_123875 < baseStart_123875 := by decide
  rcases family_descends (prefixWord ++ tailWord_123875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123966 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_123966 : Nat := 118140960795 + 123966 * 2 ^ 59
def prefixEnd_123966 : Nat := 4983230072969 + 3 ^ 40 * 123966 * 2
def baseEnd_123966 : Nat := 63654142815367216154897

theorem tailTrace_123966 : CollatzResearch.WordTrace tailWord_123966 prefixEnd_123966 63654142815367216154897 := by
  unfold tailWord_123966
  simp only [CollatzResearch.WordTrace]
  refine ⟨565176433612478569042969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3014274312599885701562501 565176433612478569042969)
  ·
    refine ⟨423882325209358926782227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 565176433612478569042969 423882325209358926782227)
    ·
      refine ⟨635823487814038390173341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423882325209358926782227 635823487814038390173341)
      ·
        refine ⟨238433807930264396315003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635823487814038390173341 238433807930264396315003)
        ·
          refine ⟨357650711895396594472505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238433807930264396315003 357650711895396594472505)
          ·
            refine ⟨268238033921547445854379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357650711895396594472505 268238033921547445854379)
            ·
              refine ⟨402357050882321168781569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268238033921547445854379 402357050882321168781569)
              ·
                refine ⟨301767788161740876586177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402357050882321168781569 301767788161740876586177)
                ·
                  refine ⟨226325841121305657439633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301767788161740876586177 226325841121305657439633)
                  ·
                    refine ⟨169744380840979243079725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226325841121305657439633 169744380840979243079725)
                    ·
                      refine ⟨63654142815367216154897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 169744380840979243079725 63654142815367216154897)
                      ·
                        rfl

theorem cell23_123966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_123966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123966 prefixEnd_123966 := by exact prefixLift 123966
  have htrace : WordTrace (prefixWord ++ tailWord_123966) baseStart_123966 baseEnd_123966 := by
    simpa [prefixWord, tailWord_123966, baseEnd_123966] using wordTrace_append hprefix tailTrace_123966
  have hstable : (prefixWord ++ tailWord_123966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123966).length < 2 ^ (prefixWord ++ tailWord_123966).sum := by decide
  have hdescent : baseEnd_123966 < baseStart_123966 := by decide
  rcases family_descends (prefixWord ++ tailWord_123966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123982 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_123982 : Nat := 118140960795 + 123982 * 2 ^ 59
def prefixEnd_123982 : Nat := 4983230072969 + 3 ^ 40 * 123982 * 2
def baseEnd_123982 : Nat := 21220786168613051184941

theorem tailTrace_123982 : CollatzResearch.WordTrace tailWord_123982 prefixEnd_123982 21220786168613051184941 := by
  unfold tailWord_123982
  simp only [CollatzResearch.WordTrace]
  refine ⟨565249379605232910615775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3014663357894575523284133 565249379605232910615775)
  ·
    refine ⟨847874069407849365923663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565249379605232910615775 847874069407849365923663)
    ·
      refine ⟨1271811104111774048885495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847874069407849365923663 1271811104111774048885495)
      ·
        refine ⟨1907716656167661073328243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271811104111774048885495 1907716656167661073328243)
        ·
          refine ⟨2861574984251491609992365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907716656167661073328243 2861574984251491609992365)
          ·
            refine ⟨1073090619094309353747137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2861574984251491609992365 1073090619094309353747137)
            ·
              refine ⟨804817964320732015310353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073090619094309353747137 804817964320732015310353)
              ·
                refine ⟨603613473240549011482765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804817964320732015310353 603613473240549011482765)
                ·
                  refine ⟨226355052465205879306037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603613473240549011482765 226355052465205879306037)
                  ·
                    refine ⟨21220786168613051184941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226355052465205879306037 21220786168613051184941)
                    ·
                      rfl

theorem cell23_123982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_123982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123982 prefixEnd_123982 := by exact prefixLift 123982
  have htrace : WordTrace (prefixWord ++ tailWord_123982) baseStart_123982 baseEnd_123982 := by
    simpa [prefixWord, tailWord_123982, baseEnd_123982] using wordTrace_append hprefix tailTrace_123982
  have hstable : (prefixWord ++ tailWord_123982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123982).length < 2 ^ (prefixWord ++ tailWord_123982).sum := by decide
  have hdescent : baseEnd_123982 < baseStart_123982 := by decide
  rcases family_descends (prefixWord ++ tailWord_123982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123986 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_123986 : Nat := 118140960795 + 123986 * 2 ^ 59
def prefixEnd_123986 : Nat := 4983230072969 + 3 ^ 40 * 123986 * 2
def baseEnd_123986 : Nat := 7073823603161904211645

theorem tailTrace_123986 : CollatzResearch.WordTrace tailWord_123986 prefixEnd_123986 7073823603161904211645 := by
  unfold tailWord_123986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130535232206842992017953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3014760619218247978714541 1130535232206842992017953)
  ·
    refine ⟨847901424155132244013465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1130535232206842992017953 847901424155132244013465)
    ·
      refine ⟨635926068116349183010099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 847901424155132244013465 635926068116349183010099)
      ·
        refine ⟨953889102174523774515149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635926068116349183010099 953889102174523774515149)
        ·
          refine ⟨357708413315446415443181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953889102174523774515149 357708413315446415443181)
          ·
            refine ⟨134140654993292405791193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357708413315446415443181 134140654993292405791193)
            ·
              refine ⟨100605491244969304343395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134140654993292405791193 100605491244969304343395)
              ·
                refine ⟨150908236867453956515093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100605491244969304343395 150908236867453956515093)
                ·
                  refine ⟨7073823603161904211645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150908236867453956515093 7073823603161904211645)
                  ·
                    rfl

theorem cell23_123986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_123986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123986 prefixEnd_123986 := by exact prefixLift 123986
  have htrace : WordTrace (prefixWord ++ tailWord_123986) baseStart_123986 baseEnd_123986 := by
    simpa [prefixWord, tailWord_123986, baseEnd_123986] using wordTrace_append hprefix tailTrace_123986
  have hstable : (prefixWord ++ tailWord_123986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123986).length < 2 ^ (prefixWord ++ tailWord_123986).sum := by decide
  have hdescent : baseEnd_123986 < baseStart_123986 := by decide
  rcases family_descends (prefixWord ++ tailWord_123986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123989 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_123989 : Nat := 118140960795 + 123989 * 2 ^ 59
def prefixEnd_123989 : Nat := 4983230072969 + 3 ^ 40 * 123989 * 2
def baseEnd_123989 : Nat := 63665952870420626167291

theorem tailTrace_123989 : CollatzResearch.WordTrace tailWord_123989 prefixEnd_123989 63665952870420626167291 := by
  unfold tailWord_123989
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522250347816503480431021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3014833565211002320287347 4522250347816503480431021)
  ·
    refine ⟨1695843880431188805161633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4522250347816503480431021 1695843880431188805161633)
    ·
      refine ⟨1271882910323391603871225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1695843880431188805161633 1271882910323391603871225)
      ·
        refine ⟨953912182742543702903419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271882910323391603871225 953912182742543702903419)
        ·
          refine ⟨1430868274113815554355129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953912182742543702903419 1430868274113815554355129)
          ·
            refine ⟨1073151205585361665766347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430868274113815554355129 1073151205585361665766347)
            ·
              refine ⟨1609726808378042498649521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073151205585361665766347 1609726808378042498649521)
              ·
                refine ⟨1207295106283531873987141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609726808378042498649521 1207295106283531873987141)
                ·
                  refine ⟨226367832428162226372589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207295106283531873987141 226367832428162226372589)
                  ·
                    refine ⟨84887937160560834889721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226367832428162226372589 84887937160560834889721)
                    ·
                      refine ⟨63665952870420626167291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 84887937160560834889721 63665952870420626167291)
                      ·
                        rfl

theorem cell23_123989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_123989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_123989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_123989 prefixEnd_123989 := by exact prefixLift 123989
  have htrace : WordTrace (prefixWord ++ tailWord_123989) baseStart_123989 baseEnd_123989 := by
    simpa [prefixWord, tailWord_123989, baseEnd_123989] using wordTrace_append hprefix tailTrace_123989
  have hstable : (prefixWord ++ tailWord_123989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123989).length < 2 ^ (prefixWord ++ tailWord_123989).sum := by decide
  have hdescent : baseEnd_123989 < baseStart_123989 := by decide
  rcases family_descends (prefixWord ++ tailWord_123989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124012 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_124012 : Nat := 118140960795 + 124012 * 2 ^ 59
def prefixEnd_124012 : Nat := 4983230072969 + 3 ^ 40 * 124012 * 2
def baseEnd_124012 : Nat := 21225920975158012059895

theorem tailTrace_124012 : CollatzResearch.WordTrace tailWord_124012 prefixEnd_124012 21225920975158012059895 := by
  unfold tailWord_124012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261544613366589204259145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3015392817822118939012193 2261544613366589204259145)
  ·
    refine ⟨1696158460024941903194359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261544613366589204259145 1696158460024941903194359)
    ·
      refine ⟨2544237690037412854791539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696158460024941903194359 2544237690037412854791539)
      ·
        refine ⟨3816356535056119282187309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544237690037412854791539 3816356535056119282187309)
        ·
          refine ⟨1431133700646044730820241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3816356535056119282187309 1431133700646044730820241)
          ·
            refine ⟨1073350275484533548115181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431133700646044730820241 1073350275484533548115181)
            ·
              refine ⟨402506353306700080543193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073350275484533548115181 402506353306700080543193)
              ·
                refine ⟨301879764980025060407395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402506353306700080543193 301879764980025060407395)
                ·
                  refine ⟨452819647470037590611093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301879764980025060407395 452819647470037590611093)
                  ·
                    refine ⟨21225920975158012059895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 452819647470037590611093 21225920975158012059895)
                    ·
                      rfl

theorem cell23_124012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_124012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124012 prefixEnd_124012 := by exact prefixLift 124012
  have htrace : WordTrace (prefixWord ++ tailWord_124012) baseStart_124012 baseEnd_124012 := by
    simpa [prefixWord, tailWord_124012, baseEnd_124012] using wordTrace_append hprefix tailTrace_124012
  have hstable : (prefixWord ++ tailWord_124012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124012).length < 2 ^ (prefixWord ++ tailWord_124012).sum := by decide
  have hdescent : baseEnd_124012 < baseStart_124012 := by decide
  rcases family_descends (prefixWord ++ tailWord_124012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124025 : List Nat := [1, 2, 1, 3, 16]
def baseStart_124025 : Nat := 118140960795 + 124025 * 2 ^ 59
def prefixEnd_124025 : Nat := 4983230072969 + 3 ^ 40 * 124025 * 2
def baseEnd_124025 : Nat := 87358625753062394125

theorem tailTrace_124025 : CollatzResearch.WordTrace tailWord_124025 prefixEnd_124025 87358625753062394125 := by
  unfold tailWord_124025
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523563375686081628741529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3015708917124054419161019 4523563375686081628741529)
  ·
    refine ⟨3392672531764561221556147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4523563375686081628741529 3392672531764561221556147)
    ·
      refine ⟨5089008797646841832334221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392672531764561221556147 5089008797646841832334221)
      ·
        refine ⟨1908378299117565687125333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5089008797646841832334221 1908378299117565687125333)
        ·
          refine ⟨87358625753062394125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 1908378299117565687125333 87358625753062394125)
          ·
            rfl

theorem cell23_124025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 16].length) (baseStart_124025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124025 prefixEnd_124025 := by exact prefixLift 124025
  have htrace : WordTrace (prefixWord ++ tailWord_124025) baseStart_124025 baseEnd_124025 := by
    simpa [prefixWord, tailWord_124025, baseEnd_124025] using wordTrace_append hprefix tailTrace_124025
  have hstable : (prefixWord ++ tailWord_124025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124025).length < 2 ^ (prefixWord ++ tailWord_124025).sum := by decide
  have hdescent : baseEnd_124025 < baseStart_124025 := by decide
  rcases family_descends (prefixWord ++ tailWord_124025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124046 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_124046 : Nat := 118140960795 + 124046 * 2 ^ 59
def prefixEnd_124046 : Nat := 4983230072969 + 3 ^ 40 * 124046 * 2
def baseEnd_124046 : Nat := 21231740422575634384843

theorem tailTrace_124046 : CollatzResearch.WordTrace tailWord_124046 prefixEnd_124046 21231740422575634384843 := by
  unfold tailWord_124046
  simp only [CollatzResearch.WordTrace]
  refine ⟨565541163576250276906999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3016219539073334810170661 565541163576250276906999)
  ·
    refine ⟨848311745364375415360499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565541163576250276906999 848311745364375415360499)
    ·
      refine ⟨1272467618046563123040749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848311745364375415360499 1272467618046563123040749)
      ·
        refine ⟨477175356767461171140281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1272467618046563123040749 477175356767461171140281)
        ·
          refine ⟨357881517575595878355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477175356767461171140281 357881517575595878355211)
          ·
            refine ⟨536822276363393817532817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357881517575595878355211 536822276363393817532817)
            ·
              refine ⟨402616707272545363149613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536822276363393817532817 402616707272545363149613)
              ·
                refine ⟨150981265227204511181105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402616707272545363149613 150981265227204511181105)
                ·
                  refine ⟨113235948920403383385829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150981265227204511181105 113235948920403383385829)
                  ·
                    refine ⟨21231740422575634384843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113235948920403383385829 21231740422575634384843)
                    ·
                      rfl

theorem cell23_124046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_124046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124046 prefixEnd_124046 := by exact prefixLift 124046
  have htrace : WordTrace (prefixWord ++ tailWord_124046) baseStart_124046 baseEnd_124046 := by
    simpa [prefixWord, tailWord_124046, baseEnd_124046] using wordTrace_append hprefix tailTrace_124046
  have hstable : (prefixWord ++ tailWord_124046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124046).length < 2 ^ (prefixWord ++ tailWord_124046).sum := by decide
  have hdescent : baseEnd_124046 < baseStart_124046 := by decide
  rcases family_descends (prefixWord ++ tailWord_124046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124069 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_124069 : Nat := 118140960795 + 124069 * 2 ^ 59
def prefixEnd_124069 : Nat := 4983230072969 + 3 ^ 40 * 124069 * 2
def baseEnd_124069 : Nat := 63707031322780313166923

theorem tailTrace_124069 : CollatzResearch.WordTrace tailWord_124069 prefixEnd_124069 63707031322780313166923 := by
  unfold tailWord_124069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525168187526677143343261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3016778791684451428895507 4525168187526677143343261)
  ·
    refine ⟨1696938070322503928753723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4525168187526677143343261 1696938070322503928753723)
    ·
      refine ⟨2545407105483755893130585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696938070322503928753723 2545407105483755893130585)
      ·
        refine ⟨1909055329112816919847939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545407105483755893130585 1909055329112816919847939)
        ·
          refine ⟨2863582993669225379771909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909055329112816919847939 2863582993669225379771909)
          ·
            refine ⟨536921811312979758707233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2863582993669225379771909 536921811312979758707233)
            ·
              refine ⟨402691358484734819030425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536921811312979758707233 402691358484734819030425)
              ·
                refine ⟨302018518863551114272819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402691358484734819030425 302018518863551114272819)
                ·
                  refine ⟨453027778295326671409229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302018518863551114272819 453027778295326671409229)
                  ·
                    refine ⟨169885416860747501778461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453027778295326671409229 169885416860747501778461)
                    ·
                      refine ⟨63707031322780313166923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 169885416860747501778461 63707031322780313166923)
                      ·
                        rfl

theorem cell23_124069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_124069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124069 prefixEnd_124069 := by exact prefixLift 124069
  have htrace : WordTrace (prefixWord ++ tailWord_124069) baseStart_124069 baseEnd_124069 := by
    simpa [prefixWord, tailWord_124069, baseEnd_124069] using wordTrace_append hprefix tailTrace_124069
  have hstable : (prefixWord ++ tailWord_124069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124069).length < 2 ^ (prefixWord ++ tailWord_124069).sum := by decide
  have hdescent : baseEnd_124069 < baseStart_124069 := by decide
  rcases family_descends (prefixWord ++ tailWord_124069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124129 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_124129 : Nat := 118140960795 + 124129 * 2 ^ 59
def prefixEnd_124129 : Nat := 4983230072969 + 3 ^ 40 * 124129 * 2
def baseEnd_124129 : Nat := 63737840162050078416647

theorem tailTrace_124129 : CollatzResearch.WordTrace tailWord_124129 prefixEnd_124129 63737840162050078416647 := by
  unfold tailWord_124129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527356567309307390527441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3018237711539538260351627 4527356567309307390527441)
  ·
    refine ⟨3395517425481980542895581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4527356567309307390527441 3395517425481980542895581)
    ·
      refine ⟨1273319034555742703585843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3395517425481980542895581 1273319034555742703585843)
      ·
        refine ⟨1909978551833614055378765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273319034555742703585843 1909978551833614055378765)
        ·
          refine ⟨716241956937605270767037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1909978551833614055378765 716241956937605270767037)
          ·
            refine ⟨268590733851601976537639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716241956937605270767037 268590733851601976537639)
            ·
              refine ⟨402886100777402964806459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268590733851601976537639 402886100777402964806459)
              ·
                refine ⟨604329151166104447209689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402886100777402964806459 604329151166104447209689)
                ·
                  refine ⟨453246863374578335407267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604329151166104447209689 453246863374578335407267)
                  ·
                    refine ⟨679870295061867503110901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 453246863374578335407267 679870295061867503110901)
                    ·
                      refine ⟨63737840162050078416647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 679870295061867503110901 63737840162050078416647)
                      ·
                        rfl

theorem cell23_124129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_124129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124129 prefixEnd_124129 := by exact prefixLift 124129
  have htrace : WordTrace (prefixWord ++ tailWord_124129) baseStart_124129 baseEnd_124129 := by
    simpa [prefixWord, tailWord_124129, baseEnd_124129] using wordTrace_append hprefix tailTrace_124129
  have hstable : (prefixWord ++ tailWord_124129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124129).length < 2 ^ (prefixWord ++ tailWord_124129).sum := by decide
  have hdescent : baseEnd_124129 < baseStart_124129 := by decide
  rcases family_descends (prefixWord ++ tailWord_124129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124132 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 9]
def baseStart_124132 : Nat := 118140960795 + 124132 * 2 ^ 59
def prefixEnd_124132 : Nat := 4983230072969 + 3 ^ 40 * 124132 * 2
def baseEnd_124132 : Nat := 7082153400445951853237

theorem tailTrace_124132 : CollatzResearch.WordTrace tailWord_124132 prefixEnd_124132 7082153400445951853237 := by
  unfold tailWord_124132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263732993149219451443325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3018310657532292601924433 2263732993149219451443325)
  ·
    refine ⟨848899872430957294291247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2263732993149219451443325 848899872430957294291247)
    ·
      refine ⟨1273349808646435941436871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848899872430957294291247 1273349808646435941436871)
      ·
        refine ⟨1910024712969653912155307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273349808646435941436871 1910024712969653912155307)
        ·
          refine ⟨2865037069454480868232961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910024712969653912155307 2865037069454480868232961)
          ·
            refine ⟨2148777802090860651174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2865037069454480868232961 2148777802090860651174721)
            ·
              refine ⟨1611583351568145488381041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148777802090860651174721 1611583351568145488381041)
              ·
                refine ⟨1208687513676109116285781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611583351568145488381041 1208687513676109116285781)
                ·
                  refine ⟨7082153400445951853237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1208687513676109116285781 7082153400445951853237)
                  ·
                    rfl

theorem cell23_124132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_124132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124132 prefixEnd_124132 := by exact prefixLift 124132
  have htrace : WordTrace (prefixWord ++ tailWord_124132) baseStart_124132 baseEnd_124132 := by
    simpa [prefixWord, tailWord_124132, baseEnd_124132] using wordTrace_append hprefix tailTrace_124132
  have hstable : (prefixWord ++ tailWord_124132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124132).length < 2 ^ (prefixWord ++ tailWord_124132).sum := by decide
  have hdescent : baseEnd_124132 < baseStart_124132 := by decide
  rcases family_descends (prefixWord ++ tailWord_124132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124200 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 5]
def baseStart_124200 : Nat := 118140960795 + 124200 * 2 ^ 59
def prefixEnd_124200 : Nat := 4983230072969 + 3 ^ 40 * 124200 * 2
def baseEnd_124200 : Nat := 7086033032057700069869

theorem tailTrace_124200 : CollatzResearch.WordTrace tailWord_124200 prefixEnd_124200 7086033032057700069869 := by
  unfold tailWord_124200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264973075026043258181027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3019964100034724344241369 2264973075026043258181027)
  ·
    refine ⟨3397459612539064887271541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2264973075026043258181027 3397459612539064887271541)
    ·
      refine ⟨318511838675537333181707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3397459612539064887271541 318511838675537333181707)
      ·
        refine ⟨477767758013305999772561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318511838675537333181707 477767758013305999772561)
        ·
          refine ⟨358325818509979499829421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477767758013305999772561 358325818509979499829421)
          ·
            refine ⟨134372181941242312436033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358325818509979499829421 134372181941242312436033)
            ·
              refine ⟨100779136455931734327025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134372181941242312436033 100779136455931734327025)
              ·
                refine ⟨75584352341948800745269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100779136455931734327025 75584352341948800745269)
                ·
                  refine ⟨7086033032057700069869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75584352341948800745269 7086033032057700069869)
                  ·
                    rfl

theorem cell23_124200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 5].length) (baseStart_124200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124200 prefixEnd_124200 := by exact prefixLift 124200
  have htrace : WordTrace (prefixWord ++ tailWord_124200) baseStart_124200 baseEnd_124200 := by
    simpa [prefixWord, tailWord_124200, baseEnd_124200] using wordTrace_append hprefix tailTrace_124200
  have hstable : (prefixWord ++ tailWord_124200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124200).length < 2 ^ (prefixWord ++ tailWord_124200).sum := by decide
  have hdescent : baseEnd_124200 < baseStart_124200 := by decide
  rcases family_descends (prefixWord ++ tailWord_124200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124230 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_124230 : Nat := 118140960795 + 124230 * 2 ^ 59
def prefixEnd_124230 : Nat := 4983230072969 + 3 ^ 40 * 124230 * 2
def baseEnd_124230 : Nat := 21263233902718061084561

theorem tailTrace_124230 : CollatzResearch.WordTrace tailWord_124230 prefixEnd_124230 21263233902718061084561 := by
  unfold tailWord_124230
  simp only [CollatzResearch.WordTrace]
  refine ⟨141595010623231301248567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3020693559962267759969429 141595010623231301248567)
  ·
    refine ⟨212392515934846951872851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141595010623231301248567 212392515934846951872851)
    ·
      refine ⟨318588773902270427809277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212392515934846951872851 318588773902270427809277)
      ·
        refine ⟨119470790213351410428479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318588773902270427809277 119470790213351410428479)
        ·
          refine ⟨179206185320027115642719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119470790213351410428479 179206185320027115642719)
          ·
            refine ⟨268809277980040673464079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179206185320027115642719 268809277980040673464079)
            ·
              refine ⟨403213916970061010196119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268809277980040673464079 403213916970061010196119)
              ·
                refine ⟨604820875455091515294179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403213916970061010196119 604820875455091515294179)
                ·
                  refine ⟨907231313182637272941269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604820875455091515294179 907231313182637272941269)
                  ·
                    refine ⟨21263233902718061084561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 907231313182637272941269 21263233902718061084561)
                    ·
                      rfl

theorem cell23_124230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_124230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124230 prefixEnd_124230 := by exact prefixLift 124230
  have htrace : WordTrace (prefixWord ++ tailWord_124230) baseStart_124230 baseEnd_124230 := by
    simpa [prefixWord, tailWord_124230, baseEnd_124230] using wordTrace_append hprefix tailTrace_124230
  have hstable : (prefixWord ++ tailWord_124230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124230).length < 2 ^ (prefixWord ++ tailWord_124230).sum := by decide
  have hdescent : baseEnd_124230 < baseStart_124230 := by decide
  rcases family_descends (prefixWord ++ tailWord_124230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124236 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_124236 : Nat := 118140960795 + 124236 * 2 ^ 59
def prefixEnd_124236 : Nat := 4983230072969 + 3 ^ 40 * 124236 * 2
def baseEnd_124236 : Nat := 63792782592081159778655

theorem tailTrace_124236 : CollatzResearch.WordTrace tailWord_124236 prefixEnd_124236 63792782592081159778655 := by
  unfold tailWord_124236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265629588960832332336281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3020839451947776443115041 2265629588960832332336281)
  ·
    refine ⟨1699222191720624249252211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2265629588960832332336281 1699222191720624249252211)
    ·
      refine ⟨2548833287580936373878317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699222191720624249252211 2548833287580936373878317)
      ·
        refine ⟨955812482842851140204369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2548833287580936373878317 955812482842851140204369)
        ·
          refine ⟨716859362132138355153277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955812482842851140204369 716859362132138355153277)
          ·
            refine ⟨268822260799551883182479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716859362132138355153277 268822260799551883182479)
            ·
              refine ⟨403233391199327824773719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268822260799551883182479 403233391199327824773719)
              ·
                refine ⟨604850086798991737160579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403233391199327824773719 604850086798991737160579)
                ·
                  refine ⟨907275130198487605740869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604850086798991737160579 907275130198487605740869)
                  ·
                    refine ⟨170114086912216426076413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907275130198487605740869 170114086912216426076413)
                    ·
                      refine ⟨63792782592081159778655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 170114086912216426076413 63792782592081159778655)
                      ·
                        rfl

theorem cell23_124236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_124236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124236 prefixEnd_124236 := by exact prefixLift 124236
  have htrace : WordTrace (prefixWord ++ tailWord_124236) baseStart_124236 baseEnd_124236 := by
    simpa [prefixWord, tailWord_124236, baseEnd_124236] using wordTrace_append hprefix tailTrace_124236
  have hstable : (prefixWord ++ tailWord_124236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124236).length < 2 ^ (prefixWord ++ tailWord_124236).sum := by decide
  have hdescent : baseEnd_124236 < baseStart_124236 := by decide
  rcases family_descends (prefixWord ++ tailWord_124236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124243 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 1, 4]
def baseStart_124243 : Nat := 118140960795 + 124243 * 2 ^ 59
def prefixEnd_124243 : Nat := 4983230072969 + 3 ^ 40 * 124243 * 2
def baseEnd_124243 : Nat := 21265458985554210797041

theorem tailTrace_124243 : CollatzResearch.WordTrace tailWord_124243 prefixEnd_124243 21265458985554210797041 := by
  unfold tailWord_124243
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531514488896304860177383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3021009659264203240118255 4531514488896304860177383)
  ·
    refine ⟨6797271733344457290266075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531514488896304860177383 6797271733344457290266075)
    ·
      refine ⟨10195907600016685935399113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6797271733344457290266075 10195907600016685935399113)
      ·
        refine ⟨7646930700012514451549335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10195907600016685935399113 7646930700012514451549335)
        ·
          refine ⟨11470396050018771677324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646930700012514451549335 11470396050018771677324003)
          ·
            refine ⟨17205594075028157515986005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470396050018771677324003 17205594075028157515986005)
            ·
              refine ⟨201628055566736220890461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 17205594075028157515986005 201628055566736220890461)
              ·
                refine ⟨75610520837526082833923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201628055566736220890461 75610520837526082833923)
                ·
                  refine ⟨113415781256289124250885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75610520837526082833923 113415781256289124250885)
                  ·
                    refine ⟨21265458985554210797041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113415781256289124250885 21265458985554210797041)
                    ·
                      rfl

theorem cell23_124243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 4].length) (baseStart_124243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124243 prefixEnd_124243 := by exact prefixLift 124243
  have htrace : WordTrace (prefixWord ++ tailWord_124243) baseStart_124243 baseEnd_124243 := by
    simpa [prefixWord, tailWord_124243, baseEnd_124243] using wordTrace_append hprefix tailTrace_124243
  have hstable : (prefixWord ++ tailWord_124243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124243).length < 2 ^ (prefixWord ++ tailWord_124243).sum := by decide
  have hdescent : baseEnd_124243 < baseStart_124243 := by decide
  rcases family_descends (prefixWord ++ tailWord_124243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124256 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 6]
def baseStart_124256 : Nat := 118140960795 + 124256 * 2 ^ 59
def prefixEnd_124256 : Nat := 4983230072969 + 3 ^ 40 * 124256 * 2
def baseEnd_124256 : Nat := 7089228022796786836507

theorem tailTrace_124256 : CollatzResearch.WordTrace tailWord_124256 prefixEnd_124256 7089228022796786836507 := by
  unfold tailWord_124256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265994318924604040200311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3021325758566138720267081 2265994318924604040200311)
  ·
    refine ⟨3398991478386906060300467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265994318924604040200311 3398991478386906060300467)
    ·
      refine ⟨5098487217580359090450701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398991478386906060300467 5098487217580359090450701)
      ·
        refine ⟨1911932706592634658919013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5098487217580359090450701 1911932706592634658919013)
        ·
          refine ⟨358487382486118998547315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1911932706592634658919013 358487382486118998547315)
          ·
            refine ⟨537731073729178497820973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358487382486118998547315 537731073729178497820973)
            ·
              refine ⟨201649152648441936682865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537731073729178497820973 201649152648441936682865)
              ·
                refine ⟨151236864486331452512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201649152648441936682865 151236864486331452512149)
                ·
                  refine ⟨7089228022796786836507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151236864486331452512149 7089228022796786836507)
                  ·
                    rfl

theorem cell23_124256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_124256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124256 prefixEnd_124256 := by exact prefixLift 124256
  have htrace : WordTrace (prefixWord ++ tailWord_124256) baseStart_124256 baseEnd_124256 := by
    simpa [prefixWord, tailWord_124256, baseEnd_124256] using wordTrace_append hprefix tailTrace_124256
  have hstable : (prefixWord ++ tailWord_124256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124256).length < 2 ^ (prefixWord ++ tailWord_124256).sum := by decide
  have hdescent : baseEnd_124256 < baseStart_124256 := by decide
  rcases family_descends (prefixWord ++ tailWord_124256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124259 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_124259 : Nat := 118140960795 + 124259 * 2 ^ 59
def prefixEnd_124259 : Nat := 4983230072969 + 3 ^ 40 * 124259 * 2
def baseEnd_124259 : Nat := 63804592647134569791049

theorem tailTrace_124259 : CollatzResearch.WordTrace tailWord_124259 prefixEnd_124259 63804592647134569791049 := by
  unfold tailWord_124259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532098056838339592759831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3021398704558893061839887 4532098056838339592759831)
  ·
    refine ⟨6798147085257509389139747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532098056838339592759831 6798147085257509389139747)
    ·
      refine ⟨10197220627886264083709621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6798147085257509389139747 10197220627886264083709621)
      ·
        refine ⟨955989433864337257847777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10197220627886264083709621 955989433864337257847777)
        ·
          refine ⟨716992075398252943385833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955989433864337257847777 716992075398252943385833)
          ·
            refine ⟨537744056548689707539375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716992075398252943385833 537744056548689707539375)
            ·
              refine ⟨806616084823034561309063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537744056548689707539375 806616084823034561309063)
              ·
                refine ⟨1209924127234551841963595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806616084823034561309063 1209924127234551841963595)
                ·
                  refine ⟨1814886190851827762945393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209924127234551841963595 1814886190851827762945393)
                  ·
                    refine ⟨1361164643138870822209045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814886190851827762945393 1361164643138870822209045)
                    ·
                      refine ⟨63804592647134569791049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1361164643138870822209045 63804592647134569791049)
                      ·
                        rfl

theorem cell23_124259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_124259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124259 prefixEnd_124259 := by exact prefixLift 124259
  have htrace : WordTrace (prefixWord ++ tailWord_124259) baseStart_124259 baseEnd_124259 := by
    simpa [prefixWord, tailWord_124259, baseEnd_124259] using wordTrace_append hprefix tailTrace_124259
  have hstable : (prefixWord ++ tailWord_124259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124259).length < 2 ^ (prefixWord ++ tailWord_124259).sum := by decide
  have hdescent : baseEnd_124259 < baseStart_124259 := by decide
  rcases family_descends (prefixWord ++ tailWord_124259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124299 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 6]
def baseStart_124299 : Nat := 118140960795 + 124299 * 2 ^ 59
def prefixEnd_124299 : Nat := 4983230072969 + 3 ^ 40 * 124299 * 2
def baseEnd_124299 : Nat := 21275043957771471096955

theorem tailTrace_124299 : CollatzResearch.WordTrace tailWord_124299 prefixEnd_124299 21275043957771471096955 := by
  unfold tailWord_124299
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533556976693426424215951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3022371317795617616143967 4533556976693426424215951)
  ·
    refine ⟨6800335465040139636323927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533556976693426424215951 6800335465040139636323927)
    ·
      refine ⟨10200503197560209454485891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800335465040139636323927 10200503197560209454485891)
      ·
        refine ⟨15300754796340314181728837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200503197560209454485891 15300754796340314181728837)
        ·
          refine ⟨2868891524313808909074157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15300754796340314181728837 2868891524313808909074157)
          ·
            refine ⟨1075834321617678340902809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2868891524313808909074157 1075834321617678340902809)
            ·
              refine ⟨806875741213258755677107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075834321617678340902809 806875741213258755677107)
              ·
                refine ⟨1210313611819888133515661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806875741213258755677107 1210313611819888133515661)
                ·
                  refine ⟨453867604432458050068373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210313611819888133515661 453867604432458050068373)
                  ·
                    refine ⟨21275043957771471096955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 453867604432458050068373 21275043957771471096955)
                    ·
                      rfl

theorem cell23_124299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_124299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124299 prefixEnd_124299 := by exact prefixLift 124299
  have htrace : WordTrace (prefixWord ++ tailWord_124299) baseStart_124299 baseEnd_124299 := by
    simpa [prefixWord, tailWord_124299, baseEnd_124299] using wordTrace_append hprefix tailTrace_124299
  have hstable : (prefixWord ++ tailWord_124299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124299).length < 2 ^ (prefixWord ++ tailWord_124299).sum := by decide
  have hdescent : baseEnd_124299 < baseStart_124299 := by decide
  rcases family_descends (prefixWord ++ tailWord_124299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124360 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_124360 : Nat := 118140960795 + 124360 * 2 ^ 59
def prefixEnd_124360 : Nat := 4983230072969 + 3 ^ 40 * 124360 * 2
def baseEnd_124360 : Nat := 63856454193238674628085

theorem tailTrace_124360 : CollatzResearch.WordTrace tailWord_124360 prefixEnd_124360 63856454193238674628085 := by
  unfold tailWord_124360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267890914736216921093267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3023854552981622561457689 2267890914736216921093267)
  ·
    refine ⟨3401836372104325381639901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2267890914736216921093267 3401836372104325381639901)
    ·
      refine ⟨1275688639539122018114963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3401836372104325381639901 1275688639539122018114963)
      ·
        refine ⟨1913532959308683027172445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275688639539122018114963 1913532959308683027172445)
        ·
          refine ⟨717574859740756135189667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1913532959308683027172445 717574859740756135189667)
          ·
            refine ⟨1076362289611134202784501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717574859740756135189667 1076362289611134202784501)
            ·
              refine ⟨100908964651043831511047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1076362289611134202784501 100908964651043831511047)
              ·
                refine ⟨151363446976565747266571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100908964651043831511047 151363446976565747266571)
                ·
                  refine ⟨227045170464848620899857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151363446976565747266571 227045170464848620899857)
                  ·
                    refine ⟨170283877848636465674893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227045170464848620899857 170283877848636465674893)
                    ·
                      refine ⟨63856454193238674628085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 170283877848636465674893 63856454193238674628085)
                      ·
                        rfl

theorem cell23_124360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_124360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124360 prefixEnd_124360 := by exact prefixLift 124360
  have htrace : WordTrace (prefixWord ++ tailWord_124360) baseStart_124360 baseEnd_124360 := by
    simpa [prefixWord, tailWord_124360, baseEnd_124360] using wordTrace_append hprefix tailTrace_124360
  have hstable : (prefixWord ++ tailWord_124360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124360).length < 2 ^ (prefixWord ++ tailWord_124360).sum := by decide
  have hdescent : baseEnd_124360 < baseStart_124360 := by decide
  rcases family_descends (prefixWord ++ tailWord_124360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124369 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_124369 : Nat := 118140960795 + 124369 * 2 ^ 59
def prefixEnd_124369 : Nat := 4983230072969 + 3 ^ 40 * 124369 * 2
def baseEnd_124369 : Nat := 63861075519129139415543

theorem tailTrace_124369 : CollatzResearch.WordTrace tailWord_124369 prefixEnd_124369 63861075519129139415543 := by
  unfold tailWord_124369
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536110086439828379264161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3024073390959885586176107 4536110086439828379264161)
  ·
    refine ⟨3402082564829871284448121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4536110086439828379264161 3402082564829871284448121)
    ·
      refine ⟨2551561923622403463336091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402082564829871284448121 2551561923622403463336091)
      ·
        refine ⟨3827342885433605195004137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551561923622403463336091 3827342885433605195004137)
        ·
          refine ⟨2870507164075203896253103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827342885433605195004137 2870507164075203896253103)
          ·
            refine ⟨4305760746112805844379655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870507164075203896253103 4305760746112805844379655)
            ·
              refine ⟨6458641119169208766569483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305760746112805844379655 6458641119169208766569483)
              ·
                refine ⟨9687961678753813149854225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458641119169208766569483 9687961678753813149854225)
                ·
                  refine ⟨7265971259065359862390669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9687961678753813149854225 7265971259065359862390669)
                  ·
                    refine ⟨2724739222149509948396501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7265971259065359862390669 2724739222149509948396501)
                    ·
                      refine ⟨63861075519129139415543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2724739222149509948396501 63861075519129139415543)
                      ·
                        rfl

theorem cell23_124369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_124369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124369 prefixEnd_124369 := by exact prefixLift 124369
  have htrace : WordTrace (prefixWord ++ tailWord_124369) baseStart_124369 baseEnd_124369 := by
    simpa [prefixWord, tailWord_124369, baseEnd_124369] using wordTrace_append hprefix tailTrace_124369
  have hstable : (prefixWord ++ tailWord_124369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124369).length < 2 ^ (prefixWord ++ tailWord_124369).sum := by decide
  have hdescent : baseEnd_124369 < baseStart_124369 := by decide
  rcases family_descends (prefixWord ++ tailWord_124369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124383 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 5, 3, 2]
def baseStart_124383 : Nat := 118140960795 + 124383 * 2 ^ 59
def prefixEnd_124383 : Nat := 4983230072969 + 3 ^ 40 * 124383 * 2
def baseEnd_124383 : Nat := 63868264248292084640479

theorem tailTrace_124383 : CollatzResearch.WordTrace tailWord_124383 prefixEnd_124383 63868264248292084640479 := by
  unfold tailWord_124383
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536620708389108770273803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3024413805592739180182535 4536620708389108770273803)
  ·
    refine ⟨6804931062583663155410705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536620708389108770273803 6804931062583663155410705)
    ·
      refine ⟨5103698296937747366558029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6804931062583663155410705 5103698296937747366558029)
      ·
        refine ⟨1913886861351655262459261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5103698296937747366558029 1913886861351655262459261)
        ·
          refine ⟨717707573006870723422223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1913886861351655262459261 717707573006870723422223)
          ·
            refine ⟨1076561359510306085133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717707573006870723422223 1076561359510306085133335)
            ·
              refine ⟨1614842039265459127700003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076561359510306085133335 1614842039265459127700003)
              ·
                refine ⟨2422263058898188691550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614842039265459127700003 2422263058898188691550005)
                ·
                  refine ⟨227087161771705189832813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422263058898188691550005 227087161771705189832813)
                  ·
                    refine ⟨85157685664389446187305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227087161771705189832813 85157685664389446187305)
                    ·
                      refine ⟨63868264248292084640479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85157685664389446187305 63868264248292084640479)
                      ·
                        rfl

theorem cell23_124383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_124383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124383 prefixEnd_124383 := by exact prefixLift 124383
  have htrace : WordTrace (prefixWord ++ tailWord_124383) baseStart_124383 baseEnd_124383 := by
    simpa [prefixWord, tailWord_124383, baseEnd_124383] using wordTrace_append hprefix tailTrace_124383
  have hstable : (prefixWord ++ tailWord_124383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124383).length < 2 ^ (prefixWord ++ tailWord_124383).sum := by decide
  have hdescent : baseEnd_124383 < baseStart_124383 := by decide
  rcases family_descends (prefixWord ++ tailWord_124383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124417 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_124417 : Nat := 118140960795 + 124417 * 2 ^ 59
def prefixEnd_124417 : Nat := 4983230072969 + 3 ^ 40 * 124417 * 2
def baseEnd_124417 : Nat := 63885722590544951615323

theorem tailTrace_124417 : CollatzResearch.WordTrace tailWord_124417 prefixEnd_124417 63885722590544951615323 := by
  unfold tailWord_124417
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537860790265932577011505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3025240526843955051341003 4537860790265932577011505)
  ·
    refine ⟨3403395592699449432758629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4537860790265932577011505 3403395592699449432758629)
    ·
      refine ⟨638136673631146768642243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3403395592699449432758629 638136673631146768642243)
      ·
        refine ⟨957205010446720152963365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638136673631146768642243 957205010446720152963365)
        ·
          refine ⟨179475939458760028680631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 957205010446720152963365 179475939458760028680631)
          ·
            refine ⟨269213909188140043020947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179475939458760028680631 269213909188140043020947)
            ·
              refine ⟨403820863782210064531421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269213909188140043020947 403820863782210064531421)
              ·
                refine ⟨151432823918328774199283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403820863782210064531421 151432823918328774199283)
                ·
                  refine ⟨227149235877493161298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151432823918328774199283 227149235877493161298925)
                  ·
                    refine ⟨85180963454059935487097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227149235877493161298925 85180963454059935487097)
                    ·
                      refine ⟨63885722590544951615323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85180963454059935487097 63885722590544951615323)
                      ·
                        rfl

theorem cell23_124417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_124417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124417 prefixEnd_124417 := by exact prefixLift 124417
  have htrace : WordTrace (prefixWord ++ tailWord_124417) baseStart_124417 baseEnd_124417 := by
    simpa [prefixWord, tailWord_124417, baseEnd_124417] using wordTrace_append hprefix tailTrace_124417
  have hstable : (prefixWord ++ tailWord_124417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124417).length < 2 ^ (prefixWord ++ tailWord_124417).sum := by decide
  have hdescent : baseEnd_124417 < baseStart_124417 := by decide
  rcases family_descends (prefixWord ++ tailWord_124417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124487 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 5]
def baseStart_124487 : Nat := 118140960795 + 124487 * 2 ^ 59
def prefixEnd_124487 : Nat := 4983230072969 + 3 ^ 40 * 124487 * 2
def baseEnd_124487 : Nat := 7102407359595519748889

theorem tailTrace_124487 : CollatzResearch.WordTrace tailWord_124487 prefixEnd_124487 7102407359595519748889 := by
  unfold tailWord_124487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540413900012334532059715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3026942600008223021373143 4540413900012334532059715)
  ·
    refine ⟨6810620850018501798089573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540413900012334532059715 6810620850018501798089573)
    ·
      refine ⟨1276991409378469087141795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6810620850018501798089573 1276991409378469087141795)
      ·
        refine ⟨1915487114067703630712693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276991409378469087141795 1915487114067703630712693)
        ·
          refine ⟨179576916943847215379315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1915487114067703630712693 179576916943847215379315)
          ·
            refine ⟨269365375415770823068973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179576916943847215379315 269365375415770823068973)
            ·
              refine ⟨101012015780914058650865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269365375415770823068973 101012015780914058650865)
              ·
                refine ⟨75759011835685543988149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101012015780914058650865 75759011835685543988149)
                ·
                  refine ⟨7102407359595519748889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75759011835685543988149 7102407359595519748889)
                  ·
                    rfl

theorem cell23_124487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 5].length) (baseStart_124487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124487 prefixEnd_124487 := by exact prefixLift 124487
  have htrace : WordTrace (prefixWord ++ tailWord_124487) baseStart_124487 baseEnd_124487 := by
    simpa [prefixWord, tailWord_124487, baseEnd_124487] using wordTrace_append hprefix tailTrace_124487
  have hstable : (prefixWord ++ tailWord_124487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124487).length < 2 ^ (prefixWord ++ tailWord_124487).sum := by decide
  have hdescent : baseEnd_124487 < baseStart_124487 := by decide
  rcases family_descends (prefixWord ++ tailWord_124487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124506 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_124506 : Nat := 118140960795 + 124506 * 2 ^ 59
def prefixEnd_124506 : Nat := 4983230072969 + 3 ^ 40 * 124506 * 2
def baseEnd_124506 : Nat := 63931422368795103402413

theorem tailTrace_124506 : CollatzResearch.WordTrace tailWord_124506 prefixEnd_124506 63931422368795103402413 := by
  unfold tailWord_124506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135276721735875194250343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3027404591295667184667581 1135276721735875194250343)
  ·
    refine ⟨1702915082603812791375515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135276721735875194250343 1702915082603812791375515)
    ·
      refine ⟨2554372623905719187063273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702915082603812791375515 2554372623905719187063273)
      ·
        refine ⟨1915779467929289390297455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554372623905719187063273 1915779467929289390297455)
        ·
          refine ⟨2873669201893934085446183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915779467929289390297455 2873669201893934085446183)
          ·
            refine ⟨4310503802840901128169275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873669201893934085446183 4310503802840901128169275)
            ·
              refine ⟨6465755704261351692253913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310503802840901128169275 6465755704261351692253913)
              ·
                refine ⟨4849316778196013769190435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6465755704261351692253913 4849316778196013769190435)
                ·
                  refine ⟨7273975167294020653785653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849316778196013769190435 7273975167294020653785653)
                  ·
                    refine ⟨681935171933814436292405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7273975167294020653785653 681935171933814436292405)
                    ·
                      refine ⟨63931422368795103402413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 681935171933814436292405 63931422368795103402413)
                      ·
                        rfl

theorem cell23_124506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_124506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124506 prefixEnd_124506 := by exact prefixLift 124506
  have htrace : WordTrace (prefixWord ++ tailWord_124506) baseStart_124506 baseEnd_124506 := by
    simpa [prefixWord, tailWord_124506, baseEnd_124506] using wordTrace_append hprefix tailTrace_124506
  have hstable : (prefixWord ++ tailWord_124506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124506).length < 2 ^ (prefixWord ++ tailWord_124506).sum := by decide
  have hdescent : baseEnd_124506 < baseStart_124506 := by decide
  rcases family_descends (prefixWord ++ tailWord_124506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124513 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_124513 : Nat := 118140960795 + 124513 * 2 ^ 59
def prefixEnd_124513 : Nat := 4983230072969 + 3 ^ 40 * 124513 * 2
def baseEnd_124513 : Nat := 21311672244458858671627

theorem tailTrace_124513 : CollatzResearch.WordTrace tailWord_124513 prefixEnd_124513 21311672244458858671627 := by
  unfold tailWord_124513
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541362197918140972506193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3027574798612093981670795 4541362197918140972506193)
  ·
    refine ⟨3406021648438605729379645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4541362197918140972506193 3406021648438605729379645)
    ·
      refine ⟨1277258118164477148517367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3406021648438605729379645 1277258118164477148517367)
      ·
        refine ⟨1915887177246715722776051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277258118164477148517367 1915887177246715722776051)
        ·
          refine ⟨2873830765870073584164077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915887177246715722776051 2873830765870073584164077)
          ·
            refine ⟨1077686537201277594061529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2873830765870073584164077 1077686537201277594061529)
            ·
              refine ⟨808264902900958195546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077686537201277594061529 808264902900958195546147)
              ·
                refine ⟨1212397354351437293319221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808264902900958195546147 1212397354351437293319221)
                ·
                  refine ⟨113662251970447246248677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212397354351437293319221 113662251970447246248677)
                  ·
                    refine ⟨21311672244458858671627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113662251970447246248677 21311672244458858671627)
                    ·
                      rfl

theorem cell23_124513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_124513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124513 prefixEnd_124513 := by exact prefixLift 124513
  have htrace : WordTrace (prefixWord ++ tailWord_124513) baseStart_124513 baseEnd_124513 := by
    simpa [prefixWord, tailWord_124513, baseEnd_124513] using wordTrace_append hprefix tailTrace_124513
  have hstable : (prefixWord ++ tailWord_124513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124513).length < 2 ^ (prefixWord ++ tailWord_124513).sum := by decide
  have hdescent : baseEnd_124513 < baseStart_124513 := by decide
  rcases family_descends (prefixWord ++ tailWord_124513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
