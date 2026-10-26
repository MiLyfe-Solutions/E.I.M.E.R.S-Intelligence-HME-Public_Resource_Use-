import V185TrunkScan22Chunk224

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2006303 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 6]
def baseStart_2006303 : Nat := 118140960795 + 2006303 * 2 ^ 59
def prefixEnd_2006303 : Nat := 4983230072969 + 3 ^ 40 * 2006303 * 2
def baseEnd_2006303 : Nat := 228932839457237569774597

theorem tailTrace_2006303 : CollatzResearch.WordTrace tailWord_2006303 prefixEnd_2006303 228932839457237569774597 := by
  unfold tailWord_2006303
  simp only [CollatzResearch.WordTrace]
  refine ⟨73175882050514355117807563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48783921367009570078538375 73175882050514355117807563)
  ·
    refine ⟨109763823075771532676711345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73175882050514355117807563 109763823075771532676711345)
    ·
      refine ⟨82322867306828649507533509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109763823075771532676711345 82322867306828649507533509)
      ·
        refine ⟨15435537620030371782662533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82322867306828649507533509 15435537620030371782662533)
        ·
          refine ⟨2894163303755694709249225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15435537620030371782662533 2894163303755694709249225)
          ·
            refine ⟨2170622477816771031936919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894163303755694709249225 2170622477816771031936919)
            ·
              refine ⟨3255933716725156547905379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170622477816771031936919 3255933716725156547905379)
              ·
                refine ⟨4883900575087734821858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255933716725156547905379 4883900575087734821858069)
                ·
                  refine ⟨228932839457237569774597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4883900575087734821858069 228932839457237569774597)
                  ·
                    rfl

theorem cell22_2006303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].length) (baseStart_2006303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006303 prefixEnd_2006303 := by exact prefixLift 2006303
  have htrace : WordTrace (prefixWord ++ tailWord_2006303) baseStart_2006303 baseEnd_2006303 := by
    simpa [prefixWord, tailWord_2006303, baseEnd_2006303] using wordTrace_append hprefix tailTrace_2006303
  have hstable : (prefixWord ++ tailWord_2006303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006303).length < 2 ^ (prefixWord ++ tailWord_2006303).sum := by decide
  have hdescent : baseEnd_2006303 < baseStart_2006303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006421 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2006421 : Nat := 118140960795 + 2006421 * 2 ^ 59
def prefixEnd_2006421 : Nat := 4983230072969 + 3 ^ 40 * 2006421 * 2
def baseEnd_2006421 : Nat := 228946304061066578291143

theorem tailTrace_2006421 : CollatzResearch.WordTrace tailWord_2006421 prefixEnd_2006421 228946304061066578291143 := by
  unfold tailWord_2006421
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180185864086861270603117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48786790576057907513735411 73180185864086861270603117)
  ·
    refine ⟨27442569699032572976476169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73180185864086861270603117 27442569699032572976476169)
    ·
      refine ⟨20581927274274429732357127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27442569699032572976476169 20581927274274429732357127)
      ·
        refine ⟨30872890911411644598535691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20581927274274429732357127 30872890911411644598535691)
        ·
          refine ⟨46309336367117466897803537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30872890911411644598535691 46309336367117466897803537)
          ·
            refine ⟨34732002275338100173352653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46309336367117466897803537 34732002275338100173352653)
            ·
              refine ⟨13024500853251787565007245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34732002275338100173352653 13024500853251787565007245)
              ·
                refine ⟨4884187819969420336877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024500853251787565007245 4884187819969420336877717)
                ·
                  refine ⟨228946304061066578291143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4884187819969420336877717 228946304061066578291143)
                  ·
                    rfl

theorem cell22_2006421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2006421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006421 prefixEnd_2006421 := by exact prefixLift 2006421
  have htrace : WordTrace (prefixWord ++ tailWord_2006421) baseStart_2006421 baseEnd_2006421 := by
    simpa [prefixWord, tailWord_2006421, baseEnd_2006421] using wordTrace_append hprefix tailTrace_2006421
  have hstable : (prefixWord ++ tailWord_2006421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006421).length < 2 ^ (prefixWord ++ tailWord_2006421).sum := by decide
  have hdescent : baseEnd_2006421 < baseStart_2006421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_2006451 : Nat := 118140960795 + 2006451 * 2 ^ 59
def prefixEnd_2006451 : Nat := 4983230072969 + 3 ^ 40 * 2006451 * 2
def baseEnd_2006451 : Nat := 686849181796289656623337

theorem tailTrace_2006451 : CollatzResearch.WordTrace tailWord_2006451 prefixEnd_2006451 686849181796289656623337 := by
  unfold tailWord_2006451
  simp only [CollatzResearch.WordTrace]
  refine ⟨73181280053978176394195207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48787520035985450929463471 73181280053978176394195207)
  ·
    refine ⟨109771920080967264591292811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73181280053978176394195207 109771920080967264591292811)
    ·
      refine ⟨164657880121450896886939217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109771920080967264591292811 164657880121450896886939217)
      ·
        refine ⟨123493410091088172665204413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164657880121450896886939217 123493410091088172665204413)
        ·
          refine ⟨46310028784158064749451655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123493410091088172665204413 46310028784158064749451655)
          ·
            refine ⟨69465043176237097124177483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46310028784158064749451655 69465043176237097124177483)
            ·
              refine ⟨104197564764355645686266225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69465043176237097124177483 104197564764355645686266225)
              ·
                refine ⟨78148173573266734264699669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104197564764355645686266225 78148173573266734264699669)
                ·
                  refine ⟨3663195636246878168657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78148173573266734264699669 3663195636246878168657797)
                  ·
                    refine ⟨686849181796289656623337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663195636246878168657797 686849181796289656623337)
                    ·
                      rfl

theorem cell22_2006451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_2006451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006451 prefixEnd_2006451 := by exact prefixLift 2006451
  have htrace : WordTrace (prefixWord ++ tailWord_2006451) baseStart_2006451 baseEnd_2006451 := by
    simpa [prefixWord, tailWord_2006451, baseEnd_2006451] using wordTrace_append hprefix tailTrace_2006451
  have hstable : (prefixWord ++ tailWord_2006451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006451).length < 2 ^ (prefixWord ++ tailWord_2006451).sum := by decide
  have hdescent : baseEnd_2006451 < baseStart_2006451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006496 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_2006496 : Nat := 118140960795 + 2006496 * 2 ^ 59
def prefixEnd_2006496 : Nat := 4983230072969 + 3 ^ 40 * 2006496 * 2
def baseEnd_2006496 : Nat := 686864586215924539248199

theorem tailTrace_2006496 : CollatzResearch.WordTrace tailWord_2006496 prefixEnd_2006496 686864586215924539248199 := by
  unfold tailWord_2006496
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591460669407574539791671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48788614225876766053055561 36591460669407574539791671)
  ·
    refine ⟨54887191004111361809687507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36591460669407574539791671 54887191004111361809687507)
    ·
      refine ⟨82330786506167042714531261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54887191004111361809687507 82330786506167042714531261)
      ·
        refine ⟨30874044939812641017949223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82330786506167042714531261 30874044939812641017949223)
        ·
          refine ⟨46311067409718961526923835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30874044939812641017949223 46311067409718961526923835)
          ·
            refine ⟨69466601114578442290385753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46311067409718961526923835 69466601114578442290385753)
            ·
              refine ⟨52099950835933831717789315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69466601114578442290385753 52099950835933831717789315)
              ·
                refine ⟨78149926253900747576683973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52099950835933831717789315 78149926253900747576683973)
                ·
                  refine ⟨14653111172606390170628245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78149926253900747576683973 14653111172606390170628245)
                  ·
                    refine ⟨686864586215924539248199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14653111172606390170628245 686864586215924539248199)
                    ·
                      rfl

theorem cell22_2006496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_2006496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006496 prefixEnd_2006496 := by exact prefixLift 2006496
  have htrace : WordTrace (prefixWord ++ tailWord_2006496) baseStart_2006496 baseEnd_2006496 := by
    simpa [prefixWord, tailWord_2006496, baseEnd_2006496] using wordTrace_append hprefix tailTrace_2006496
  have hstable : (prefixWord ++ tailWord_2006496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006496).length < 2 ^ (prefixWord ++ tailWord_2006496).sum := by decide
  have hdescent : baseEnd_2006496 < baseStart_2006496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006511 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 9]
def baseStart_2006511 : Nat := 118140960795 + 2006511 * 2 ^ 59
def prefixEnd_2006511 : Nat := 4983230072969 + 3 ^ 40 * 2006511 * 2
def baseEnd_2006511 : Nat := 228956573674156500041051

theorem tailTrace_2006511 : CollatzResearch.WordTrace tailWord_2006511 prefixEnd_2006511 228956573674156500041051 := by
  unfold tailWord_2006511
  simp only [CollatzResearch.WordTrace]
  refine ⟨73183468433760806641379387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48788978955840537760919591 73183468433760806641379387)
  ·
    refine ⟨109775202650641209962069081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73183468433760806641379387 109775202650641209962069081)
    ·
      refine ⟨82331401987980907471551811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109775202650641209962069081 82331401987980907471551811)
      ·
        refine ⟨123497102981971361207327717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82331401987980907471551811 123497102981971361207327717)
        ·
          refine ⟨23155706809119630226373947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123497102981971361207327717 23155706809119630226373947)
          ·
            refine ⟨34733560213679445339560921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23155706809119630226373947 34733560213679445339560921)
            ·
              refine ⟨26050170160259584004670691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34733560213679445339560921 26050170160259584004670691)
              ·
                refine ⟨39075255240389376007006037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26050170160259584004670691 39075255240389376007006037)
                ·
                  refine ⟨228956573674156500041051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39075255240389376007006037 228956573674156500041051)
                  ·
                    rfl

theorem cell22_2006511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_2006511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006511 prefixEnd_2006511 := by exact prefixLift 2006511
  have htrace : WordTrace (prefixWord ++ tailWord_2006511) baseStart_2006511 baseEnd_2006511 := by
    simpa [prefixWord, tailWord_2006511, baseEnd_2006511] using wordTrace_append hprefix tailTrace_2006511
  have hstable : (prefixWord ++ tailWord_2006511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006511).length < 2 ^ (prefixWord ++ tailWord_2006511).sum := by decide
  have hdescent : baseEnd_2006511 < baseStart_2006511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006530 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2006530 : Nat := 118140960795 + 2006530 * 2 ^ 59
def prefixEnd_2006530 : Nat := 4983230072969 + 3 ^ 40 * 2006530 * 2
def baseEnd_2006530 : Nat := 686876225110759783898095

theorem tailTrace_2006530 : CollatzResearch.WordTrace tailWord_2006530 prefixEnd_2006530 686876225110759783898095 := by
  unfold tailWord_2006530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296040355172993221580261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48789440947127981924214029 18296040355172993221580261)
  ·
    refine ⟨3430507566594936229046299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18296040355172993221580261 3430507566594936229046299)
    ·
      refine ⟨5145761349892404343569449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430507566594936229046299 5145761349892404343569449)
      ·
        refine ⟨3859321012419303257677087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5145761349892404343569449 3859321012419303257677087)
        ·
          refine ⟨5788981518628954886515631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859321012419303257677087 5788981518628954886515631)
          ·
            refine ⟨8683472277943432329773447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788981518628954886515631 8683472277943432329773447)
            ·
              refine ⟨13025208416915148494660171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683472277943432329773447 13025208416915148494660171)
              ·
                refine ⟨19537812625372722741990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025208416915148494660171 19537812625372722741990257)
                ·
                  refine ⟨14653359469029542056492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19537812625372722741990257 14653359469029542056492693)
                  ·
                    refine ⟨686876225110759783898095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14653359469029542056492693 686876225110759783898095)
                    ·
                      rfl

theorem cell22_2006530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2006530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006530 prefixEnd_2006530 := by exact prefixLift 2006530
  have htrace : WordTrace (prefixWord ++ tailWord_2006530) baseStart_2006530 baseEnd_2006530 := by
    simpa [prefixWord, tailWord_2006530, baseEnd_2006530] using wordTrace_append hprefix tailTrace_2006530
  have hstable : (prefixWord ++ tailWord_2006530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006530).length < 2 ^ (prefixWord ++ tailWord_2006530).sum := by decide
  have hdescent : baseEnd_2006530 < baseStart_2006530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006620 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2006620 : Nat := 118140960795 + 2006620 * 2 ^ 59
def prefixEnd_2006620 : Nat := 4983230072969 + 3 ^ 40 * 2006620 * 2
def baseEnd_2006620 : Nat := 686907033950029549147819

theorem tailTrace_2006620 : CollatzResearch.WordTrace tailWord_2006620 prefixEnd_2006620 686907033950029549147819 := by
  unfold tailWord_2006620
  simp only [CollatzResearch.WordTrace]
  refine ⟨36593721995182959128548657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48791629326910612171398209 36593721995182959128548657)
  ·
    refine ⟨27445291496387219346411493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36593721995182959128548657 27445291496387219346411493)
    ·
      refine ⟨5145992155572603627452155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27445291496387219346411493 5145992155572603627452155)
      ·
        refine ⟨7718988233358905441178233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145992155572603627452155 7718988233358905441178233)
        ·
          refine ⟨5789241175019179080883675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7718988233358905441178233 5789241175019179080883675)
          ·
            refine ⟨8683861762528768621325513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789241175019179080883675 8683861762528768621325513)
            ·
              refine ⟨6512896321896576465994135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8683861762528768621325513 6512896321896576465994135)
              ·
                refine ⟨9769344482844864698991203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512896321896576465994135 9769344482844864698991203)
                ·
                  refine ⟨14654016724267297048486805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9769344482844864698991203 14654016724267297048486805)
                  ·
                    refine ⟨686907033950029549147819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14654016724267297048486805 686907033950029549147819)
                    ·
                      rfl

theorem cell22_2006620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2006620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006620 prefixEnd_2006620 := by exact prefixLift 2006620
  have htrace : WordTrace (prefixWord ++ tailWord_2006620) baseStart_2006620 baseEnd_2006620 := by
    simpa [prefixWord, tailWord_2006620, baseEnd_2006620] using wordTrace_append hprefix tailTrace_2006620
  have hstable : (prefixWord ++ tailWord_2006620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006620).length < 2 ^ (prefixWord ++ tailWord_2006620).sum := by decide
  have hdescent : baseEnd_2006620 < baseStart_2006620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006637 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2006637 : Nat := 118140960795 + 2006637 * 2 ^ 59
def prefixEnd_2006637 : Nat := 4983230072969 + 3 ^ 40 * 2006637 * 2
def baseEnd_2006637 : Nat := 686912853397447171472767

theorem tailTrace_2006637 : CollatzResearch.WordTrace tailWord_2006637 prefixEnd_2006637 686912853397447171472767 := by
  unfold tailWord_2006637
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188064031304330160466165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48792042687536220106977443 73188064031304330160466165)
  ·
    refine ⟨6861381002934780952543703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73188064031304330160466165 6861381002934780952543703)
    ·
      refine ⟨10292071504402171428815555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861381002934780952543703 10292071504402171428815555)
      ·
        refine ⟨15438107256603257143223333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292071504402171428815555 15438107256603257143223333)
        ·
          refine ⟨2894645110613110714354375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15438107256603257143223333 2894645110613110714354375)
          ·
            refine ⟨4341967665919666071531563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894645110613110714354375 4341967665919666071531563)
            ·
              refine ⟨6512951498879499107297345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341967665919666071531563 6512951498879499107297345)
              ·
                refine ⟨4884713624159624330473009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6512951498879499107297345 4884713624159624330473009)
                ·
                  refine ⟨3663535218119718247854757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884713624159624330473009 3663535218119718247854757)
                  ·
                    refine ⟨686912853397447171472767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3663535218119718247854757 686912853397447171472767)
                    ·
                      rfl

theorem cell22_2006637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2006637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006637 prefixEnd_2006637 := by exact prefixLift 2006637
  have htrace : WordTrace (prefixWord ++ tailWord_2006637) baseStart_2006637 baseEnd_2006637 := by
    simpa [prefixWord, tailWord_2006637, baseEnd_2006637] using wordTrace_append hprefix tailTrace_2006637
  have hstable : (prefixWord ++ tailWord_2006637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006637).length < 2 ^ (prefixWord ++ tailWord_2006637).sum := by decide
  have hdescent : baseEnd_2006637 < baseStart_2006637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006650 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_2006650 : Nat := 118140960795 + 2006650 * 2 ^ 59
def prefixEnd_2006650 : Nat := 4983230072969 + 3 ^ 40 * 2006650 * 2
def baseEnd_2006650 : Nat := 686917303563119470897727

theorem tailTrace_2006650 : CollatzResearch.WordTrace tailWord_2006650 prefixEnd_2006650 686917303563119470897727 := by
  unfold tailWord_2006650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297134545064308345172351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48792358786838155587126269 18297134545064308345172351)
  ·
    refine ⟨27445701817596462517758527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18297134545064308345172351 27445701817596462517758527)
    ·
      refine ⟨41168552726394693776637791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27445701817596462517758527 41168552726394693776637791)
      ·
        refine ⟨61752829089592040664956687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41168552726394693776637791 61752829089592040664956687)
        ·
          refine ⟨92629243634388060997435031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61752829089592040664956687 92629243634388060997435031)
          ·
            refine ⟨138943865451582091496152547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92629243634388060997435031 138943865451582091496152547)
            ·
              refine ⟨208415798177373137244228821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138943865451582091496152547 208415798177373137244228821)
              ·
                refine ⟨4884745269782182904161613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208415798177373137244228821 4884745269782182904161613)
                ·
                  refine ⟨1831779476168318589060605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4884745269782182904161613 1831779476168318589060605)
                  ·
                    refine ⟨686917303563119470897727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831779476168318589060605 686917303563119470897727)
                    ·
                      rfl

theorem cell22_2006650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_2006650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006650 prefixEnd_2006650 := by exact prefixLift 2006650
  have htrace : WordTrace (prefixWord ++ tailWord_2006650) baseStart_2006650 baseEnd_2006650 := by
    simpa [prefixWord, tailWord_2006650, baseEnd_2006650] using wordTrace_append hprefix tailTrace_2006650
  have hstable : (prefixWord ++ tailWord_2006650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006650).length < 2 ^ (prefixWord ++ tailWord_2006650).sum := by decide
  have hdescent : baseEnd_2006650 < baseStart_2006650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006757 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_2006757 : Nat := 118140960795 + 2006757 * 2 ^ 59
def prefixEnd_2006757 : Nat := 4983230072969 + 3 ^ 40 * 2006757 * 2
def baseEnd_2006757 : Nat := 686953931849806858472399

theorem tailTrace_2006757 : CollatzResearch.WordTrace tailWord_2006757 prefixEnd_2006757 686953931849806858472399 := by
  unfold tailWord_2006757
  simp only [CollatzResearch.WordTrace]
  refine ⟨73192440790869590654834525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48794960527246393769889683 73192440790869590654834525)
  ·
    refine ⟨27447165296576096495562947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73192440790869590654834525 27447165296576096495562947)
    ·
      refine ⟨41170747944864144743344421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27447165296576096495562947 41170747944864144743344421)
      ·
        refine ⟨7719515239662027139377079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41170747944864144743344421 7719515239662027139377079)
        ·
          refine ⟨11579272859493040709065619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719515239662027139377079 11579272859493040709065619)
          ·
            refine ⟨17368909289239561063598429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579272859493040709065619 17368909289239561063598429)
            ·
              refine ⟨6513340983464835398849411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17368909289239561063598429 6513340983464835398849411)
              ·
                refine ⟨9770011475197253098274117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513340983464835398849411 9770011475197253098274117)
                ·
                  refine ⟨1831877151599484955926397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9770011475197253098274117 1831877151599484955926397)
                  ·
                    refine ⟨686953931849806858472399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831877151599484955926397 686953931849806858472399)
                    ·
                      rfl

theorem cell22_2006757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_2006757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006757 prefixEnd_2006757 := by exact prefixLift 2006757
  have htrace : WordTrace (prefixWord ++ tailWord_2006757) baseStart_2006757 baseEnd_2006757 := by
    simpa [prefixWord, tailWord_2006757, baseEnd_2006757] using wordTrace_append hprefix tailTrace_2006757
  have hstable : (prefixWord ++ tailWord_2006757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006757).length < 2 ^ (prefixWord ++ tailWord_2006757).sum := by decide
  have hdescent : baseEnd_2006757 < baseStart_2006757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006759 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 6]
def baseStart_2006759 : Nat := 118140960795 + 2006759 * 2 ^ 59
def prefixEnd_2006759 : Nat := 4983230072969 + 3 ^ 40 * 2006759 * 2
def baseEnd_2006759 : Nat := 228984872163559839974131

theorem tailTrace_2006759 : CollatzResearch.WordTrace tailWord_2006759 prefixEnd_2006759 228984872163559839974131 := by
  unfold tailWord_2006759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73192513736862344996407331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48795009157908229997604887 73192513736862344996407331)
  ·
    refine ⟨109788770605293517494610997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73192513736862344996407331 109788770605293517494610997)
    ·
      refine ⟨10292697244246267265119781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109788770605293517494610997 10292697244246267265119781)
      ·
        refine ⟨1929880733296175112209959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10292697244246267265119781 1929880733296175112209959)
        ·
          refine ⟨2894821099944262668314939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929880733296175112209959 2894821099944262668314939)
          ·
            refine ⟨4342231649916394002472409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894821099944262668314939 4342231649916394002472409)
            ·
              refine ⟨3256673737437295501854307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342231649916394002472409 3256673737437295501854307)
              ·
                refine ⟨4885010606155943252781461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256673737437295501854307 4885010606155943252781461)
                ·
                  refine ⟨228984872163559839974131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4885010606155943252781461 228984872163559839974131)
                  ·
                    rfl

theorem cell22_2006759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].length) (baseStart_2006759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006759 prefixEnd_2006759 := by exact prefixLift 2006759
  have htrace : WordTrace (prefixWord ++ tailWord_2006759) baseStart_2006759 baseEnd_2006759 := by
    simpa [prefixWord, tailWord_2006759, baseEnd_2006759] using wordTrace_append hprefix tailTrace_2006759
  have hstable : (prefixWord ++ tailWord_2006759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006759).length < 2 ^ (prefixWord ++ tailWord_2006759).sum := by decide
  have hdescent : baseEnd_2006759 < baseStart_2006759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006770 : List Nat := [3, 2, 1, 3, 1, 1, 2, 9]
def baseStart_2006770 : Nat := 118140960795 + 2006770 * 2 ^ 59
def prefixEnd_2006770 : Nat := 4983230072969 + 3 ^ 40 * 2006770 * 2
def baseEnd_2006770 : Nat := 76328709112831017544151

theorem tailTrace_2006770 : CollatzResearch.WordTrace tailWord_2006770 prefixEnd_2006770 76328709112831017544151 := by
  unfold tailWord_2006770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18298228734955623468764441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48795276626548329250038509 18298228734955623468764441)
  ·
    refine ⟨13723671551216717601573331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18298228734955623468764441 13723671551216717601573331)
    ·
      refine ⟨20585507326825076402359997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13723671551216717601573331 20585507326825076402359997)
      ·
        refine ⟨7719565247559403650884999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20585507326825076402359997 7719565247559403650884999)
        ·
          refine ⟨11579347871339105476327499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719565247559403650884999 11579347871339105476327499)
          ·
            refine ⟨17369021807008658214491249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579347871339105476327499 17369021807008658214491249)
            ·
              refine ⟨13026766355256493660868437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369021807008658214491249 13026766355256493660868437)
              ·
                refine ⟨76328709112831017544151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13026766355256493660868437 76328709112831017544151)
                ·
                  rfl

theorem cell22_2006770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_2006770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006770 prefixEnd_2006770 := by exact prefixLift 2006770
  have htrace : WordTrace (prefixWord ++ tailWord_2006770) baseStart_2006770 baseEnd_2006770 := by
    simpa [prefixWord, tailWord_2006770, baseEnd_2006770] using wordTrace_append hprefix tailTrace_2006770
  have hstable : (prefixWord ++ tailWord_2006770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006770).length < 2 ^ (prefixWord ++ tailWord_2006770).sum := by decide
  have hdescent : baseEnd_2006770 < baseStart_2006770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006774 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2006774 : Nat := 118140960795 + 2006774 * 2 ^ 59
def prefixEnd_2006774 : Nat := 4983230072969 + 3 ^ 40 * 2006774 * 2
def baseEnd_2006774 : Nat := 686959751297224480797347

theorem tailTrace_2006774 : CollatzResearch.WordTrace tailWord_2006774 prefixEnd_2006774 686959751297224480797347 := by
  unfold tailWord_2006774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574566301988000159887711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48795373887872001705468917 4574566301988000159887711)
  ·
    refine ⟨6861849452982000239831567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574566301988000159887711 6861849452982000239831567)
    ·
      refine ⟨10292774179473000359747351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861849452982000239831567 10292774179473000359747351)
      ·
        refine ⟨15439161269209500539621027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292774179473000359747351 15439161269209500539621027)
        ·
          refine ⟨23158741903814250809431541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15439161269209500539621027 23158741903814250809431541)
          ·
            refine ⟨2171132053482586013384207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23158741903814250809431541 2171132053482586013384207)
            ·
              refine ⟨3256698080223879020076311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171132053482586013384207 3256698080223879020076311)
              ·
                refine ⟨4885047120335818530114467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256698080223879020076311 4885047120335818530114467)
                ·
                  refine ⟨7327570680503727795171701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885047120335818530114467 7327570680503727795171701)
                  ·
                    refine ⟨686959751297224480797347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7327570680503727795171701 686959751297224480797347)
                    ·
                      rfl

theorem cell22_2006774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2006774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006774 prefixEnd_2006774 := by exact prefixLift 2006774
  have htrace : WordTrace (prefixWord ++ tailWord_2006774) baseStart_2006774 baseEnd_2006774 := by
    simpa [prefixWord, tailWord_2006774, baseEnd_2006774] using wordTrace_append hprefix tailTrace_2006774
  have hstable : (prefixWord ++ tailWord_2006774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006774).length < 2 ^ (prefixWord ++ tailWord_2006774).sum := by decide
  have hdescent : baseEnd_2006774 < baseStart_2006774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006815 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 7]
def baseStart_2006815 : Nat := 118140960795 + 2006815 * 2 ^ 59
def prefixEnd_2006815 : Nat := 4983230072969 + 3 ^ 40 * 2006815 * 2
def baseEnd_2006815 : Nat := 228991262145038013507407

theorem tailTrace_2006815 : CollatzResearch.WordTrace tailWord_2006815 prefixEnd_2006815 228991262145038013507407 := by
  unfold tailWord_2006815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73194556224659466560445899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48796370816439644373630599 73194556224659466560445899)
  ·
    refine ⟨109791834336989199840668849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73194556224659466560445899 109791834336989199840668849)
    ·
      refine ⟨82343875752741899880501637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109791834336989199840668849 82343875752741899880501637)
      ·
        refine ⟨15439476703639106227594057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82343875752741899880501637 15439476703639106227594057)
        ·
          refine ⟨11579607527729329670695543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439476703639106227594057 11579607527729329670695543)
          ·
            refine ⟨17369411291593994506043315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11579607527729329670695543 17369411291593994506043315)
            ·
              refine ⟨26054116937390991759064973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17369411291593994506043315 26054116937390991759064973)
              ·
                refine ⟨9770293851521621909649365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26054116937390991759064973 9770293851521621909649365)
                ·
                  refine ⟨228991262145038013507407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9770293851521621909649365 228991262145038013507407)
                  ·
                    rfl

theorem cell22_2006815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_2006815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006815 prefixEnd_2006815 := by exact prefixLift 2006815
  have htrace : WordTrace (prefixWord ++ tailWord_2006815) baseStart_2006815 baseEnd_2006815 := by
    simpa [prefixWord, tailWord_2006815, baseEnd_2006815] using wordTrace_append hprefix tailTrace_2006815
  have hstable : (prefixWord ++ tailWord_2006815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006815).length < 2 ^ (prefixWord ++ tailWord_2006815).sum := by decide
  have hdescent : baseEnd_2006815 < baseStart_2006815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006819 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 1, 3]
def baseStart_2006819 : Nat := 118140960795 + 2006819 * 2 ^ 59
def prefixEnd_2006819 : Nat := 4983230072969 + 3 ^ 40 * 2006819 * 2
def baseEnd_2006819 : Nat := 686975155716859363422209

theorem tailTrace_2006819 : CollatzResearch.WordTrace tailWord_2006819 prefixEnd_2006819 686975155716859363422209 := by
  unfold tailWord_2006819
  simp only [CollatzResearch.WordTrace]
  refine ⟨73194702116644975243591511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48796468077763316829061007 73194702116644975243591511)
  ·
    refine ⟨109792053174967462865387267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73194702116644975243591511 109792053174967462865387267)
    ·
      refine ⟨164688079762451194298080901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109792053174967462865387267 164688079762451194298080901)
      ·
        refine ⟨30879014955459598930890169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164688079762451194298080901 30879014955459598930890169)
        ·
          refine ⟨23159261216594699198167627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30879014955459598930890169 23159261216594699198167627)
          ·
            refine ⟨34738891824892048797251441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23159261216594699198167627 34738891824892048797251441)
            ·
              refine ⟨26054168868669036597938581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34738891824892048797251441 26054168868669036597938581)
              ·
                refine ⟨1221289165718861090528371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26054168868669036597938581 1221289165718861090528371)
                ·
                  refine ⟨1831933748578291635792557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221289165718861090528371 1831933748578291635792557)
                  ·
                    refine ⟨686975155716859363422209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831933748578291635792557 686975155716859363422209)
                    ·
                      rfl

theorem cell22_2006819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 3].length) (baseStart_2006819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006819 prefixEnd_2006819 := by exact prefixLift 2006819
  have htrace : WordTrace (prefixWord ++ tailWord_2006819) baseStart_2006819 baseEnd_2006819 := by
    simpa [prefixWord, tailWord_2006819, baseEnd_2006819] using wordTrace_append hprefix tailTrace_2006819
  have hstable : (prefixWord ++ tailWord_2006819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006819).length < 2 ^ (prefixWord ++ tailWord_2006819).sum := by decide
  have hdescent : baseEnd_2006819 < baseStart_2006819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006892 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_2006892 : Nat := 118140960795 + 2006892 * 2 ^ 59
def prefixEnd_2006892 : Nat := 4983230072969 + 3 ^ 40 * 2006892 * 2
def baseEnd_2006892 : Nat := 687000145108711506346985

theorem tailTrace_2006892 : CollatzResearch.WordTrace tailWord_2006892 prefixEnd_2006892 687000145108711506346985 := by
  unfold tailWord_2006892
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598682322690254355499465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48798243096920339140665953 36598682322690254355499465)
  ·
    refine ⟨27449011742017690766624599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36598682322690254355499465 27449011742017690766624599)
    ·
      refine ⟨41173517613026536149936899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449011742017690766624599 41173517613026536149936899)
      ·
        refine ⟨61760276419539804224905349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41173517613026536149936899 61760276419539804224905349)
        ·
          refine ⟨11580051828663713292169753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61760276419539804224905349 11580051828663713292169753)
          ·
            refine ⟨8685038871497784969127315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580051828663713292169753 8685038871497784969127315)
            ·
              refine ⟨13027558307246677453690973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685038871497784969127315 13027558307246677453690973)
              ·
                refine ⟨4885334365217504045134115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13027558307246677453690973 4885334365217504045134115)
                ·
                  refine ⟨7328001547826256067701173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885334365217504045134115 7328001547826256067701173)
                  ·
                    refine ⟨687000145108711506346985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7328001547826256067701173 687000145108711506346985)
                    ·
                      rfl

theorem cell22_2006892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_2006892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006892 prefixEnd_2006892 := by exact prefixLift 2006892
  have htrace : WordTrace (prefixWord ++ tailWord_2006892) baseStart_2006892 baseEnd_2006892 := by
    simpa [prefixWord, tailWord_2006892, baseEnd_2006892] using wordTrace_append hprefix tailTrace_2006892
  have hstable : (prefixWord ++ tailWord_2006892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006892).length < 2 ^ (prefixWord ++ tailWord_2006892).sum := by decide
  have hdescent : baseEnd_2006892 < baseStart_2006892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006894 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2006894 : Nat := 118140960795 + 2006894 * 2 ^ 59
def prefixEnd_2006894 : Nat := 4983230072969 + 3 ^ 40 * 2006894 * 2
def baseEnd_2006894 : Nat := 229000276583194722598993

theorem tailTrace_2006894 : CollatzResearch.WordTrace tailWord_2006894 prefixEnd_2006894 229000276583194722598993 := by
  unfold tailWord_2006894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149679698921657881571467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48798291727582175368381157 9149679698921657881571467)
  ·
    refine ⟨13724519548382486822357201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149679698921657881571467 13724519548382486822357201)
    ·
      refine ⟨10293389661286865116767901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13724519548382486822357201 10293389661286865116767901)
      ·
        refine ⟨3860021122982574418787963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10293389661286865116767901 3860021122982574418787963)
        ·
          refine ⟨5790031684473861628181945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860021122982574418787963 5790031684473861628181945)
          ·
            refine ⟨4342523763355396221136459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5790031684473861628181945 4342523763355396221136459)
            ·
              refine ⟨6513785645033094331704689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342523763355396221136459 6513785645033094331704689)
              ·
                refine ⟨4885339233774820748778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513785645033094331704689 4885339233774820748778517)
                ·
                  refine ⟨229000276583194722598993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4885339233774820748778517 229000276583194722598993)
                  ·
                    rfl

theorem cell22_2006894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2006894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006894 prefixEnd_2006894 := by exact prefixLift 2006894
  have htrace : WordTrace (prefixWord ++ tailWord_2006894) baseStart_2006894 baseEnd_2006894 := by
    simpa [prefixWord, tailWord_2006894, baseEnd_2006894] using wordTrace_append hprefix tailTrace_2006894
  have hstable : (prefixWord ++ tailWord_2006894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006894).length < 2 ^ (prefixWord ++ tailWord_2006894).sum := by decide
  have hdescent : baseEnd_2006894 < baseStart_2006894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006943 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 2, 3]
def baseStart_2006943 : Nat := 118140960795 + 2006943 * 2 ^ 59
def prefixEnd_2006943 : Nat := 4983230072969 + 3 ^ 40 * 2006943 * 2
def baseEnd_2006943 : Nat := 687017603450964373321829

theorem tailTrace_2006943 : CollatzResearch.WordTrace tailWord_2006943 prefixEnd_2006943 687017603450964373321829 := by
  unfold tailWord_2006943
  simp only [CollatzResearch.WordTrace]
  refine ⟨73199224768195744421105483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48799483178797162947403655 73199224768195744421105483)
  ·
    refine ⟨109798837152293616631658225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73199224768195744421105483 109798837152293616631658225)
    ·
      refine ⟨82349127864220212473743669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109798837152293616631658225 82349127864220212473743669)
      ·
        refine ⟨7720230737270644919413469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82349127864220212473743669 7720230737270644919413469)
        ·
          refine ⟨2895086526476491844780051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7720230737270644919413469 2895086526476491844780051)
          ·
            refine ⟨4342629789714737767170077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895086526476491844780051 4342629789714737767170077)
            ·
              refine ⟨1628486171143026662688779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4342629789714737767170077 1628486171143026662688779)
              ·
                refine ⟨2442729256714539994033169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628486171143026662688779 2442729256714539994033169)
                ·
                  refine ⟨1832046942535904995524877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2442729256714539994033169 1832046942535904995524877)
                  ·
                    refine ⟨687017603450964373321829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832046942535904995524877 687017603450964373321829)
                    ·
                      rfl

theorem cell22_2006943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_2006943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006943 prefixEnd_2006943 := by exact prefixLift 2006943
  have htrace : WordTrace (prefixWord ++ tailWord_2006943) baseStart_2006943 baseEnd_2006943 := by
    simpa [prefixWord, tailWord_2006943, baseEnd_2006943] using wordTrace_append hprefix tailTrace_2006943
  have hstable : (prefixWord ++ tailWord_2006943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006943).length < 2 ^ (prefixWord ++ tailWord_2006943).sum := by decide
  have hdescent : baseEnd_2006943 < baseStart_2006943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007012 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2007012 : Nat := 118140960795 + 2007012 * 2 ^ 59
def prefixEnd_2007012 : Nat := 4983230072969 + 3 ^ 40 * 2007012 * 2
def baseEnd_2007012 : Nat := 229013741187023731115539

theorem tailTrace_2007012 : CollatzResearch.WordTrace tailWord_2007012 prefixEnd_2007012 229013741187023731115539 := by
  unfold tailWord_2007012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36600870702472884602683645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48801160936630512803578193 36600870702472884602683645)
  ·
    refine ⟨13725326513427331726006367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36600870702472884602683645 13725326513427331726006367)
    ·
      refine ⟨20587989770140997589009551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13725326513427331726006367 20587989770140997589009551)
      ·
        refine ⟨30881984655211496383514327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20587989770140997589009551 30881984655211496383514327)
        ·
          refine ⟨46322976982817244575271491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30881984655211496383514327 46322976982817244575271491)
          ·
            refine ⟨69484465474225866862907237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46322976982817244575271491 69484465474225866862907237)
            ·
              refine ⟨13028337276417350036795107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69484465474225866862907237 13028337276417350036795107)
              ·
                refine ⟨19542505914626025055192661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13028337276417350036795107 19542505914626025055192661)
                ·
                  refine ⟨229013741187023731115539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19542505914626025055192661 229013741187023731115539)
                  ·
                    rfl

theorem cell22_2007012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2007012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007012 prefixEnd_2007012 := by exact prefixLift 2007012
  have htrace : WordTrace (prefixWord ++ tailWord_2007012) baseStart_2007012 baseEnd_2007012 := by
    simpa [prefixWord, tailWord_2007012, baseEnd_2007012] using wordTrace_append hprefix tailTrace_2007012
  have hstable : (prefixWord ++ tailWord_2007012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007012).length < 2 ^ (prefixWord ++ tailWord_2007012).sum := by decide
  have hdescent : baseEnd_2007012 < baseStart_2007012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007061 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2007061 : Nat := 118140960795 + 2007061 * 2 ^ 59
def prefixEnd_2007061 : Nat := 4983230072969 + 3 ^ 40 * 2007061 * 2
def baseEnd_2007061 : Nat := 687057997262451398871467

theorem tailTrace_2007061 : CollatzResearch.WordTrace tailWord_2007061 prefixEnd_2007061 687057997262451398871467 := by
  unfold tailWord_2007061
  simp only [CollatzResearch.WordTrace]
  refine ⟨73203528581768250573901037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48802352387845500382600691 73203528581768250573901037)
  ·
    refine ⟨27451323218163093965212889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73203528581768250573901037 27451323218163093965212889)
    ·
      refine ⟨20588492413622320473909667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27451323218163093965212889 20588492413622320473909667)
      ·
        refine ⟨30882738620433480710864501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20588492413622320473909667 30882738620433480710864501)
        ·
          refine ⟨2895256745665638816643547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30882738620433480710864501 2895256745665638816643547)
          ·
            refine ⟨4342885118498458224965321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895256745665638816643547 4342885118498458224965321)
            ·
              refine ⟨3257163838873843668723991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342885118498458224965321 3257163838873843668723991)
              ·
                refine ⟨4885745758310765503085987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257163838873843668723991 4885745758310765503085987)
                ·
                  refine ⟨7328618637466148254628981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885745758310765503085987 7328618637466148254628981)
                  ·
                    refine ⟨687057997262451398871467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7328618637466148254628981 687057997262451398871467)
                    ·
                      rfl

theorem cell22_2007061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2007061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007061 prefixEnd_2007061 := by exact prefixLift 2007061
  have htrace : WordTrace (prefixWord ++ tailWord_2007061) baseStart_2007061 baseEnd_2007061 := by
    simpa [prefixWord, tailWord_2007061, baseEnd_2007061] using wordTrace_append hprefix tailTrace_2007061
  have hstable : (prefixWord ++ tailWord_2007061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007061).length < 2 ^ (prefixWord ++ tailWord_2007061).sum := by decide
  have hdescent : baseEnd_2007061 < baseStart_2007061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007076 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2007076 : Nat := 118140960795 + 2007076 * 2 ^ 59
def prefixEnd_2007076 : Nat := 4983230072969 + 3 ^ 40 * 2007076 * 2
def baseEnd_2007076 : Nat := 687063132068996359746421

theorem tailTrace_2007076 : CollatzResearch.WordTrace tailWord_2007076 prefixEnd_2007076 687063132068996359746421 := by
  unfold tailWord_2007076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602037838356954067848541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48802717117809272090464721 36602037838356954067848541)
  ·
    refine ⟨13725764189383857775443203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36602037838356954067848541 13725764189383857775443203)
    ·
      refine ⟨20588646284075786663164805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13725764189383857775443203 20588646284075786663164805)
      ·
        refine ⟨3860371178264209999343401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20588646284075786663164805 3860371178264209999343401)
        ·
          refine ⟨2895278383698157499507551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860371178264209999343401 2895278383698157499507551)
          ·
            refine ⟨4342917575547236249261327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895278383698157499507551 4342917575547236249261327)
            ·
              refine ⟨6514376363320854373891991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342917575547236249261327 6514376363320854373891991)
              ·
                refine ⟨9771564544981281560837987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514376363320854373891991 9771564544981281560837987)
                ·
                  refine ⟨14657346817471922341256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771564544981281560837987 14657346817471922341256981)
                  ·
                    refine ⟨687063132068996359746421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14657346817471922341256981 687063132068996359746421)
                    ·
                      rfl

theorem cell22_2007076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2007076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007076 prefixEnd_2007076 := by exact prefixLift 2007076
  have htrace : WordTrace (prefixWord ++ tailWord_2007076) baseStart_2007076 baseEnd_2007076 := by
    simpa [prefixWord, tailWord_2007076, baseEnd_2007076] using wordTrace_append hprefix tailTrace_2007076
  have hstable : (prefixWord ++ tailWord_2007076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007076).length < 2 ^ (prefixWord ++ tailWord_2007076).sum := by decide
  have hdescent : baseEnd_2007076 < baseStart_2007076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007080 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_2007080 : Nat := 118140960795 + 2007080 * 2 ^ 59
def prefixEnd_2007080 : Nat := 4983230072969 + 3 ^ 40 * 2007080 * 2
def baseEnd_2007080 : Nat := 229021500450247227548803

theorem tailTrace_2007080 : CollatzResearch.WordTrace tailWord_2007080 prefixEnd_2007080 229021500450247227548803 := by
  unfold tailWord_2007080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602110784349708409421347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48802814379132944545895129 36602110784349708409421347)
  ·
    refine ⟨54903166176524562614132021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36602110784349708409421347 54903166176524562614132021)
    ·
      refine ⟨5147171829049177745074877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54903166176524562614132021 5147171829049177745074877)
      ·
        refine ⟨1930189435893441654403079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5147171829049177745074877 1930189435893441654403079)
        ·
          refine ⟨2895284153840162481604619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930189435893441654403079 2895284153840162481604619)
          ·
            refine ⟨4342926230760243722406929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895284153840162481604619 4342926230760243722406929)
            ·
              refine ⟨3257194673070182791805197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342926230760243722406929 3257194673070182791805197)
              ·
                refine ⟨1221448002401318546926949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257194673070182791805197 1221448002401318546926949)
                ·
                  refine ⟨229021500450247227548803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221448002401318546926949 229021500450247227548803)
                  ·
                    rfl

theorem cell22_2007080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_2007080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007080 prefixEnd_2007080 := by exact prefixLift 2007080
  have htrace : WordTrace (prefixWord ++ tailWord_2007080) baseStart_2007080 baseEnd_2007080 := by
    simpa [prefixWord, tailWord_2007080, baseEnd_2007080] using wordTrace_append hprefix tailTrace_2007080
  have hstable : (prefixWord ++ tailWord_2007080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007080).length < 2 ^ (prefixWord ++ tailWord_2007080).sum := by decide
  have hdescent : baseEnd_2007080 < baseStart_2007080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007087 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_2007087 : Nat := 118140960795 + 2007087 * 2 ^ 59
def prefixEnd_2007087 : Nat := 4983230072969 + 3 ^ 40 * 2007087 * 2
def baseEnd_2007087 : Nat := 687066897593795997721387

theorem tailTrace_2007087 : CollatzResearch.WordTrace tailWord_2007087 prefixEnd_2007087 687066897593795997721387 := by
  unfold tailWord_2007087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73204476879674057014347515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48802984586449371342898343 73204476879674057014347515)
  ·
    refine ⟨109806715319511085521521273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73204476879674057014347515 109806715319511085521521273)
    ·
      refine ⟨82355036489633314141140955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109806715319511085521521273 82355036489633314141140955)
      ·
        refine ⟨123532554734449971211711433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82355036489633314141140955 123532554734449971211711433)
        ·
          refine ⟨92649416050837478408783575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123532554734449971211711433 92649416050837478408783575)
          ·
            refine ⟨138974124076256217613175363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92649416050837478408783575 138974124076256217613175363)
            ·
              refine ⟨208461186114384326419763045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138974124076256217613175363 208461186114384326419763045)
              ·
                refine ⟨39086472396447061203705571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208461186114384326419763045 39086472396447061203705571)
                ·
                  refine ⟨58629708594670591805558357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39086472396447061203705571 58629708594670591805558357)
                  ·
                    refine ⟨687066897593795997721387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58629708594670591805558357 687066897593795997721387)
                    ·
                      rfl

theorem cell22_2007087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_2007087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007087 prefixEnd_2007087 := by exact prefixLift 2007087
  have htrace : WordTrace (prefixWord ++ tailWord_2007087) baseStart_2007087 baseEnd_2007087 := by
    simpa [prefixWord, tailWord_2007087, baseEnd_2007087] using wordTrace_append hprefix tailTrace_2007087
  have hstable : (prefixWord ++ tailWord_2007087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007087).length < 2 ^ (prefixWord ++ tailWord_2007087).sum := by decide
  have hdescent : baseEnd_2007087 < baseStart_2007087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007196 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2007196 : Nat := 118140960795 + 2007196 * 2 ^ 59
def prefixEnd_2007196 : Nat := 4983230072969 + 3 ^ 40 * 2007196 * 2
def baseEnd_2007196 : Nat := 687104210521356046746053

theorem tailTrace_2007196 : CollatzResearch.WordTrace tailWord_2007196 prefixEnd_2007196 687104210521356046746053 := by
  unfold tailWord_2007196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36604226218139584315032721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48805634957519445753376961 36604226218139584315032721)
  ·
    refine ⟨27453169663604688236274541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36604226218139584315032721 27453169663604688236274541)
    ·
      refine ⟨10294938623851758088602953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27453169663604688236274541 10294938623851758088602953)
      ·
        refine ⟨7721203967888818566452215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10294938623851758088602953 7721203967888818566452215)
        ·
          refine ⟨11581805951833227849678323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721203967888818566452215 11581805951833227849678323)
          ·
            refine ⟨17372708927749841774517485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11581805951833227849678323 17372708927749841774517485)
            ·
              refine ⟨6514765847906190665444057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17372708927749841774517485 6514765847906190665444057)
              ·
                refine ⟨4886074385929642999083043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514765847906190665444057 4886074385929642999083043)
                ·
                  refine ⟨7329111578894464498624565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886074385929642999083043 7329111578894464498624565)
                  ·
                    refine ⟨687104210521356046746053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7329111578894464498624565 687104210521356046746053)
                    ·
                      rfl

theorem cell22_2007196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2007196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007196 prefixEnd_2007196 := by exact prefixLift 2007196
  have htrace : WordTrace (prefixWord ++ tailWord_2007196) baseStart_2007196 baseEnd_2007196 := by
    simpa [prefixWord, tailWord_2007196, baseEnd_2007196] using wordTrace_append hprefix tailTrace_2007196
  have hstable : (prefixWord ++ tailWord_2007196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007196).length < 2 ^ (prefixWord ++ tailWord_2007196).sum := by decide
  have hdescent : baseEnd_2007196 < baseStart_2007196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007326 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2007326 : Nat := 118140960795 + 2007326 * 2 ^ 59
def prefixEnd_2007326 : Nat := 4983230072969 + 3 ^ 40 * 2007326 * 2
def baseEnd_2007326 : Nat := 687148712178079040995655

theorem tailTrace_2007326 : CollatzResearch.WordTrace tailWord_2007326 prefixEnd_2007326 687148712178079040995655 := by
  unfold tailWord_2007326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151649240726025104037229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48808795950538800554865221 9151649240726025104037229)
  ·
    refine ⟨3431868465272259414013961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9151649240726025104037229 3431868465272259414013961)
    ·
      refine ⟨2573901348954194560510471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3431868465272259414013961 2573901348954194560510471)
      ·
        refine ⟨3860852023431291840765707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573901348954194560510471 3860852023431291840765707)
        ·
          refine ⟨5791278035146937761148561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860852023431291840765707 5791278035146937761148561)
          ·
            refine ⟨4343458526360203320861421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791278035146937761148561 4343458526360203320861421)
            ·
              refine ⟨1628796947385076245323033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343458526360203320861421 1628796947385076245323033)
              ·
                refine ⟨1221597710538807183992275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628796947385076245323033 1221597710538807183992275)
                ·
                  refine ⟨1832396565808210775988413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221597710538807183992275 1832396565808210775988413)
                  ·
                    refine ⟨687148712178079040995655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832396565808210775988413 687148712178079040995655)
                    ·
                      rfl

theorem cell22_2007326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2007326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007326 prefixEnd_2007326 := by exact prefixLift 2007326
  have htrace : WordTrace (prefixWord ++ tailWord_2007326) baseStart_2007326 baseEnd_2007326 := by
    simpa [prefixWord, tailWord_2007326, baseEnd_2007326] using wordTrace_append hprefix tailTrace_2007326
  have hstable : (prefixWord ++ tailWord_2007326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007326).length < 2 ^ (prefixWord ++ tailWord_2007326).sum := by decide
  have hdescent : baseEnd_2007326 < baseStart_2007326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007391 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_2007391 : Nat := 118140960795 + 2007391 * 2 ^ 59
def prefixEnd_2007391 : Nat := 4983230072969 + 3 ^ 40 * 2007391 * 2
def baseEnd_2007391 : Nat := 687170963006440538120455

theorem tailTrace_2007391 : CollatzResearch.WordTrace tailWord_2007391 prefixEnd_2007391 687170963006440538120455 := by
  unfold tailWord_2007391
  simp only [CollatzResearch.WordTrace]
  refine ⟨73215564670572716933414027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48810376447048477955609351 73215564670572716933414027)
  ·
    refine ⟨109823347005859075400121041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73215564670572716933414027 109823347005859075400121041)
    ·
      refine ⟨82367510254394306550090781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109823347005859075400121041 82367510254394306550090781)
      ·
        refine ⟨30887816345397864956284043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82367510254394306550090781 30887816345397864956284043)
        ·
          refine ⟨46331724518096797434426065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887816345397864956284043 46331724518096797434426065)
          ·
            refine ⟨34748793388572598075819549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46331724518096797434426065 34748793388572598075819549)
            ·
              refine ⟨13030797520714724278432331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34748793388572598075819549 13030797520714724278432331)
              ·
                refine ⟨19546196281072086417648497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13030797520714724278432331 19546196281072086417648497)
                ·
                  refine ⟨14659647210804064813236373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19546196281072086417648497 14659647210804064813236373)
                  ·
                    refine ⟨687170963006440538120455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14659647210804064813236373 687170963006440538120455)
                    ·
                      rfl

theorem cell22_2007391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_2007391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007391 prefixEnd_2007391 := by exact prefixLift 2007391
  have htrace : WordTrace (prefixWord ++ tailWord_2007391) baseStart_2007391 baseEnd_2007391 := by
    simpa [prefixWord, tailWord_2007391, baseEnd_2007391] using wordTrace_append hprefix tailTrace_2007391
  have hstable : (prefixWord ++ tailWord_2007391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007391).length < 2 ^ (prefixWord ++ tailWord_2007391).sum := by decide
  have hdescent : baseEnd_2007391 < baseStart_2007391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007410 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2007410 : Nat := 118140960795 + 2007410 * 2 ^ 59
def prefixEnd_2007410 : Nat := 4983230072969 + 3 ^ 40 * 2007410 * 2
def baseEnd_2007410 : Nat := 687177467094730821895397

theorem tailTrace_2007410 : CollatzResearch.WordTrace tailWord_2007410 prefixEnd_2007410 687177467094730821895397 := by
  unfold tailWord_2007410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304064414375970794588921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48810838438335922118903789 18304064414375970794588921)
  ·
    refine ⟨13728048310781978095941691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18304064414375970794588921 13728048310781978095941691)
    ·
      refine ⟨20592072466172967143912537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13728048310781978095941691 20592072466172967143912537)
      ·
        refine ⟨15444054349629725357934403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20592072466172967143912537 15444054349629725357934403)
        ·
          refine ⟨23166081524444588036901605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444054349629725357934403 23166081524444588036901605)
          ·
            refine ⟨4343640285833360256919051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23166081524444588036901605 4343640285833360256919051)
            ·
              refine ⟨6515460428750040385378577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343640285833360256919051 6515460428750040385378577)
              ·
                refine ⟨4886595321562530289033933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515460428750040385378577 4886595321562530289033933)
                ·
                  refine ⟨1832473245585948858387725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4886595321562530289033933 1832473245585948858387725)
                  ·
                    refine ⟨687177467094730821895397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832473245585948858387725 687177467094730821895397)
                    ·
                      rfl

theorem cell22_2007410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2007410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007410 prefixEnd_2007410 := by exact prefixLift 2007410
  have htrace : WordTrace (prefixWord ++ tailWord_2007410) baseStart_2007410 baseEnd_2007410 := by
    simpa [prefixWord, tailWord_2007410, baseEnd_2007410] using wordTrace_append hprefix tailTrace_2007410
  have hstable : (prefixWord ++ tailWord_2007410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007410).length < 2 ^ (prefixWord ++ tailWord_2007410).sum := by decide
  have hdescent : baseEnd_2007410 < baseStart_2007410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007414 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2007414 : Nat := 118140960795 + 2007414 * 2 ^ 59
def prefixEnd_2007414 : Nat := 4983230072969 + 3 ^ 40 * 2007414 * 2
def baseEnd_2007414 : Nat := 687178836376476144795385

theorem tailTrace_2007414 : CollatzResearch.WordTrace tailWord_2007414 prefixEnd_2007414 687178836376476144795385 := by
  unfold tailWord_2007414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576025221843086991343831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48810935699659594574334197 4576025221843086991343831)
  ·
    refine ⟨6864037832764630487015747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4576025221843086991343831 6864037832764630487015747)
    ·
      refine ⟨10296056749146945730523621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864037832764630487015747 10296056749146945730523621)
      ·
        refine ⟨1930510640465052324473179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10296056749146945730523621 1930510640465052324473179)
        ·
          refine ⟨2895765960697578486709769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930510640465052324473179 2895765960697578486709769)
          ·
            refine ⟨2171824470523183865032327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2895765960697578486709769 2171824470523183865032327)
            ·
              refine ⟨3257736705784775797548491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171824470523183865032327 3257736705784775797548491)
              ·
                refine ⟨4886605058677163696322737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257736705784775797548491 4886605058677163696322737)
                ·
                  refine ⟨3664953794007872772242053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886605058677163696322737 3664953794007872772242053)
                  ·
                    refine ⟨687178836376476144795385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664953794007872772242053 687178836376476144795385)
                    ·
                      rfl

theorem cell22_2007414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2007414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007414 prefixEnd_2007414 := by exact prefixLift 2007414
  have htrace : WordTrace (prefixWord ++ tailWord_2007414) baseStart_2007414 baseEnd_2007414 := by
    simpa [prefixWord, tailWord_2007414, baseEnd_2007414] using wordTrace_append hprefix tailTrace_2007414
  have hstable : (prefixWord ++ tailWord_2007414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007414).length < 2 ^ (prefixWord ++ tailWord_2007414).sum := by decide
  have hdescent : baseEnd_2007414 < baseStart_2007414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007513 : List Nat := [1, 2, 1, 2, 4, 1, 4, 7]
def baseStart_2007513 : Nat := 118140960795 + 2007513 * 2 ^ 59
def prefixEnd_2007513 : Nat := 4983230072969 + 3 ^ 40 * 2007513 * 2
def baseEnd_2007513 : Nat := 76356969566630320730009

theorem tailTrace_2007513 : CollatzResearch.WordTrace tailWord_2007513 prefixEnd_2007513 76356969566630320730009 := by
  unfold tailWord_2007513
  simp only [CollatzResearch.WordTrace]
  refine ⟨73220014376130731769355193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48813342917420487846236795 73220014376130731769355193)
  ·
    refine ⟨54915010782098048827016395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73220014376130731769355193 54915010782098048827016395)
    ·
      refine ⟨82372516173147073240524593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54915010782098048827016395 82372516173147073240524593)
      ·
        refine ⟨61779387129860304930393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82372516173147073240524593 61779387129860304930393445)
        ·
          refine ⟨11583635086848807174448771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61779387129860304930393445 11583635086848807174448771)
          ·
            refine ⟨17375452630273210761673157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583635086848807174448771 17375452630273210761673157)
            ·
              refine ⟨3257897368176227017813717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17375452630273210761673157 3257897368176227017813717)
              ·
                refine ⟨76356969566630320730009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3257897368176227017813717 76356969566630320730009)
                ·
                  rfl

theorem cell22_2007513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 7].length) (baseStart_2007513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007513 prefixEnd_2007513 := by exact prefixLift 2007513
  have htrace : WordTrace (prefixWord ++ tailWord_2007513) baseStart_2007513 baseEnd_2007513 := by
    simpa [prefixWord, tailWord_2007513, baseEnd_2007513] using wordTrace_append hprefix tailTrace_2007513
  have hstable : (prefixWord ++ tailWord_2007513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007513).length < 2 ^ (prefixWord ++ tailWord_2007513).sum := by decide
  have hdescent : baseEnd_2007513 < baseStart_2007513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007517 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2007517 : Nat := 118140960795 + 2007517 * 2 ^ 59
def prefixEnd_2007517 : Nat := 4983230072969 + 3 ^ 40 * 2007517 * 2
def baseEnd_2007517 : Nat := 687214095381418209470069

theorem tailTrace_2007517 : CollatzResearch.WordTrace tailWord_2007517 prefixEnd_2007517 687214095381418209470069 := by
  unfold tailWord_2007517
  simp only [CollatzResearch.WordTrace]
  refine ⟨73220160268116240452500805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48813440178744160301667203 73220160268116240452500805)
  ·
    refine ⟨13728780050271795084843901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73220160268116240452500805 13728780050271795084843901)
    ·
      refine ⟨5148292518851923156816463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13728780050271795084843901 5148292518851923156816463)
      ·
        refine ⟨7722438778277884735224695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148292518851923156816463 7722438778277884735224695)
        ·
          refine ⟨11583658167416827102837043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722438778277884735224695 11583658167416827102837043)
          ·
            refine ⟨17375487251125240654255565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583658167416827102837043 17375487251125240654255565)
            ·
              refine ⟨6515807719171965245345837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17375487251125240654255565 6515807719171965245345837)
              ·
                refine ⟨2443427894689486967004689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515807719171965245345837 2443427894689486967004689)
                ·
                  refine ⟨1832570921017115225253517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443427894689486967004689 1832570921017115225253517)
                  ·
                    refine ⟨687214095381418209470069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832570921017115225253517 687214095381418209470069)
                    ·
                      rfl

theorem cell22_2007517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2007517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007517 prefixEnd_2007517 := by exact prefixLift 2007517
  have htrace : WordTrace (prefixWord ++ tailWord_2007517) baseStart_2007517 baseEnd_2007517 := by
    simpa [prefixWord, tailWord_2007517, baseEnd_2007517] using wordTrace_append hprefix tailTrace_2007517
  have hstable : (prefixWord ++ tailWord_2007517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007517).length < 2 ^ (prefixWord ++ tailWord_2007517).sum := by decide
  have hdescent : baseEnd_2007517 < baseStart_2007517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007603 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 8]
def baseStart_2007603 : Nat := 118140960795 + 2007603 * 2 ^ 59
def prefixEnd_2007603 : Nat := 4983230072969 + 3 ^ 40 * 2007603 * 2
def baseEnd_2007603 : Nat := 229081178312980883939935

theorem tailTrace_2007603 : CollatzResearch.WordTrace tailWord_2007603 prefixEnd_2007603 229081178312980883939935 := by
  unfold tailWord_2007603
  simp only [CollatzResearch.WordTrace]
  refine ⟨73223296945804677140131463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48815531297203118093420975 73223296945804677140131463)
  ·
    refine ⟨109834945418707015710197195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73223296945804677140131463 109834945418707015710197195)
    ·
      refine ⟨164752418128060523565295793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109834945418707015710197195 164752418128060523565295793)
      ·
        refine ⟨123564313596045392673971845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164752418128060523565295793 123564313596045392673971845)
        ·
          refine ⟨23168308799258511126369721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123564313596045392673971845 23168308799258511126369721)
          ·
            refine ⟨17376231599443883344777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23168308799258511126369721 17376231599443883344777291)
            ·
              refine ⟨26064347399165825017165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17376231599443883344777291 26064347399165825017165937)
              ·
                refine ⟨19548260549374368762874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26064347399165825017165937 19548260549374368762874453)
                ·
                  refine ⟨229081178312980883939935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19548260549374368762874453 229081178312980883939935)
                  ·
                    rfl

theorem cell22_2007603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_2007603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007603 prefixEnd_2007603 := by exact prefixLift 2007603
  have htrace : WordTrace (prefixWord ++ tailWord_2007603) baseStart_2007603 baseEnd_2007603 := by
    simpa [prefixWord, tailWord_2007603, baseEnd_2007603] using wordTrace_append hprefix tailTrace_2007603
  have hstable : (prefixWord ++ tailWord_2007603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007603).length < 2 ^ (prefixWord ++ tailWord_2007603).sum := by decide
  have hdescent : baseEnd_2007603 < baseStart_2007603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007727 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 5]
def baseStart_2007727 : Nat := 118140960795 + 2007727 * 2 ^ 59
def prefixEnd_2007727 : Nat := 4983230072969 + 3 ^ 40 * 2007727 * 2
def baseEnd_2007727 : Nat := 229095327557682553906475

theorem tailTrace_2007727 : CollatzResearch.WordTrace tailWord_2007727 prefixEnd_2007727 229095327557682553906475 := by
  unfold tailWord_2007727
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227819597355446317645435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48818546398236964211763623 73227819597355446317645435)
  ·
    refine ⟨109841729396033169476468153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73227819597355446317645435 109841729396033169476468153)
    ·
      refine ⟨82381297047024877107351115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109841729396033169476468153 82381297047024877107351115)
      ·
        refine ⟨123571945570537315661026673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82381297047024877107351115 123571945570537315661026673)
        ·
          refine ⟨92678959177902986745770005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123571945570537315661026673 92678959177902986745770005)
          ·
            refine ⟨4344326211464202503707969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92678959177902986745770005 4344326211464202503707969)
            ·
              refine ⟨3258244658598151877780977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344326211464202503707969 3258244658598151877780977)
              ·
                refine ⟨2443683493948613908335733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258244658598151877780977 2443683493948613908335733)
                ·
                  refine ⟨229095327557682553906475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443683493948613908335733 229095327557682553906475)
                  ·
                    rfl

theorem cell22_2007727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].length) (baseStart_2007727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007727 prefixEnd_2007727 := by exact prefixLift 2007727
  have htrace : WordTrace (prefixWord ++ tailWord_2007727) baseStart_2007727 baseEnd_2007727 := by
    simpa [prefixWord, tailWord_2007727, baseEnd_2007727] using wordTrace_append hprefix tailTrace_2007727
  have hstable : (prefixWord ++ tailWord_2007727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007727).length < 2 ^ (prefixWord ++ tailWord_2007727).sum := by decide
  have hdescent : baseEnd_2007727 < baseStart_2007727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007731 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 1, 3]
def baseStart_2007731 : Nat := 118140960795 + 2007731 * 2 ^ 59
def prefixEnd_2007731 : Nat := 4983230072969 + 3 ^ 40 * 2007731 * 2
def baseEnd_2007731 : Nat := 687287351954792984619413

theorem tailTrace_2007731 : CollatzResearch.WordTrace tailWord_2007731 prefixEnd_2007731 687287351954792984619413 := by
  unfold tailWord_2007731
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227965489340955000791047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48818643659560636667194031 73227965489340955000791047)
  ·
    refine ⟨109841948234011432501186571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73227965489340955000791047 109841948234011432501186571)
    ·
      refine ⟨164762922351017148751779857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109841948234011432501186571 164762922351017148751779857)
      ·
        refine ⟨123572191763262861563834893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164762922351017148751779857 123572191763262861563834893)
        ·
          refine ⟨46339571911223573086438085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123572191763262861563834893 46339571911223573086438085)
          ·
            refine ⟨8688669733354419953707141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46339571911223573086438085 8688669733354419953707141)
            ·
              refine ⟨1629125575003953741320089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8688669733354419953707141 1629125575003953741320089)
              ·
                refine ⟨1221844181252965305990067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629125575003953741320089 1221844181252965305990067)
                ·
                  refine ⟨1832766271879447958985101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221844181252965305990067 1832766271879447958985101)
                  ·
                    refine ⟨687287351954792984619413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832766271879447958985101 687287351954792984619413)
                    ·
                      rfl

theorem cell22_2007731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 3].length) (baseStart_2007731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007731 prefixEnd_2007731 := by exact prefixLift 2007731
  have htrace : WordTrace (prefixWord ++ tailWord_2007731) baseStart_2007731 baseEnd_2007731 := by
    simpa [prefixWord, tailWord_2007731, baseEnd_2007731] using wordTrace_append hprefix tailTrace_2007731
  have hstable : (prefixWord ++ tailWord_2007731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007731).length < 2 ^ (prefixWord ++ tailWord_2007731).sum := by decide
  have hdescent : baseEnd_2007731 < baseStart_2007731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007742 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2007742 : Nat := 118140960795 + 2007742 * 2 ^ 59
def prefixEnd_2007742 : Nat := 4983230072969 + 3 ^ 40 * 2007742 * 2
def baseEnd_2007742 : Nat := 687291117479592622594379

theorem tailTrace_2007742 : CollatzResearch.WordTrace tailWord_2007742 prefixEnd_2007742 687291117479592622594379 := by
  unfold tailWord_2007742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153545836537637984930185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48818911128200735919627653 9153545836537637984930185)
  ·
    refine ⟨6865159377403228488697639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9153545836537637984930185 6865159377403228488697639)
    ·
      refine ⟨10297739066104842733046459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865159377403228488697639 10297739066104842733046459)
      ·
        refine ⟨15446608599157264099569689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10297739066104842733046459 15446608599157264099569689)
        ·
          refine ⟨11584956449367948074677267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15446608599157264099569689 11584956449367948074677267)
          ·
            refine ⟨17377434674051922112015901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584956449367948074677267 17377434674051922112015901)
            ·
              refine ⟨6516538002769470792005963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17377434674051922112015901 6516538002769470792005963)
              ·
                refine ⟨9774807004154206188008945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516538002769470792005963 9774807004154206188008945)
                ·
                  refine ⟨7331105253115654641006709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9774807004154206188008945 7331105253115654641006709)
                  ·
                    refine ⟨687291117479592622594379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331105253115654641006709 687291117479592622594379)
                    ·
                      rfl

theorem cell22_2007742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2007742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007742 prefixEnd_2007742 := by exact prefixLift 2007742
  have htrace : WordTrace (prefixWord ++ tailWord_2007742) baseStart_2007742 baseEnd_2007742 := by
    simpa [prefixWord, tailWord_2007742, baseEnd_2007742] using wordTrace_append hprefix tailTrace_2007742
  have hstable : (prefixWord ++ tailWord_2007742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007742).length < 2 ^ (prefixWord ++ tailWord_2007742).sum := by decide
  have hdescent : baseEnd_2007742 < baseStart_2007742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007789 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2007789 : Nat := 118140960795 + 2007789 * 2 ^ 59
def prefixEnd_2007789 : Nat := 4983230072969 + 3 ^ 40 * 2007789 * 2
def baseEnd_2007789 : Nat := 229102402180033388889745

theorem tailTrace_2007789 : CollatzResearch.WordTrace tailWord_2007789 prefixEnd_2007789 229102402180033388889745 := by
  unfold tailWord_2007789
  simp only [CollatzResearch.WordTrace]
  refine ⟨73230080923130830906402421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48820053948753887270934947 73230080923130830906402421)
  ·
    refine ⟨6865320086543515397475227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73230080923130830906402421 6865320086543515397475227)
    ·
      refine ⟨10297980129815273096212841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865320086543515397475227 10297980129815273096212841)
      ·
        refine ⟨7723485097361454822159631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10297980129815273096212841 7723485097361454822159631)
        ·
          refine ⟨11585227646042182233239447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723485097361454822159631 11585227646042182233239447)
          ·
            refine ⟨17377841469063273349859171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585227646042182233239447 17377841469063273349859171)
            ·
              refine ⟨26066762203594910024788757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377841469063273349859171 26066762203594910024788757)
              ·
                refine ⟨1221879478293511407411973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26066762203594910024788757 1221879478293511407411973)
                ·
                  refine ⟨229102402180033388889745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221879478293511407411973 229102402180033388889745)
                  ·
                    rfl

theorem cell22_2007789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2007789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007789 prefixEnd_2007789 := by exact prefixLift 2007789
  have htrace : WordTrace (prefixWord ++ tailWord_2007789) baseStart_2007789 baseEnd_2007789 := by
    simpa [prefixWord, tailWord_2007789, baseEnd_2007789] using wordTrace_append hprefix tailTrace_2007789
  have hstable : (prefixWord ++ tailWord_2007789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007789).length < 2 ^ (prefixWord ++ tailWord_2007789).sum := by decide
  have hdescent : baseEnd_2007789 < baseStart_2007789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007800 : List Nat := [2, 1, 2, 1, 1, 2, 4, 9]
def baseStart_2007800 : Nat := 118140960795 + 2007800 * 2 ^ 59
def prefixEnd_2007800 : Nat := 4983230072969 + 3 ^ 40 * 2007800 * 2
def baseEnd_2007800 : Nat := 76367885784988867182689

theorem tailTrace_2007800 : CollatzResearch.WordTrace tailWord_2007800 prefixEnd_2007800 76367885784988867182689 := by
  unfold tailWord_2007800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615241063045489892526427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48820321417393986523368569 36615241063045489892526427)
  ·
    refine ⟨54922861594568234838789641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36615241063045489892526427 54922861594568234838789641)
    ·
      refine ⟨41192146195926176129092231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54922861594568234838789641 41192146195926176129092231)
      ·
        refine ⟨61788219293889264193638347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41192146195926176129092231 61788219293889264193638347)
        ·
          refine ⟨92682328940833896290457521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61788219293889264193638347 92682328940833896290457521)
          ·
            refine ⟨69511746705625422217843141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92682328940833896290457521 69511746705625422217843141)
            ·
              refine ⟨13033452507304766665845589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69511746705625422217843141 13033452507304766665845589)
              ·
                refine ⟨76367885784988867182689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13033452507304766665845589 76367885784988867182689)
                ·
                  rfl

theorem cell22_2007800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_2007800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007800 prefixEnd_2007800 := by exact prefixLift 2007800
  have htrace : WordTrace (prefixWord ++ tailWord_2007800) baseStart_2007800 baseEnd_2007800 := by
    simpa [prefixWord, tailWord_2007800, baseEnd_2007800] using wordTrace_append hprefix tailTrace_2007800
  have hstable : (prefixWord ++ tailWord_2007800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007800).length < 2 ^ (prefixWord ++ tailWord_2007800).sum := by decide
  have hdescent : baseEnd_2007800 < baseStart_2007800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007804 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2007804 : Nat := 118140960795 + 2007804 * 2 ^ 59
def prefixEnd_2007804 : Nat := 4983230072969 + 3 ^ 40 * 2007804 * 2
def baseEnd_2007804 : Nat := 687312341346645127544189

theorem tailTrace_2007804 : CollatzResearch.WordTrace tailWord_2007804 prefixEnd_2007804 687312341346645127544189 := by
  unfold tailWord_2007804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615314009038244234099233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48820418678717658978798977 36615314009038244234099233)
  ·
    refine ⟨27461485506778683175574425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36615314009038244234099233 27461485506778683175574425)
    ·
      refine ⟨20596114130084012381680819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27461485506778683175574425 20596114130084012381680819)
      ·
        refine ⟨30894171195126018572521229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20596114130084012381680819 30894171195126018572521229)
        ·
          refine ⟨11585314198172256964695461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30894171195126018572521229 11585314198172256964695461)
          ·
            refine ⟨2172246412157298180880399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11585314198172256964695461 2172246412157298180880399)
            ·
              refine ⟨3258369618235947271320599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172246412157298180880399 3258369618235947271320599)
              ·
                refine ⟨4887554427353920906980899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258369618235947271320599 4887554427353920906980899)
                ·
                  refine ⟨7331331641030881360471349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887554427353920906980899 7331331641030881360471349)
                  ·
                    refine ⟨687312341346645127544189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331331641030881360471349 687312341346645127544189)
                    ·
                      rfl

theorem cell22_2007804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2007804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007804 prefixEnd_2007804 := by exact prefixLift 2007804
  have htrace : WordTrace (prefixWord ++ tailWord_2007804) baseStart_2007804 baseEnd_2007804 := by
    simpa [prefixWord, tailWord_2007804, baseEnd_2007804] using wordTrace_append hprefix tailTrace_2007804
  have hstable : (prefixWord ++ tailWord_2007804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007804).length < 2 ^ (prefixWord ++ tailWord_2007804).sum := by decide
  have hdescent : baseEnd_2007804 < baseStart_2007804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007817 : List Nat := [1, 2, 1, 1, 3, 2, 6, 6]
def baseStart_2007817 : Nat := 118140960795 + 2007817 * 2 ^ 59
def prefixEnd_2007817 : Nat := 4983230072969 + 3 ^ 40 * 2007817 * 2
def baseEnd_2007817 : Nat := 76368532390257491885461

theorem tailTrace_2007817 : CollatzResearch.WordTrace tailWord_2007817 prefixEnd_2007817 76368532390257491885461 := by
  unfold tailWord_2007817
  simp only [CollatzResearch.WordTrace]
  refine ⟨73231102167029391688421705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48820734778019594458947803 73231102167029391688421705)
  ·
    refine ⟨54923326625272043766316279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73231102167029391688421705 54923326625272043766316279)
    ·
      refine ⟨82384989937908065649474419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54923326625272043766316279 82384989937908065649474419)
      ·
        refine ⟨123577484906862098474211629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82384989937908065649474419 123577484906862098474211629)
        ·
          refine ⟨46341556840073286927829361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123577484906862098474211629 46341556840073286927829361)
          ·
            refine ⟨34756167630054965195872021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46341556840073286927829361 34756167630054965195872021)
            ·
              refine ⟨1629195357658826493556501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34756167630054965195872021 1629195357658826493556501)
              ·
                refine ⟨76368532390257491885461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1629195357658826493556501 76368532390257491885461)
                ·
                  rfl

theorem cell22_2007817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 6].length) (baseStart_2007817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007817 prefixEnd_2007817 := by exact prefixLift 2007817
  have htrace : WordTrace (prefixWord ++ tailWord_2007817) baseStart_2007817 baseEnd_2007817 := by
    simpa [prefixWord, tailWord_2007817, baseEnd_2007817] using wordTrace_append hprefix tailTrace_2007817
  have hstable : (prefixWord ++ tailWord_2007817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007817).length < 2 ^ (prefixWord ++ tailWord_2007817).sum := by decide
  have hdescent : baseEnd_2007817 < baseStart_2007817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007900 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2007900 : Nat := 118140960795 + 2007900 * 2 ^ 59
def prefixEnd_2007900 : Nat := 4983230072969 + 3 ^ 40 * 2007900 * 2
def baseEnd_2007900 : Nat := 687345204108532877143895

theorem tailTrace_2007900 : CollatzResearch.WordTrace tailWord_2007900 prefixEnd_2007900 687345204108532877143895 := by
  unfold tailWord_2007900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36617064712864348431846577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48822752950485797909128769 36617064712864348431846577)
  ·
    refine ⟨27462798534648261323884933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36617064712864348431846577 27462798534648261323884933)
    ·
      refine ⟨5149274725246548998228425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27462798534648261323884933 5149274725246548998228425)
      ·
        refine ⟨3861956043934911748671319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5149274725246548998228425 3861956043934911748671319)
        ·
          refine ⟨5792934065902367623006979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861956043934911748671319 5792934065902367623006979)
          ·
            refine ⟨8689401098853551434510469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792934065902367623006979 8689401098853551434510469)
            ·
              refine ⟨1629262706035040893970713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8689401098853551434510469 1629262706035040893970713)
              ·
                refine ⟨1221947029526280670478035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629262706035040893970713 1221947029526280670478035)
                ·
                  refine ⟨1832920544289421005717053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221947029526280670478035 1832920544289421005717053)
                  ·
                    refine ⟨687345204108532877143895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832920544289421005717053 687345204108532877143895)
                    ·
                      rfl

theorem cell22_2007900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2007900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007900 prefixEnd_2007900 := by exact prefixLift 2007900
  have htrace : WordTrace (prefixWord ++ tailWord_2007900) baseStart_2007900 baseEnd_2007900 := by
    simpa [prefixWord, tailWord_2007900, baseEnd_2007900] using wordTrace_append hprefix tailTrace_2007900
  have hstable : (prefixWord ++ tailWord_2007900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007900).length < 2 ^ (prefixWord ++ tailWord_2007900).sum := by decide
  have hdescent : baseEnd_2007900 < baseStart_2007900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007926 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2007926 : Nat := 118140960795 + 2007926 * 2 ^ 59
def prefixEnd_2007926 : Nat := 4983230072969 + 3 ^ 40 * 2007926 * 2
def baseEnd_2007926 : Nat := 687354104439877475993815

theorem tailTrace_2007926 : CollatzResearch.WordTrace tailWord_2007926 prefixEnd_2007926 687354104439877475993815 := by
  unfold tailWord_2007926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577192357727156456508727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48823385149089668869426421 4577192357727156456508727)
  ·
    refine ⟨6865788536590734684763091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577192357727156456508727 6865788536590734684763091)
    ·
      refine ⟨10298682804886102027144637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865788536590734684763091 10298682804886102027144637)
      ·
        refine ⟨3862006051832288260179239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10298682804886102027144637 3862006051832288260179239)
        ·
          refine ⟨5793009077748432390268859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862006051832288260179239 5793009077748432390268859)
          ·
            refine ⟨8689513616622648585403289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793009077748432390268859 8689513616622648585403289)
            ·
              refine ⟨6517135212466986439052467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689513616622648585403289 6517135212466986439052467)
              ·
                refine ⟨9775702818700479658578701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517135212466986439052467 9775702818700479658578701)
                ·
                  refine ⟨3665888557012679871967013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9775702818700479658578701 3665888557012679871967013)
                  ·
                    refine ⟨687354104439877475993815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665888557012679871967013 687354104439877475993815)
                    ·
                      rfl

theorem cell22_2007926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2007926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007926 prefixEnd_2007926 := by exact prefixLift 2007926
  have htrace : WordTrace (prefixWord ++ tailWord_2007926) baseStart_2007926 baseEnd_2007926 := by
    simpa [prefixWord, tailWord_2007926, baseEnd_2007926] using wordTrace_append hprefix tailTrace_2007926
  have hstable : (prefixWord ++ tailWord_2007926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007926).length < 2 ^ (prefixWord ++ tailWord_2007926).sum := by decide
  have hdescent : baseEnd_2007926 < baseStart_2007926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007939 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 4, 3]
def baseStart_2007939 : Nat := 118140960795 + 2007939 * 2 ^ 59
def prefixEnd_2007939 : Nat := 4983230072969 + 3 ^ 40 * 2007939 * 2
def baseEnd_2007939 : Nat := 687358554605549775418775

theorem tailTrace_2007939 : CollatzResearch.WordTrace tailWord_2007939 prefixEnd_2007939 687358554605549775418775 := by
  unfold tailWord_2007939
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235551872587406524362871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48823701248391604349575247 73235551872587406524362871)
  ·
    refine ⟨109853327808881109786544307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73235551872587406524362871 109853327808881109786544307)
    ·
      refine ⟨164779991713321664679816461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109853327808881109786544307 164779991713321664679816461)
      ·
        refine ⟨61792496892495624254931173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164779991713321664679816461 61792496892495624254931173)
        ·
          refine ⟨11586093167342929547799595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61792496892495624254931173 11586093167342929547799595)
          ·
            refine ⟨17379139751014394321699393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586093167342929547799595 17379139751014394321699393)
            ·
              refine ⟨13034354813260795741274545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17379139751014394321699393 13034354813260795741274545)
              ·
                refine ⟨9775766109945596805955909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034354813260795741274545 9775766109945596805955909)
                ·
                  refine ⟨1832956145614799401116733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9775766109945596805955909 1832956145614799401116733)
                  ·
                    refine ⟨687358554605549775418775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832956145614799401116733 687358554605549775418775)
                    ·
                      rfl

theorem cell22_2007939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].length) (baseStart_2007939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007939 prefixEnd_2007939 := by exact prefixLift 2007939
  have htrace : WordTrace (prefixWord ++ tailWord_2007939) baseStart_2007939 baseEnd_2007939 := by
    simpa [prefixWord, tailWord_2007939, baseEnd_2007939] using wordTrace_append hprefix tailTrace_2007939
  have hstable : (prefixWord ++ tailWord_2007939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007939).length < 2 ^ (prefixWord ++ tailWord_2007939).sum := by decide
  have hdescent : baseEnd_2007939 < baseStart_2007939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007941 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 4]
def baseStart_2007941 : Nat := 118140960795 + 2007941 * 2 ^ 59
def prefixEnd_2007941 : Nat := 4983230072969 + 3 ^ 40 * 2007941 * 2
def baseEnd_2007941 : Nat := 229119746415474145622923

theorem tailTrace_2007941 : CollatzResearch.WordTrace tailWord_2007941 prefixEnd_2007941 229119746415474145622923 := by
  unfold tailWord_2007941
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235624818580160865935677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48823749879053440577290451 73235624818580160865935677)
  ·
    refine ⟨27463359306967560324725879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73235624818580160865935677 27463359306967560324725879)
    ·
      refine ⟨41195038960451340487088819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27463359306967560324725879 41195038960451340487088819)
      ·
        refine ⟨61792558440677010730633229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41195038960451340487088819 61792558440677010730633229)
        ·
          refine ⟨23172209415253879023987461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61792558440677010730633229 23172209415253879023987461)
          ·
            refine ⟨4344789265360102316997649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23172209415253879023987461 4344789265360102316997649)
            ·
              refine ⟨3258591949020076737748237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344789265360102316997649 3258591949020076737748237)
              ·
                refine ⟨1221971980882528776655589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3258591949020076737748237 1221971980882528776655589)
                ·
                  refine ⟨229119746415474145622923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221971980882528776655589 229119746415474145622923)
                  ·
                    rfl

theorem cell22_2007941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_2007941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007941 prefixEnd_2007941 := by exact prefixLift 2007941
  have htrace : WordTrace (prefixWord ++ tailWord_2007941) baseStart_2007941 baseEnd_2007941 := by
    simpa [prefixWord, tailWord_2007941, baseEnd_2007941] using wordTrace_append hprefix tailTrace_2007941
  have hstable : (prefixWord ++ tailWord_2007941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007941).length < 2 ^ (prefixWord ++ tailWord_2007941).sum := by decide
  have hdescent : baseEnd_2007941 < baseStart_2007941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007943 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2007943 : Nat := 118140960795 + 2007943 * 2 ^ 59
def prefixEnd_2007943 : Nat := 4983230072969 + 3 ^ 40 * 2007943 * 2
def baseEnd_2007943 : Nat := 687359923887295098318763

theorem tailTrace_2007943 : CollatzResearch.WordTrace tailWord_2007943 prefixEnd_2007943 687359923887295098318763 := by
  unfold tailWord_2007943
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235697764572915207508483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48823798509715276805005655 73235697764572915207508483)
  ·
    refine ⟨109853546646859372811262725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73235697764572915207508483 109853546646859372811262725)
    ·
      refine ⟨20597539996286132402111761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109853546646859372811262725 20597539996286132402111761)
      ·
        refine ⟨15448154997214599301583821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20597539996286132402111761 15448154997214599301583821)
        ·
          refine ⟨5793058123955474738093933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448154997214599301583821 5793058123955474738093933)
          ·
            refine ⟨2172396796483303026785225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5793058123955474738093933 2172396796483303026785225)
            ·
              refine ⟨1629297597362477270088919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172396796483303026785225 1629297597362477270088919)
              ·
                refine ⟨2443946396043715905133379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629297597362477270088919 2443946396043715905133379)
                ·
                  refine ⟨3665919594065573857700069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443946396043715905133379 3665919594065573857700069)
                  ·
                    refine ⟨687359923887295098318763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665919594065573857700069 687359923887295098318763)
                    ·
                      rfl

theorem cell22_2007943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2007943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007943 prefixEnd_2007943 := by exact prefixLift 2007943
  have htrace : WordTrace (prefixWord ++ tailWord_2007943) baseStart_2007943 baseEnd_2007943 := by
    simpa [prefixWord, tailWord_2007943, baseEnd_2007943] using wordTrace_append hprefix tailTrace_2007943
  have hstable : (prefixWord ++ tailWord_2007943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007943).length < 2 ^ (prefixWord ++ tailWord_2007943).sum := by decide
  have hdescent : baseEnd_2007943 < baseStart_2007943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007956 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2007956 : Nat := 118140960795 + 2007956 * 2 ^ 59
def prefixEnd_2007956 : Nat := 4983230072969 + 3 ^ 40 * 2007956 * 2
def baseEnd_2007956 : Nat := 687364374052967397743723

theorem tailTrace_2007956 : CollatzResearch.WordTrace tailWord_2007956 prefixEnd_2007956 687364374052967397743723 := by
  unfold tailWord_2007956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36618085956762909213865861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48824114609017212285154481 36618085956762909213865861)
  ·
    refine ⟨6865891116893045477599849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36618085956762909213865861 6865891116893045477599849)
    ·
      refine ⟨5149418337669784108199887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6865891116893045477599849 5149418337669784108199887)
      ·
        refine ⟨7724127506504676162299831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149418337669784108199887 7724127506504676162299831)
        ·
          refine ⟨11586191259757014243449747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724127506504676162299831 11586191259757014243449747)
          ·
            refine ⟨17379286889635521365174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586191259757014243449747 17379286889635521365174621)
            ·
              refine ⟨6517232583613320511940483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17379286889635521365174621 6517232583613320511940483)
              ·
                refine ⟨9775848875419980767910725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517232583613320511940483 9775848875419980767910725)
                ·
                  refine ⟨1832971664141246393983261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9775848875419980767910725 1832971664141246393983261)
                  ·
                    refine ⟨687364374052967397743723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832971664141246393983261 687364374052967397743723)
                    ·
                      rfl

theorem cell22_2007956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2007956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007956 prefixEnd_2007956 := by exact prefixLift 2007956
  have htrace : WordTrace (prefixWord ++ tailWord_2007956) baseStart_2007956 baseEnd_2007956 := by
    simpa [prefixWord, tailWord_2007956, baseEnd_2007956] using wordTrace_append hprefix tailTrace_2007956
  have hstable : (prefixWord ++ tailWord_2007956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007956).length < 2 ^ (prefixWord ++ tailWord_2007956).sum := by decide
  have hdescent : baseEnd_2007956 < baseStart_2007956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007958 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2007958 : Nat := 118140960795 + 2007958 * 2 ^ 59
def prefixEnd_2007958 : Nat := 4983230072969 + 3 ^ 40 * 2007958 * 2
def baseEnd_2007958 : Nat := 229121686231280019731239

theorem tailTrace_2007958 : CollatzResearch.WordTrace tailWord_2007958 prefixEnd_2007958 229121686231280019731239 := by
  unfold tailWord_2007958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577265303719910798081533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48824163239679048512869685 4577265303719910798081533)
  ·
    refine ⟨1716474488894966549280575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4577265303719910798081533 1716474488894966549280575)
    ·
      refine ⟨2574711733342449823920863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716474488894966549280575 2574711733342449823920863)
      ·
        refine ⟨3862067600013674735881295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574711733342449823920863 3862067600013674735881295)
        ·
          refine ⟨5793101400020512103821943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862067600013674735881295 5793101400020512103821943)
          ·
            refine ⟨8689652100030768155732915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793101400020512103821943 8689652100030768155732915)
            ·
              refine ⟨13034478150046152233599373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689652100030768155732915 13034478150046152233599373)
              ·
                refine ⟨4887929306267307087599765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034478150046152233599373 4887929306267307087599765)
                ·
                  refine ⟨229121686231280019731239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4887929306267307087599765 229121686231280019731239)
                  ·
                    rfl

theorem cell22_2007958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2007958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2007958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2007958 prefixEnd_2007958 := by exact prefixLift 2007958
  have htrace : WordTrace (prefixWord ++ tailWord_2007958) baseStart_2007958 baseEnd_2007958 := by
    simpa [prefixWord, tailWord_2007958, baseEnd_2007958] using wordTrace_append hprefix tailTrace_2007958
  have hstable : (prefixWord ++ tailWord_2007958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007958).length < 2 ^ (prefixWord ++ tailWord_2007958).sum := by decide
  have hdescent : baseEnd_2007958 < baseStart_2007958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008014 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2008014 : Nat := 118140960795 + 2008014 * 2 ^ 59
def prefixEnd_2008014 : Nat := 4983230072969 + 3 ^ 40 * 2008014 * 2
def baseEnd_2008014 : Nat := 229128076212758193264515

theorem tailTrace_2008014 : CollatzResearch.WordTrace tailWord_2008014 prefixEnd_2008014 229128076212758193264515 := by
  unfold tailWord_2008014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154785918414461791667887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48825524898210462888895397 9154785918414461791667887)
  ·
    refine ⟨13732178877621692687501831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9154785918414461791667887 13732178877621692687501831)
    ·
      refine ⟨20598268316432539031252747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13732178877621692687501831 20598268316432539031252747)
      ·
        refine ⟨30897402474648808546879121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20598268316432539031252747 30897402474648808546879121)
        ·
          refine ⟨23173051855986606410159341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30897402474648808546879121 23173051855986606410159341)
          ·
            refine ⟨8689894445994977403809753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23173051855986606410159341 8689894445994977403809753)
            ·
              refine ⟨6517420834496233052857315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689894445994977403809753 6517420834496233052857315)
              ·
                refine ⟨9776131251744349579285973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517420834496233052857315 9776131251744349579285973)
                ·
                  refine ⟨229128076212758193264515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9776131251744349579285973 229128076212758193264515)
                  ·
                    rfl

theorem cell22_2008014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2008014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008014 prefixEnd_2008014 := by exact prefixLift 2008014
  have htrace : WordTrace (prefixWord ++ tailWord_2008014) baseStart_2008014 baseEnd_2008014 := by
    simpa [prefixWord, tailWord_2008014, baseEnd_2008014] using wordTrace_append hprefix tailTrace_2008014
  have hstable : (prefixWord ++ tailWord_2008014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008014).length < 2 ^ (prefixWord ++ tailWord_2008014).sum := by decide
  have hdescent : baseEnd_2008014 < baseStart_2008014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008018 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2008018 : Nat := 118140960795 + 2008018 * 2 ^ 59
def prefixEnd_2008018 : Nat := 4983230072969 + 3 ^ 40 * 2008018 * 2
def baseEnd_2008018 : Nat := 687385597920019902693533

theorem tailTrace_2008018 : CollatzResearch.WordTrace tailWord_2008018 prefixEnd_2008018 687385597920019902693533 := by
  unfold tailWord_2008018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309608309825300754122177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48825622159534135344325805 18309608309825300754122177)
  ·
    refine ⟨13732206232368975565591633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18309608309825300754122177 13732206232368975565591633)
    ·
      refine ⟨10299154674276731674193725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13732206232368975565591633 10299154674276731674193725)
      ·
        refine ⟨3862183002853774377822647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10299154674276731674193725 3862183002853774377822647)
        ·
          refine ⟨5793274504280661566733971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862183002853774377822647 5793274504280661566733971)
          ·
            refine ⟨8689911756420992350100957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793274504280661566733971 8689911756420992350100957)
            ·
              refine ⟨3258716908657872131287859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8689911756420992350100957 3258716908657872131287859)
              ·
                refine ⟨4888075362986808196931789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258716908657872131287859 4888075362986808196931789)
                ·
                  refine ⟨1833028261120053073849421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888075362986808196931789 1833028261120053073849421)
                  ·
                    refine ⟨687385597920019902693533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833028261120053073849421 687385597920019902693533)
                    ·
                      rfl

theorem cell22_2008018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2008018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008018 prefixEnd_2008018 := by exact prefixLift 2008018
  have htrace : WordTrace (prefixWord ++ tailWord_2008018) baseStart_2008018 baseEnd_2008018 := by
    simpa [prefixWord, tailWord_2008018, baseEnd_2008018] using wordTrace_append hprefix tailTrace_2008018
  have hstable : (prefixWord ++ tailWord_2008018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008018).length < 2 ^ (prefixWord ++ tailWord_2008018).sum := by decide
  have hdescent : baseEnd_2008018 < baseStart_2008018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008031 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 5]
def baseStart_2008031 : Nat := 118140960795 + 2008031 * 2 ^ 59
def prefixEnd_2008031 : Nat := 4983230072969 + 3 ^ 40 * 2008031 * 2
def baseEnd_2008031 : Nat := 229130016028564067372831

theorem tailTrace_2008031 : CollatzResearch.WordTrace tailWord_2008031 prefixEnd_2008031 229130016028564067372831 := by
  unfold tailWord_2008031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238907388254106236711947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48825938258836070824474631 73238907388254106236711947)
  ·
    refine ⟨109858361082381159355067921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73238907388254106236711947 109858361082381159355067921)
    ·
      refine ⟨82393770811785869516300941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109858361082381159355067921 82393770811785869516300941)
      ·
        refine ⟨30897664054419701068612853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82393770811785869516300941 30897664054419701068612853)
        ·
          refine ⟨2896656005101846975182455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30897664054419701068612853 2896656005101846975182455)
          ·
            refine ⟨4344984007652770462773683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896656005101846975182455 4344984007652770462773683)
            ·
              refine ⟨6517476011479155694160525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344984007652770462773683 6517476011479155694160525)
              ·
                refine ⟨2444053504304683385310197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6517476011479155694160525 2444053504304683385310197)
                ·
                  refine ⟨229130016028564067372831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2444053504304683385310197 229130016028564067372831)
                  ·
                    rfl

theorem cell22_2008031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 5].length) (baseStart_2008031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008031 prefixEnd_2008031 := by exact prefixLift 2008031
  have htrace : WordTrace (prefixWord ++ tailWord_2008031) baseStart_2008031 baseEnd_2008031 := by
    simpa [prefixWord, tailWord_2008031, baseEnd_2008031] using wordTrace_append hprefix tailTrace_2008031
  have hstable : (prefixWord ++ tailWord_2008031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008031).length < 2 ^ (prefixWord ++ tailWord_2008031).sum := by decide
  have hdescent : baseEnd_2008031 < baseStart_2008031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008089 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_2008089 : Nat := 118140960795 + 2008089 * 2 ^ 59
def prefixEnd_2008089 : Nat := 4983230072969 + 3 ^ 40 * 2008089 * 2
def baseEnd_2008089 : Nat := 687409902670999384168315

theorem tailTrace_2008089 : CollatzResearch.WordTrace tailWord_2008089 prefixEnd_2008089 687409902670999384168315 := by
  unfold tailWord_2008089
  simp only [CollatzResearch.WordTrace]
  refine ⟨73241022822043982142323321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48827348548029321428215547 73241022822043982142323321)
  ·
    refine ⟨54930767116532986606742491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73241022822043982142323321 54930767116532986606742491)
    ·
      refine ⟨82396150674799479910113737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54930767116532986606742491 82396150674799479910113737)
      ·
        refine ⟨61797113006099609932585303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82396150674799479910113737 61797113006099609932585303)
        ·
          refine ⟨92695669509149414898877955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61797113006099609932585303 92695669509149414898877955)
          ·
            refine ⟨139043504263724122348316933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92695669509149414898877955 139043504263724122348316933)
            ·
              refine ⟨26070657049448272940309425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139043504263724122348316933 26070657049448272940309425)
              ·
                refine ⟨19552992787086204705232069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26070657049448272940309425 19552992787086204705232069)
                ·
                  refine ⟨3666186147578663382231013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19552992787086204705232069 3666186147578663382231013)
                  ·
                    refine ⟨687409902670999384168315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666186147578663382231013 687409902670999384168315)
                    ·
                      rfl

theorem cell22_2008089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_2008089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008089 prefixEnd_2008089 := by exact prefixLift 2008089
  have htrace : WordTrace (prefixWord ++ tailWord_2008089) baseStart_2008089 baseEnd_2008089 := by
    simpa [prefixWord, tailWord_2008089, baseEnd_2008089] using wordTrace_append hprefix tailTrace_2008089
  have hstable : (prefixWord ++ tailWord_2008089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008089).length < 2 ^ (prefixWord ++ tailWord_2008089).sum := by decide
  have hdescent : baseEnd_2008089 < baseStart_2008089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008125 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_2008125 : Nat := 118140960795 + 2008125 * 2 ^ 59
def prefixEnd_2008125 : Nat := 4983230072969 + 3 ^ 40 * 2008125 * 2
def baseEnd_2008125 : Nat := 687422226206707290268205

theorem tailTrace_2008125 : CollatzResearch.WordTrace tailWord_2008125 prefixEnd_2008125 687422226206707290268205 := by
  unfold tailWord_2008125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73242335849913560290633829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48828223899942373527089219 73242335849913560290633829)
  ·
    refine ⟨13732937971858792554493843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73242335849913560290633829 13732937971858792554493843)
    ·
      refine ⟨20599406957788188831740765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13732937971858792554493843 20599406957788188831740765)
      ·
        refine ⟨7724777609170570811902787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20599406957788188831740765 7724777609170570811902787)
        ·
          refine ⟨11587166413755856217854181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724777609170570811902787 11587166413755856217854181)
          ·
            refine ⟨2172593702579223040847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11587166413755856217854181 2172593702579223040847659)
            ·
              refine ⟨3258890553868834561271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172593702579223040847659 3258890553868834561271489)
              ·
                refine ⟨2444167915401625920953617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258890553868834561271489 2444167915401625920953617)
                ·
                  refine ⟨1833125936551219440715213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444167915401625920953617 1833125936551219440715213)
                  ·
                    refine ⟨687422226206707290268205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833125936551219440715213 687422226206707290268205)
                    ·
                      rfl

theorem cell22_2008125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_2008125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008125 prefixEnd_2008125 := by exact prefixLift 2008125
  have htrace : WordTrace (prefixWord ++ tailWord_2008125) baseStart_2008125 baseEnd_2008125 := by
    simpa [prefixWord, tailWord_2008125, baseEnd_2008125] using wordTrace_append hprefix tailTrace_2008125
  have hstable : (prefixWord ++ tailWord_2008125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008125).length < 2 ^ (prefixWord ++ tailWord_2008125).sum := by decide
  have hdescent : baseEnd_2008125 < baseStart_2008125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008243 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 2, 3]
def baseStart_2008243 : Nat := 118140960795 + 2008243 * 2 ^ 59
def prefixEnd_2008243 : Nat := 4983230072969 + 3 ^ 40 * 2008243 * 2
def baseEnd_2008243 : Nat := 687462620018194315817843

theorem tailTrace_2008243 : CollatzResearch.WordTrace tailWord_2008243 prefixEnd_2008243 687462620018194315817843 := by
  unfold tailWord_2008243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73246639663486066443429383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48831093108990710962286255 73246639663486066443429383)
  ·
    refine ⟨109869959495229099665144075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73246639663486066443429383 109869959495229099665144075)
    ·
      refine ⟨164804939242843649497716113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109869959495229099665144075 164804939242843649497716113)
      ·
        refine ⟨123603704432132737123287085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164804939242843649497716113 123603704432132737123287085)
        ·
          refine ⟨46351389162049776421232657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123603704432132737123287085 46351389162049776421232657)
          ·
            refine ⟨34763541871537332315924493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46351389162049776421232657 34763541871537332315924493)
            ·
              refine ⟨13036328201826499618471685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34763541871537332315924493 13036328201826499618471685)
              ·
                refine ⟨2444311537842468678463441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13036328201826499618471685 2444311537842468678463441)
                ·
                  refine ⟨1833233653381851508847581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444311537842468678463441 1833233653381851508847581)
                  ·
                    refine ⟨687462620018194315817843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833233653381851508847581 687462620018194315817843)
                    ·
                      rfl

theorem cell22_2008243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].length) (baseStart_2008243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008243 prefixEnd_2008243 := by exact prefixLift 2008243
  have htrace : WordTrace (prefixWord ++ tailWord_2008243) baseStart_2008243 baseEnd_2008243 := by
    simpa [prefixWord, tailWord_2008243, baseEnd_2008243] using wordTrace_append hprefix tailTrace_2008243
  have hstable : (prefixWord ++ tailWord_2008243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008243).length < 2 ^ (prefixWord ++ tailWord_2008243).sum := by decide
  have hdescent : baseEnd_2008243 < baseStart_2008243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008260 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2008260 : Nat := 118140960795 + 2008260 * 2 ^ 59
def prefixEnd_2008260 : Nat := 4983230072969 + 3 ^ 40 * 2008260 * 2
def baseEnd_2008260 : Nat := 687468439465611938142791

theorem tailTrace_2008260 : CollatzResearch.WordTrace tailWord_2008260 prefixEnd_2008260 687468439465611938142791 := by
  unfold tailWord_2008260
  simp only [CollatzResearch.WordTrace]
  refine ⟨36623629852212239173399117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48831506469616318897865489 36623629852212239173399117)
  ·
    refine ⟨13733861194579589690024669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36623629852212239173399117 13733861194579589690024669)
    ·
      refine ⟨5150197947967346133759251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13733861194579589690024669 5150197947967346133759251)
      ·
        refine ⟨7725296921951019200638877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150197947967346133759251 7725296921951019200638877)
        ·
          refine ⟨2896986345731632200239579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7725296921951019200638877 2896986345731632200239579)
          ·
            refine ⟨4345479518597448300359369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896986345731632200239579 4345479518597448300359369)
            ·
              refine ⟨3259109638948086225269527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345479518597448300359369 3259109638948086225269527)
              ·
                refine ⟨4888664458422129337904291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259109638948086225269527 4888664458422129337904291)
                ·
                  refine ⟨7332996687633194006856437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888664458422129337904291 7332996687633194006856437)
                  ·
                    refine ⟨687468439465611938142791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7332996687633194006856437 687468439465611938142791)
                    ·
                      rfl

theorem cell22_2008260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2008260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008260 prefixEnd_2008260 := by exact prefixLift 2008260
  have htrace : WordTrace (prefixWord ++ tailWord_2008260) baseStart_2008260 baseEnd_2008260 := by
    simpa [prefixWord, tailWord_2008260, baseEnd_2008260] using wordTrace_append hprefix tailTrace_2008260
  have hstable : (prefixWord ++ tailWord_2008260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008260).length < 2 ^ (prefixWord ++ tailWord_2008260).sum := by decide
  have hdescent : baseEnd_2008260 < baseStart_2008260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008378 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2008378 : Nat := 118140960795 + 2008378 * 2 ^ 59
def prefixEnd_2008378 : Nat := 4983230072969 + 3 ^ 40 * 2008378 * 2
def baseEnd_2008378 : Nat := 687508833277098963692429

theorem tailTrace_2008378 : CollatzResearch.WordTrace tailWord_2008378 prefixEnd_2008378 687508833277098963692429 := by
  unfold tailWord_2008378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312890879499246124898447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48834375678664656333062525 18312890879499246124898447)
  ·
    refine ⟨27469336319248869187347671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18312890879499246124898447 27469336319248869187347671)
    ·
      refine ⟨41204004478873303781021507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27469336319248869187347671 41204004478873303781021507)
      ·
        refine ⟨61806006718309955671532261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41204004478873303781021507 61806006718309955671532261)
        ·
          refine ⟨11588626259683116688412299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61806006718309955671532261 11588626259683116688412299)
          ·
            refine ⟨17382939389524675032618449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11588626259683116688412299 17382939389524675032618449)
            ·
              refine ⟨13037204542143506274463837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17382939389524675032618449 13037204542143506274463837)
              ·
                refine ⟨4888951703303814852923939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13037204542143506274463837 4888951703303814852923939)
                ·
                  refine ⟨7333427554955722279385909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888951703303814852923939 7333427554955722279385909)
                  ·
                    refine ⟨687508833277098963692429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7333427554955722279385909 687508833277098963692429)
                    ·
                      rfl

theorem cell22_2008378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2008378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008378 prefixEnd_2008378 := by exact prefixLift 2008378
  have htrace : WordTrace (prefixWord ++ tailWord_2008378) baseStart_2008378 baseEnd_2008378 := by
    simpa [prefixWord, tailWord_2008378, baseEnd_2008378] using wordTrace_append hprefix tailTrace_2008378
  have hstable : (prefixWord ++ tailWord_2008378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008378).length < 2 ^ (prefixWord ++ tailWord_2008378).sum := by decide
  have hdescent : baseEnd_2008378 < baseStart_2008378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008393 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_2008393 : Nat := 118140960795 + 2008393 * 2 ^ 59
def prefixEnd_2008393 : Nat := 4983230072969 + 3 ^ 40 * 2008393 * 2
def baseEnd_2008393 : Nat := 687513968083643924567383

theorem tailTrace_2008393 : CollatzResearch.WordTrace tailWord_2008393 prefixEnd_2008393 687513968083643924567383 := by
  unfold tailWord_2008393
  simp only [CollatzResearch.WordTrace]
  refine ⟨73252110612942642061389833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48834740408628428040926555 73252110612942642061389833)
  ·
    refine ⟨54939082959706981546042375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73252110612942642061389833 54939082959706981546042375)
    ·
      refine ⟨82408624439560472319063563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54939082959706981546042375 82408624439560472319063563)
      ·
        refine ⟨123612936659340708478595345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82408624439560472319063563 123612936659340708478595345)
        ·
          refine ⟨92709702494505531358946509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123612936659340708478595345 92709702494505531358946509)
          ·
            refine ⟨34766138435439574259604941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92709702494505531358946509 34766138435439574259604941)
            ·
              refine ⟨13037301913289840347351853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34766138435439574259604941 13037301913289840347351853)
              ·
                refine ⟨4888988217483690130256945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13037301913289840347351853 4888988217483690130256945)
                ·
                  refine ⟨3666741163112767597692709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888988217483690130256945 3666741163112767597692709)
                  ·
                    refine ⟨687513968083643924567383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666741163112767597692709 687513968083643924567383)
                    ·
                      rfl

theorem cell22_2008393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_2008393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008393 prefixEnd_2008393 := by exact prefixLift 2008393
  have htrace : WordTrace (prefixWord ++ tailWord_2008393) baseStart_2008393 baseEnd_2008393 := by
    simpa [prefixWord, tailWord_2008393, baseEnd_2008393] using wordTrace_append hprefix tailTrace_2008393
  have hstable : (prefixWord ++ tailWord_2008393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008393).length < 2 ^ (prefixWord ++ tailWord_2008393).sum := by decide
  have hdescent : baseEnd_2008393 < baseStart_2008393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008487 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 5]
def baseStart_2008487 : Nat := 118140960795 + 2008487 * 2 ^ 59
def prefixEnd_2008487 : Nat := 4983230072969 + 3 ^ 40 * 2008487 * 2
def baseEnd_2008487 : Nat := 229182048734886337572365

theorem tailTrace_2008487 : CollatzResearch.WordTrace tailWord_2008487 prefixEnd_2008487 229182048734886337572365 := by
  unfold tailWord_2008487
  simp only [CollatzResearch.WordTrace]
  refine ⟨73255539074602096115311715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48837026049734730743541143 73255539074602096115311715)
  ·
    refine ⟨109883308611903144172967573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73255539074602096115311715 109883308611903144172967573)
    ·
      refine ⟨5150780091182959883107855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109883308611903144172967573 5150780091182959883107855)
      ·
        refine ⟨7726170136774439824661783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150780091182959883107855 7726170136774439824661783)
        ·
          refine ⟨11589255205161659736992675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726170136774439824661783 11589255205161659736992675)
          ·
            refine ⟨17383882807742489605489013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589255205161659736992675 17383882807742489605489013)
            ·
              refine ⟨1629739013225858400514595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17383882807742489605489013 1629739013225858400514595)
              ·
                refine ⟨2444608519838787600771893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629739013225858400514595 2444608519838787600771893)
                ·
                  refine ⟨229182048734886337572365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2444608519838787600771893 229182048734886337572365)
                  ·
                    rfl

theorem cell22_2008487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 5].length) (baseStart_2008487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008487 prefixEnd_2008487 := by exact prefixLift 2008487
  have htrace : WordTrace (prefixWord ++ tailWord_2008487) baseStart_2008487 baseEnd_2008487 := by
    simpa [prefixWord, tailWord_2008487, baseEnd_2008487] using wordTrace_append hprefix tailTrace_2008487
  have hstable : (prefixWord ++ tailWord_2008487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008487).length < 2 ^ (prefixWord ++ tailWord_2008487).sum := by decide
  have hdescent : baseEnd_2008487 < baseStart_2008487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008498 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2008498 : Nat := 118140960795 + 2008498 * 2 ^ 59
def prefixEnd_2008498 : Nat := 4983230072969 + 3 ^ 40 * 2008498 * 2
def baseEnd_2008498 : Nat := 229183303909819550230687

theorem tailTrace_2008498 : CollatzResearch.WordTrace tailWord_2008498 prefixEnd_2008498 229183303909819550230687 := by
  unfold tailWord_2008498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313985069390561248490537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48837293518374829995974765 18313985069390561248490537)
  ·
    refine ⟨13735488802042920936367903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18313985069390561248490537 13735488802042920936367903)
    ·
      refine ⟨20603233203064381404551855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735488802042920936367903 20603233203064381404551855)
      ·
        refine ⟨30904849804596572106827783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603233203064381404551855 30904849804596572106827783)
        ·
          refine ⟨46357274706894858160241675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30904849804596572106827783 46357274706894858160241675)
          ·
            refine ⟨69535912060342287240362513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46357274706894858160241675 69535912060342287240362513)
            ·
              refine ⟨52151934045256715430271885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69535912060342287240362513 52151934045256715430271885)
              ·
                refine ⟨19556975266971268286351957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52151934045256715430271885 19556975266971268286351957)
                ·
                  refine ⟨229183303909819550230687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19556975266971268286351957 229183303909819550230687)
                  ·
                    rfl

theorem cell22_2008498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2008498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008498 prefixEnd_2008498 := by exact prefixLift 2008498
  have htrace : WordTrace (prefixWord ++ tailWord_2008498) baseStart_2008498 baseEnd_2008498 := by
    simpa [prefixWord, tailWord_2008498, baseEnd_2008498] using wordTrace_append hprefix tailTrace_2008498
  have hstable : (prefixWord ++ tailWord_2008498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008498).length < 2 ^ (prefixWord ++ tailWord_2008498).sum := by decide
  have hdescent : baseEnd_2008498 < baseStart_2008498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008508 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_2008508 : Nat := 118140960795 + 2008508 * 2 ^ 59
def prefixEnd_2008508 : Nat := 4983230072969 + 3 ^ 40 * 2008508 * 2
def baseEnd_2008508 : Nat := 687553334933821957942031

theorem tailTrace_2008508 : CollatzResearch.WordTrace tailWord_2008508 prefixEnd_2008508 687553334933821957942031 := by
  unfold tailWord_2008508
  simp only [CollatzResearch.WordTrace]
  refine ⟨36628152503763008350913089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48837536671684011134550785 36628152503763008350913089)
  ·
    refine ⟨27471114377822256263184817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36628152503763008350913089 27471114377822256263184817)
    ·
      refine ⟨20603335783366692197388613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27471114377822256263184817 20603335783366692197388613)
      ·
        refine ⟨3863125459381254787010365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20603335783366692197388613 3863125459381254787010365)
        ·
          refine ⟨1448672047267970545128887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3863125459381254787010365 1448672047267970545128887)
          ·
            refine ⟨2173008070901955817693331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448672047267970545128887 2173008070901955817693331)
            ·
              refine ⟨3259512106352933726539997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173008070901955817693331 3259512106352933726539997)
              ·
                refine ⟨1222317039882350147452499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3259512106352933726539997 1222317039882350147452499)
                ·
                  refine ⟨1833475559823525221178749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222317039882350147452499 1833475559823525221178749)
                  ·
                    refine ⟨687553334933821957942031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833475559823525221178749 687553334933821957942031)
                    ·
                      rfl

theorem cell22_2008508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_2008508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008508 prefixEnd_2008508 := by exact prefixLift 2008508
  have htrace : WordTrace (prefixWord ++ tailWord_2008508) baseStart_2008508 baseEnd_2008508 := by
    simpa [prefixWord, tailWord_2008508, baseEnd_2008508] using wordTrace_append hprefix tailTrace_2008508
  have hstable : (prefixWord ++ tailWord_2008508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008508).length < 2 ^ (prefixWord ++ tailWord_2008508).sum := by decide
  have hdescent : baseEnd_2008508 < baseStart_2008508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008562 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2008562 : Nat := 118140960795 + 2008562 * 2 ^ 59
def prefixEnd_2008562 : Nat := 4983230072969 + 3 ^ 40 * 2008562 * 2
def baseEnd_2008562 : Nat := 687571820237383817091865

theorem tailTrace_2008562 : CollatzResearch.WordTrace tailWord_2008562 prefixEnd_2008562 687571820237383817091865 := by
  unfold tailWord_2008562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314568637332595981072985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48838849699553589282861293 18314568637332595981072985)
  ·
    refine ⟨13735926477999446985804739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18314568637332595981072985 13735926477999446985804739)
    ·
      refine ⟨20603889716999170478707109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735926477999446985804739 20603889716999170478707109)
      ·
        refine ⟨3863229321937344464757583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20603889716999170478707109 3863229321937344464757583)
        ·
          refine ⟨5794843982906016697136375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863229321937344464757583 5794843982906016697136375)
          ·
            refine ⟨8692265974359025045704563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794843982906016697136375 8692265974359025045704563)
            ·
              refine ⟨13038398961538537568556845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692265974359025045704563 13038398961538537568556845)
              ·
                refine ⟨4889399610576951588208817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13038398961538537568556845 4889399610576951588208817)
                ·
                  refine ⟨3667049707932713691156613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889399610576951588208817 3667049707932713691156613)
                  ·
                    refine ⟨687571820237383817091865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667049707932713691156613 687571820237383817091865)
                    ·
                      rfl

theorem cell22_2008562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2008562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008562 prefixEnd_2008562 := by exact prefixLift 2008562
  have htrace : WordTrace (prefixWord ++ tailWord_2008562) baseStart_2008562 baseEnd_2008562 := by
    simpa [prefixWord, tailWord_2008562, baseEnd_2008562] using wordTrace_append hprefix tailTrace_2008562
  have hstable : (prefixWord ++ tailWord_2008562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008562).length < 2 ^ (prefixWord ++ tailWord_2008562).sum := by decide
  have hdescent : baseEnd_2008562 < baseStart_2008562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008575 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 7, 3]
def baseStart_2008575 : Nat := 118140960795 + 2008575 * 2 ^ 59
def prefixEnd_2008575 : Nat := 4983230072969 + 3 ^ 40 * 2008575 * 2
def baseEnd_2008575 : Nat := 687576270403056116516825

theorem tailTrace_2008575 : CollatzResearch.WordTrace tailWord_2008575 prefixEnd_2008575 687576270403056116516825 := by
  unfold tailWord_2008575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73258748698283287144515179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48839165798855524763010119 73258748698283287144515179)
  ·
    refine ⟨109888123047424930716772769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73258748698283287144515179 109888123047424930716772769)
    ·
      refine ⟨82416092285568698037579577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109888123047424930716772769 82416092285568698037579577)
      ·
        refine ⟨61812069214176523528184683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82416092285568698037579577 61812069214176523528184683)
        ·
          refine ⟨92718103821264785292277025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61812069214176523528184683 92718103821264785292277025)
          ·
            refine ⟨69538577865948588969207769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92718103821264785292277025 69538577865948588969207769)
            ·
              refine ⟨52153933399461441726905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69538577865948588969207769 52153933399461441726905827)
              ·
                refine ⟨78230900099192162590358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52153933399461441726905827 78230900099192162590358741)
                ·
                  refine ⟨1833536721074816310711533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78230900099192162590358741 1833536721074816310711533)
                  ·
                    refine ⟨687576270403056116516825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833536721074816310711533 687576270403056116516825)
                    ·
                      rfl

theorem cell22_2008575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_2008575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008575 prefixEnd_2008575 := by exact prefixLift 2008575
  have htrace : WordTrace (prefixWord ++ tailWord_2008575) baseStart_2008575 baseEnd_2008575 := by
    simpa [prefixWord, tailWord_2008575, baseEnd_2008575] using wordTrace_append hprefix tailTrace_2008575
  have hstable : (prefixWord ++ tailWord_2008575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008575).length < 2 ^ (prefixWord ++ tailWord_2008575).sum := by decide
  have hdescent : baseEnd_2008575 < baseStart_2008575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008697 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_2008697 : Nat := 118140960795 + 2008697 * 2 ^ 59
def prefixEnd_2008697 : Nat := 4983230072969 + 3 ^ 40 * 2008697 * 2
def baseEnd_2008697 : Nat := 687618033496288464966451

theorem tailTrace_2008697 : CollatzResearch.WordTrace tailWord_2008697 prefixEnd_2008697 687618033496288464966451 := by
  unfold tailWord_2008697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73263198403841301980456345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48842132269227534653637563 73263198403841301980456345)
  ·
    refine ⟨54947398802880976485342259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73263198403841301980456345 54947398802880976485342259)
    ·
      refine ⟨82421098204321464728013389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54947398802880976485342259 82421098204321464728013389)
      ·
        refine ⟨30907911826620549273005021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82421098204321464728013389 30907911826620549273005021)
        ·
          refine ⟨11590466934982705977376883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30907911826620549273005021 11590466934982705977376883)
          ·
            refine ⟨17385700402474058966065325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11590466934982705977376883 17385700402474058966065325)
            ·
              refine ⟨6519637650927772112274497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17385700402474058966065325 6519637650927772112274497)
              ·
                refine ⟨4889728238195829084205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6519637650927772112274497 4889728238195829084205873)
                ·
                  refine ⟨3667296178646871813154405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889728238195829084205873 3667296178646871813154405)
                  ·
                    refine ⟨687618033496288464966451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667296178646871813154405 687618033496288464966451)
                    ·
                      rfl

theorem cell22_2008697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_2008697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008697 prefixEnd_2008697 := by exact prefixLift 2008697
  have htrace : WordTrace (prefixWord ++ tailWord_2008697) baseStart_2008697 baseEnd_2008697 := by
    simpa [prefixWord, tailWord_2008697, baseEnd_2008697] using wordTrace_append hprefix tailTrace_2008697
  have hstable : (prefixWord ++ tailWord_2008697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008697).length < 2 ^ (prefixWord ++ tailWord_2008697).sum := by decide
  have hdescent : baseEnd_2008697 < baseStart_2008697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008701 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2008701 : Nat := 118140960795 + 2008701 * 2 ^ 59
def prefixEnd_2008701 : Nat := 4983230072969 + 3 ^ 40 * 2008701 * 2
def baseEnd_2008701 : Nat := 229206467592677929288813

theorem tailTrace_2008701 : CollatzResearch.WordTrace tailWord_2008701 prefixEnd_2008701 229206467592677929288813 := by
  unfold tailWord_2008701
  simp only [CollatzResearch.WordTrace]
  refine ⟨73263344295826810663601957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48842229530551207109067971 73263344295826810663601957)
  ·
    refine ⟨13736877055467526999425367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73263344295826810663601957 13736877055467526999425367)
    ·
      refine ⟨20605315583201290499138051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13736877055467526999425367 20605315583201290499138051)
      ·
        refine ⟨30907973374801935748707077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20605315583201290499138051 30907973374801935748707077)
        ·
          refine ⟨5795245007775362952882577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30907973374801935748707077 5795245007775362952882577)
          ·
            refine ⟨4346433755831522214661933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5795245007775362952882577 4346433755831522214661933)
            ·
              refine ⟨1629912658436820830498225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4346433755831522214661933 1629912658436820830498225)
              ·
                refine ⟨1222434493827615622873669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629912658436820830498225 1222434493827615622873669)
                ·
                  refine ⟨229206467592677929288813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222434493827615622873669 229206467592677929288813)
                  ·
                    rfl

theorem cell22_2008701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2008701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008701 prefixEnd_2008701 := by exact prefixLift 2008701
  have htrace : WordTrace (prefixWord ++ tailWord_2008701) baseStart_2008701 baseEnd_2008701 := by
    simpa [prefixWord, tailWord_2008701, baseEnd_2008701] using wordTrace_append hprefix tailTrace_2008701
  have hstable : (prefixWord ++ tailWord_2008701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008701).length < 2 ^ (prefixWord ++ tailWord_2008701).sum := by decide
  have hdescent : baseEnd_2008701 < baseStart_2008701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008804 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2008804 : Nat := 118140960795 + 2008804 * 2 ^ 59
def prefixEnd_2008804 : Nat := 4983230072969 + 3 ^ 40 * 2008804 * 2
def baseEnd_2008804 : Nat := 687654661782975852541123

theorem tailTrace_2008804 : CollatzResearch.WordTrace tailWord_2008804 prefixEnd_2008804 687654661782975852541123 := by
  unfold tailWord_2008804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36633550507226829627300733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48844734009635772836400977 36633550507226829627300733)
  ·
    refine ⟨13737581440210061110237775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36633550507226829627300733 13737581440210061110237775)
    ·
      refine ⟨20606372160315091665356663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13737581440210061110237775 20606372160315091665356663)
      ·
        refine ⟨30909558240472637498034995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20606372160315091665356663 30909558240472637498034995)
        ·
          refine ⟨46364337360708956247052493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30909558240472637498034995 46364337360708956247052493)
          ·
            refine ⟨17386626510265858592644685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46364337360708956247052493 17386626510265858592644685)
            ·
              refine ⟨6519984941349696972241757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17386626510265858592644685 6519984941349696972241757)
              ·
                refine ⟨2444994353006136364590659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6519984941349696972241757 2444994353006136364590659)
                ·
                  refine ⟨3667491529509204546885989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444994353006136364590659 3667491529509204546885989)
                  ·
                    refine ⟨687654661782975852541123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667491529509204546885989 687654661782975852541123)
                    ·
                      rfl

theorem cell22_2008804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2008804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008804 prefixEnd_2008804 := by exact prefixLift 2008804
  have htrace : WordTrace (prefixWord ++ tailWord_2008804) baseStart_2008804 baseEnd_2008804 := by
    simpa [prefixWord, tailWord_2008804, baseEnd_2008804] using wordTrace_append hprefix tailTrace_2008804
  have hstable : (prefixWord ++ tailWord_2008804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008804).length < 2 ^ (prefixWord ++ tailWord_2008804).sum := by decide
  have hdescent : baseEnd_2008804 < baseStart_2008804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008819 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 4]
def baseStart_2008819 : Nat := 118140960795 + 2008819 * 2 ^ 59
def prefixEnd_2008819 : Nat := 4983230072969 + 3 ^ 40 * 2008819 * 2
def baseEnd_2008819 : Nat := 229219932196506937805359

theorem tailTrace_2008819 : CollatzResearch.WordTrace tailWord_2008819 prefixEnd_2008819 229219932196506937805359 := by
  unfold tailWord_2008819
  simp only [CollatzResearch.WordTrace]
  refine ⟨73267648109399316816397511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48845098739599544544265007 73267648109399316816397511)
  ·
    refine ⟨109901472164098975224596267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73267648109399316816397511 109901472164098975224596267)
    ·
      refine ⟨164852208246148462836894401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109901472164098975224596267 164852208246148462836894401)
      ·
        refine ⟨123639156184611347127670801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164852208246148462836894401 123639156184611347127670801)
        ·
          refine ⟨92729367138458510345753101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123639156184611347127670801 92729367138458510345753101)
          ·
            refine ⟨34773512676921941379657413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92729367138458510345753101 34773512676921941379657413)
            ·
              refine ⟨6520033626922864008685765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34773512676921941379657413 6520033626922864008685765)
              ·
                refine ⟨1222506305048037001628581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6520033626922864008685765 1222506305048037001628581)
                ·
                  refine ⟨229219932196506937805359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222506305048037001628581 229219932196506937805359)
                  ·
                    rfl

theorem cell22_2008819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 4].length) (baseStart_2008819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008819 prefixEnd_2008819 := by exact prefixLift 2008819
  have htrace : WordTrace (prefixWord ++ tailWord_2008819) baseStart_2008819 baseEnd_2008819 := by
    simpa [prefixWord, tailWord_2008819, baseEnd_2008819] using wordTrace_append hprefix tailTrace_2008819
  have hstable : (prefixWord ++ tailWord_2008819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008819).length < 2 ^ (prefixWord ++ tailWord_2008819).sum := by decide
  have hdescent : baseEnd_2008819 < baseStart_2008819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008832 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_2008832 : Nat := 118140960795 + 2008832 * 2 ^ 59
def prefixEnd_2008832 : Nat := 4983230072969 + 3 ^ 40 * 2008832 * 2
def baseEnd_2008832 : Nat := 687664246755193112841037

theorem tailTrace_2008832 : CollatzResearch.WordTrace tailWord_2008832 prefixEnd_2008832 687664246755193112841037 := by
  unfold tailWord_2008832
  simp only [CollatzResearch.WordTrace]
  refine ⟨36634061129176110018310375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48845414838901480024413833 36634061129176110018310375)
  ·
    refine ⟨54951091693764165027465563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36634061129176110018310375 54951091693764165027465563)
    ·
      refine ⟨82426637540646247541198345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54951091693764165027465563 82426637540646247541198345)
      ·
        refine ⟨61819978155484685655898759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82426637540646247541198345 61819978155484685655898759)
        ·
          refine ⟨92729967233227028483848139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61819978155484685655898759 92729967233227028483848139)
          ·
            refine ⟨139094950849840542725772209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92729967233227028483848139 139094950849840542725772209)
            ·
              refine ⟨104321213137380407044329157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139094950849840542725772209 104321213137380407044329157)
              ·
                refine ⟨19560227463258826320811717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104321213137380407044329157 19560227463258826320811717)
                ·
                  refine ⟨3667542649361029935152197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19560227463258826320811717 3667542649361029935152197)
                  ·
                    refine ⟨687664246755193112841037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3667542649361029935152197 687664246755193112841037)
                    ·
                      rfl

theorem cell22_2008832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_2008832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008832 prefixEnd_2008832 := by exact prefixLift 2008832
  have htrace : WordTrace (prefixWord ++ tailWord_2008832) baseStart_2008832 baseEnd_2008832 := by
    simpa [prefixWord, tailWord_2008832, baseEnd_2008832] using wordTrace_append hprefix tailTrace_2008832
  have hstable : (prefixWord ++ tailWord_2008832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008832).length < 2 ^ (prefixWord ++ tailWord_2008832).sum := by decide
  have hdescent : baseEnd_2008832 < baseStart_2008832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008885 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2008885 : Nat := 118140960795 + 2008885 * 2 ^ 59
def prefixEnd_2008885 : Nat := 4983230072969 + 3 ^ 40 * 2008885 * 2
def baseEnd_2008885 : Nat := 687682389738318641265875

theorem tailTrace_2008885 : CollatzResearch.WordTrace tailWord_2008885 prefixEnd_2008885 687682389738318641265875 := by
  unfold tailWord_2008885
  simp only [CollatzResearch.WordTrace]
  refine ⟨73270055327160210088300109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48846703551440140058866739 73270055327160210088300109)
  ·
    refine ⟨27476270747685078783112541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73270055327160210088300109 27476270747685078783112541)
    ·
      refine ⟨10303601530381904543667203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27476270747685078783112541 10303601530381904543667203)
      ·
        refine ⟨15455402295572856815500805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303601530381904543667203 15455402295572856815500805)
        ·
          refine ⟨2897887930419910652906401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15455402295572856815500805 2897887930419910652906401)
          ·
            refine ⟨2173415947814932989679801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897887930419910652906401 2173415947814932989679801)
            ·
              refine ⟨1630061960861199742259851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173415947814932989679801 1630061960861199742259851)
              ·
                refine ⟨2445092941291799613389777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630061960861199742259851 2445092941291799613389777)
                ·
                  refine ⟨1833819705968849710042333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445092941291799613389777 1833819705968849710042333)
                  ·
                    refine ⟨687682389738318641265875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833819705968849710042333 687682389738318641265875)
                    ·
                      rfl

theorem cell22_2008885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2008885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008885 prefixEnd_2008885 := by exact prefixLift 2008885
  have htrace : WordTrace (prefixWord ++ tailWord_2008885) baseStart_2008885 baseEnd_2008885 := by
    simpa [prefixWord, tailWord_2008885, baseEnd_2008885] using wordTrace_append hprefix tailTrace_2008885
  have hstable : (prefixWord ++ tailWord_2008885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008885).length < 2 ^ (prefixWord ++ tailWord_2008885).sum := by decide
  have hdescent : baseEnd_2008885 < baseStart_2008885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008930 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2008930 : Nat := 118140960795 + 2008930 * 2 ^ 59
def prefixEnd_2008930 : Nat := 4983230072969 + 3 ^ 40 * 2008930 * 2
def baseEnd_2008930 : Nat := 687697794157953523890737

theorem tailTrace_2008930 : CollatzResearch.WordTrace tailWord_2008930 prefixEnd_2008930 687697794157953523890737 := by
  unfold tailWord_2008930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317924152999295693422061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48847797741331455182458829 18317924152999295693422061)
  ·
    refine ⟨6869221557374735885033273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18317924152999295693422061 6869221557374735885033273)
    ·
      refine ⟨5151916168031051913774955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6869221557374735885033273 5151916168031051913774955)
      ·
        refine ⟨7727874252046577870662433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151916168031051913774955 7727874252046577870662433)
        ·
          refine ⟨5795905689034933402996825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727874252046577870662433 5795905689034933402996825)
          ·
            refine ⟨4346929266776200052247619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5795905689034933402996825 4346929266776200052247619)
            ·
              refine ⟨6520393900164300078371429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346929266776200052247619 6520393900164300078371429)
              ·
                refine ⟨1222573856280806264694643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6520393900164300078371429 1222573856280806264694643)
                ·
                  refine ⟨1833860784421209397041965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222573856280806264694643 1833860784421209397041965)
                  ·
                    refine ⟨687697794157953523890737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833860784421209397041965 687697794157953523890737)
                    ·
                      rfl

theorem cell22_2008930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2008930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008930 prefixEnd_2008930 := by exact prefixLift 2008930
  have htrace : WordTrace (prefixWord ++ tailWord_2008930) baseStart_2008930 baseEnd_2008930 := by
    simpa [prefixWord, tailWord_2008930, baseEnd_2008930] using wordTrace_append hprefix tailTrace_2008930
  have hstable : (prefixWord ++ tailWord_2008930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008930).length < 2 ^ (prefixWord ++ tailWord_2008930).sum := by decide
  have hdescent : baseEnd_2008930 < baseStart_2008930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008937 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 10]
def baseStart_2008937 : Nat := 118140960795 + 2008937 * 2 ^ 59
def prefixEnd_2008937 : Nat := 4983230072969 + 3 ^ 40 * 2008937 * 2
def baseEnd_2008937 : Nat := 229233396800335946321905

theorem tailTrace_2008937 : CollatzResearch.WordTrace tailWord_2008937 prefixEnd_2008937 229233396800335946321905 := by
  unfold tailWord_2008937
  simp only [CollatzResearch.WordTrace]
  refine ⟨73271951922971822969193065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48847967948647881979462043 73271951922971822969193065)
  ·
    refine ⟨54953963942228867226894799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73271951922971822969193065 54953963942228867226894799)
    ·
      refine ⟨82430945913343300840342199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54953963942228867226894799 82430945913343300840342199)
      ·
        refine ⟨123646418870014951260513299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82430945913343300840342199 123646418870014951260513299)
        ·
          refine ⟨185469628305022426890769949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123646418870014951260513299 185469628305022426890769949)
          ·
            refine ⟨69551110614383410084038731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185469628305022426890769949 69551110614383410084038731)
            ·
              refine ⟨104326665921575115126058097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69551110614383410084038731 104326665921575115126058097)
              ·
                refine ⟨78244999441181336344543573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104326665921575115126058097 78244999441181336344543573)
                ·
                  refine ⟨229233396800335946321905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78244999441181336344543573 229233396800335946321905)
                  ·
                    rfl

theorem cell22_2008937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_2008937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008937 prefixEnd_2008937 := by exact prefixLift 2008937
  have htrace : WordTrace (prefixWord ++ tailWord_2008937) baseStart_2008937 baseEnd_2008937 := by
    simpa [prefixWord, tailWord_2008937, baseEnd_2008937] using wordTrace_append hprefix tailTrace_2008937
  have hstable : (prefixWord ++ tailWord_2008937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008937).length < 2 ^ (prefixWord ++ tailWord_2008937).sum := by decide
  have hdescent : baseEnd_2008937 < baseStart_2008937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008969 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_2008969 : Nat := 118140960795 + 2008969 * 2 ^ 59
def prefixEnd_2008969 : Nat := 4983230072969 + 3 ^ 40 * 2008969 * 2
def baseEnd_2008969 : Nat := 687711144654970422165617

theorem tailTrace_2008969 : CollatzResearch.WordTrace tailWord_2008969 prefixEnd_2008969 687711144654970422165617 := by
  unfold tailWord_2008969
  simp only [CollatzResearch.WordTrace]
  refine ⟨73273119058855892434357961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48848746039237261622905307 73273119058855892434357961)
  ·
    refine ⟨54954839294141919325768471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73273119058855892434357961 54954839294141919325768471)
    ·
      refine ⟨82432258941212878988652707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54954839294141919325768471 82432258941212878988652707)
      ·
        refine ⟨123648388411819318482979061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82432258941212878988652707 123648388411819318482979061)
        ·
          refine ⟨11592036413608061107779287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123648388411819318482979061 11592036413608061107779287)
          ·
            refine ⟨17388054620412091661668931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592036413608061107779287 17388054620412091661668931)
            ·
              refine ⟨26082081930618137492503397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17388054620412091661668931 26082081930618137492503397)
              ·
                refine ⟨4890390361990900779844387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26082081930618137492503397 4890390361990900779844387)
                ·
                  refine ⟨7335585542986351169766581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890390361990900779844387 7335585542986351169766581)
                  ·
                    refine ⟨687711144654970422165617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7335585542986351169766581 687711144654970422165617)
                    ·
                      rfl

theorem cell22_2008969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_2008969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008969 prefixEnd_2008969 := by exact prefixLift 2008969
  have htrace : WordTrace (prefixWord ++ tailWord_2008969) baseStart_2008969 baseEnd_2008969 := by
    simpa [prefixWord, tailWord_2008969, baseEnd_2008969] using wordTrace_append hprefix tailTrace_2008969
  have hstable : (prefixWord ++ tailWord_2008969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008969).length < 2 ^ (prefixWord ++ tailWord_2008969).sum := by decide
  have hdescent : baseEnd_2008969 < baseStart_2008969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008988 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_2008988 : Nat := 118140960795 + 2008988 * 2 ^ 59
def prefixEnd_2008988 : Nat := 4983230072969 + 3 ^ 40 * 2008988 * 2
def baseEnd_2008988 : Nat := 229239216247753568646853

theorem tailTrace_2008988 : CollatzResearch.WordTrace tailWord_2008988 prefixEnd_2008988 229239216247753568646853 := by
  unfold tailWord_2008988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36636906022893529339649809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48849208030524705786199745 36636906022893529339649809)
  ·
    refine ⟨27477679517170147004737357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36636906022893529339649809 27477679517170147004737357)
    ·
      refine ⟨10304129818938805126776509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27477679517170147004737357 10304129818938805126776509)
      ·
        refine ⟨3864048682102051922541191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10304129818938805126776509 3864048682102051922541191)
        ·
          refine ⟨5796073023153077883811787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864048682102051922541191 5796073023153077883811787)
          ·
            refine ⟨8694109534729616825717681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796073023153077883811787 8694109534729616825717681)
            ·
              refine ⟨6520582151047212619288261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694109534729616825717681 6520582151047212619288261)
              ·
                refine ⟨1222609153321352366116549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6520582151047212619288261 1222609153321352366116549)
                ·
                  refine ⟨229239216247753568646853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222609153321352366116549 229239216247753568646853)
                  ·
                    rfl

theorem cell22_2008988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_2008988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2008988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2008988 prefixEnd_2008988 := by exact prefixLift 2008988
  have htrace : WordTrace (prefixWord ++ tailWord_2008988) baseStart_2008988 baseEnd_2008988 := by
    simpa [prefixWord, tailWord_2008988, baseEnd_2008988] using wordTrace_append hprefix tailTrace_2008988
  have hstable : (prefixWord ++ tailWord_2008988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008988).length < 2 ^ (prefixWord ++ tailWord_2008988).sum := by decide
  have hdescent : baseEnd_2008988 < baseStart_2008988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009091 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 1, 4]
def baseStart_2009091 : Nat := 118140960795 + 2009091 * 2 ^ 59
def prefixEnd_2009091 : Nat := 4983230072969 + 3 ^ 40 * 2009091 * 2
def baseEnd_2009091 : Nat := 687752907748202770615243

theorem tailTrace_2009091 : CollatzResearch.WordTrace tailWord_2009091 prefixEnd_2009091 687752907748202770615243 := by
  unfold tailWord_2009091
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277568764413907270299127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48851712509609271513532751 73277568764413907270299127)
  ·
    refine ⟨109916353146620860905448691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277568764413907270299127 109916353146620860905448691)
    ·
      refine ⟨164874529719931291358173037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109916353146620860905448691 164874529719931291358173037)
      ·
        refine ⟨61827948644974234259314889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164874529719931291358173037 61827948644974234259314889)
        ·
          refine ⟨46370961483730675694486167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61827948644974234259314889 46370961483730675694486167)
          ·
            refine ⟨69556442225596013541729251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46370961483730675694486167 69556442225596013541729251)
            ·
              refine ⟨104334663338394020312593877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69556442225596013541729251 104334663338394020312593877)
              ·
                refine ⟨2445343671993609851076419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104334663338394020312593877 2445343671993609851076419)
                ·
                  refine ⟨3668015507990414776614629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445343671993609851076419 3668015507990414776614629)
                  ·
                    refine ⟨687752907748202770615243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668015507990414776614629 687752907748202770615243)
                    ·
                      rfl

theorem cell22_2009091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_2009091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009091 prefixEnd_2009091 := by exact prefixLift 2009091
  have htrace : WordTrace (prefixWord ++ tailWord_2009091) baseStart_2009091 baseEnd_2009091 := by
    simpa [prefixWord, tailWord_2009091, baseEnd_2009091] using wordTrace_append hprefix tailTrace_2009091
  have hstable : (prefixWord ++ tailWord_2009091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009091).length < 2 ^ (prefixWord ++ tailWord_2009091).sum := by decide
  have hdescent : baseEnd_2009091 < baseStart_2009091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009136 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_2009136 : Nat := 118140960795 + 2009136 * 2 ^ 59
def prefixEnd_2009136 : Nat := 4983230072969 + 3 ^ 40 * 2009136 * 2
def baseEnd_2009136 : Nat := 687768312167837653240105

theorem tailTrace_2009136 : CollatzResearch.WordTrace tailWord_2009136 prefixEnd_2009136 687768312167837653240105 := by
  unfold tailWord_2009136
  simp only [CollatzResearch.WordTrace]
  refine ⟨36639605024625439977843631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48852806699500586637124841 36639605024625439977843631)
  ·
    refine ⟨54959407536938159966765447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36639605024625439977843631 54959407536938159966765447)
    ·
      refine ⟨82439111305407239950148171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54959407536938159966765447 82439111305407239950148171)
      ·
        refine ⟨123658666958110859925222257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82439111305407239950148171 123658666958110859925222257)
        ·
          refine ⟨92744000218583144943916693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123658666958110859925222257 92744000218583144943916693)
          ·
            refine ⟨4347375010246084919246095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92744000218583144943916693 4347375010246084919246095)
            ·
              refine ⟨6521062515369127378869143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347375010246084919246095 6521062515369127378869143)
              ·
                refine ⟨9781593773053691068303715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521062515369127378869143 9781593773053691068303715)
                ·
                  refine ⟨14672390659580536602455573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781593773053691068303715 14672390659580536602455573)
                  ·
                    refine ⟨687768312167837653240105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14672390659580536602455573 687768312167837653240105)
                    ·
                      rfl

theorem cell22_2009136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_2009136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009136 prefixEnd_2009136 := by exact prefixLift 2009136
  have htrace : WordTrace (prefixWord ++ tailWord_2009136) baseStart_2009136 baseEnd_2009136 := by
    simpa [prefixWord, tailWord_2009136, baseEnd_2009136] using wordTrace_append hprefix tailTrace_2009136
  have hstable : (prefixWord ++ tailWord_2009136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009136).length < 2 ^ (prefixWord ++ tailWord_2009136).sum := by decide
  have hdescent : baseEnd_2009136 < baseStart_2009136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009196 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_2009196 : Nat := 118140960795 + 2009196 * 2 ^ 59
def prefixEnd_2009196 : Nat := 4983230072969 + 3 ^ 40 * 2009196 * 2
def baseEnd_2009196 : Nat := 229262950464672498913307

theorem tailTrace_2009196 : CollatzResearch.WordTrace tailWord_2009196 prefixEnd_2009196 229262950464672498913307 := by
  unfold tailWord_2009196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640699214516755101435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48854265619355673468580961 36640699214516755101435721)
  ·
    refine ⟨27480524410887566326076791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36640699214516755101435721 27480524410887566326076791)
    ·
      refine ⟨41220786616331349489115187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27480524410887566326076791 41220786616331349489115187)
      ·
        refine ⟨61831179924497024233672781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41220786616331349489115187 61831179924497024233672781)
        ·
          refine ⟨23186692471686384087627293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61831179924497024233672781 23186692471686384087627293)
          ·
            refine ⟨8695009676882394032860235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23186692471686384087627293 8695009676882394032860235)
            ·
              refine ⟨13042514515323591049290353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695009676882394032860235 13042514515323591049290353)
              ·
                refine ⟨9781885886492693286967765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13042514515323591049290353 9781885886492693286967765)
                ·
                  refine ⟨229262950464672498913307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9781885886492693286967765 229262950464672498913307)
                  ·
                    rfl

theorem cell22_2009196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_2009196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009196 prefixEnd_2009196 := by exact prefixLift 2009196
  have htrace : WordTrace (prefixWord ++ tailWord_2009196) baseStart_2009196 baseEnd_2009196 := by
    simpa [prefixWord, tailWord_2009196, baseEnd_2009196] using wordTrace_append hprefix tailTrace_2009196
  have hstable : (prefixWord ++ tailWord_2009196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009196).length < 2 ^ (prefixWord ++ tailWord_2009196).sum := by decide
  have hdescent : baseEnd_2009196 < baseStart_2009196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009217 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2009217 : Nat := 118140960795 + 2009217 * 2 ^ 59
def prefixEnd_2009217 : Nat := 4983230072969 + 3 ^ 40 * 2009217 * 2
def baseEnd_2009217 : Nat := 687796040123180441964857

theorem tailTrace_2009217 : CollatzResearch.WordTrace tailWord_2009217 prefixEnd_2009217 687796040123180441964857 := by
  unfold tailWord_2009217
  simp only [CollatzResearch.WordTrace]
  refine ⟨73282164361957430789385905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48854776241304953859590603 73282164361957430789385905)
  ·
    refine ⟨54961623271468073092039429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73282164361957430789385905 54961623271468073092039429)
    ·
      refine ⟨10305304363400263704757393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54961623271468073092039429 10305304363400263704757393)
      ·
        refine ⟨7728978272550197778568045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10305304363400263704757393 7728978272550197778568045)
        ·
          refine ⟨2898366852206324166963017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7728978272550197778568045 2898366852206324166963017)
          ·
            refine ⟨2173775139154743125222263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898366852206324166963017 2173775139154743125222263)
            ·
              refine ⟨3260662708732114687833395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173775139154743125222263 3260662708732114687833395)
              ·
                refine ⟨4890994063098172031750093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260662708732114687833395 4890994063098172031750093)
                ·
                  refine ⟨1834122773661814511906285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4890994063098172031750093 1834122773661814511906285)
                  ·
                    refine ⟨687796040123180441964857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834122773661814511906285 687796040123180441964857)
                    ·
                      rfl

theorem cell22_2009217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2009217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009217 prefixEnd_2009217 := by exact prefixLift 2009217
  have htrace : WordTrace (prefixWord ++ tailWord_2009217) baseStart_2009217 baseEnd_2009217 := by
    simpa [prefixWord, tailWord_2009217, baseEnd_2009217] using wordTrace_append hprefix tailTrace_2009217
  have hstable : (prefixWord ++ tailWord_2009217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009217).length < 2 ^ (prefixWord ++ tailWord_2009217).sum := by decide
  have hdescent : baseEnd_2009217 < baseStart_2009217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009230 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2009230 : Nat := 118140960795 + 2009230 * 2 ^ 59
def prefixEnd_2009230 : Nat := 4983230072969 + 3 ^ 40 * 2009230 * 2
def baseEnd_2009230 : Nat := 229266830096284247129939

theorem tailTrace_2009230 : CollatzResearch.WordTrace tailWord_2009230 prefixEnd_2009230 229266830096284247129939 := by
  unfold tailWord_2009230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160329813863791751201143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48855092340606889339739429 9160329813863791751201143)
  ·
    refine ⟨13740494720795687626801715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9160329813863791751201143 13740494720795687626801715)
    ·
      refine ⟨20610742081193531440202573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13740494720795687626801715 20610742081193531440202573)
      ·
        refine ⟨7729028280447574290075965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20610742081193531440202573 7729028280447574290075965)
        ·
          refine ⟨2898385605167840358778487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7729028280447574290075965 2898385605167840358778487)
          ·
            refine ⟨4347578407751760538167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898385605167840358778487 4347578407751760538167731)
            ·
              refine ⟨6521367611627640807251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347578407751760538167731 6521367611627640807251597)
              ·
                refine ⟨2445512854360365302719349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6521367611627640807251597 2445512854360365302719349)
                ·
                  refine ⟨229266830096284247129939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2445512854360365302719349 229266830096284247129939)
                  ·
                    rfl

theorem cell22_2009230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2009230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009230 prefixEnd_2009230 := by exact prefixLift 2009230
  have htrace : WordTrace (prefixWord ++ tailWord_2009230) baseStart_2009230 baseEnd_2009230 := by
    simpa [prefixWord, tailWord_2009230, baseEnd_2009230] using wordTrace_append hprefix tailTrace_2009230
  have hstable : (prefixWord ++ tailWord_2009230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009230).length < 2 ^ (prefixWord ++ tailWord_2009230).sum := by decide
  have hdescent : baseEnd_2009230 < baseStart_2009230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009241 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 6]
def baseStart_2009241 : Nat := 118140960795 + 2009241 * 2 ^ 59
def prefixEnd_2009241 : Nat := 4983230072969 + 3 ^ 40 * 2009241 * 2
def baseEnd_2009241 : Nat := 229268085271217459788261

theorem tailTrace_2009241 : CollatzResearch.WordTrace tailWord_2009241 prefixEnd_2009241 229268085271217459788261 := by
  unfold tailWord_2009241
  simp only [CollatzResearch.WordTrace]
  refine ⟨73283039713870482888259577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48855359809246988592173051 73283039713870482888259577)
  ·
    refine ⟨54962279785402862166194683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73283039713870482888259577 54962279785402862166194683)
    ·
      refine ⟨82443419678104293249292025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962279785402862166194683 82443419678104293249292025)
      ·
        refine ⟨61832564758578219936969019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82443419678104293249292025 61832564758578219936969019)
        ·
          refine ⟨92748847137867329905453529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61832564758578219936969019 92748847137867329905453529)
          ·
            refine ⟨69561635353400497429090147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92748847137867329905453529 69561635353400497429090147)
            ·
              refine ⟨104342453030100746143635221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69561635353400497429090147 104342453030100746143635221)
              ·
                refine ⟨4891052485785972475482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104342453030100746143635221 4891052485785972475482901)
                ·
                  refine ⟨229268085271217459788261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4891052485785972475482901 229268085271217459788261)
                  ·
                    rfl

theorem cell22_2009241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_2009241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009241 prefixEnd_2009241 := by exact prefixLift 2009241
  have htrace : WordTrace (prefixWord ++ tailWord_2009241) baseStart_2009241 baseEnd_2009241 := by
    simpa [prefixWord, tailWord_2009241, baseEnd_2009241] using wordTrace_append hprefix tailTrace_2009241
  have hstable : (prefixWord ++ tailWord_2009241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009241).length < 2 ^ (prefixWord ++ tailWord_2009241).sum := by decide
  have hdescent : baseEnd_2009241 < baseStart_2009241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009268 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2009268 : Nat := 118140960795 + 2009268 * 2 ^ 59
def prefixEnd_2009268 : Nat := 4983230072969 + 3 ^ 40 * 2009268 * 2
def baseEnd_2009268 : Nat := 687813498465433308939701

theorem tailTrace_2009268 : CollatzResearch.WordTrace tailWord_2009268 prefixEnd_2009268 687813498465433308939701 := by
  unfold tailWord_2009268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642012242386333249746229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48856016323181777666328305 36642012242386333249746229)
  ·
    refine ⟨3435188647723718742163709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36642012242386333249746229 3435188647723718742163709)
    ·
      refine ⟨1288195742896394528311391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3435188647723718742163709 1288195742896394528311391)
      ·
        refine ⟨1932293614344591792467087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288195742896394528311391 1932293614344591792467087)
        ·
          refine ⟨2898440421516887688700631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932293614344591792467087 2898440421516887688700631)
          ·
            refine ⟨4347660632275331533050947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898440421516887688700631 4347660632275331533050947)
            ·
              refine ⟨6521490948412997299576421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347660632275331533050947 6521490948412997299576421)
              ·
                refine ⟨1222779552827436993670579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6521490948412997299576421 1222779552827436993670579)
                ·
                  refine ⟨1834169329241155490505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222779552827436993670579 1834169329241155490505869)
                  ·
                    refine ⟨687813498465433308939701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834169329241155490505869 687813498465433308939701)
                    ·
                      rfl

theorem cell22_2009268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2009268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009268 prefixEnd_2009268 := by exact prefixLift 2009268
  have htrace : WordTrace (prefixWord ++ tailWord_2009268) baseStart_2009268 baseEnd_2009268 := by
    simpa [prefixWord, tailWord_2009268, baseEnd_2009268] using wordTrace_append hprefix tailTrace_2009268
  have hstable : (prefixWord ++ tailWord_2009268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009268).length < 2 ^ (prefixWord ++ tailWord_2009268).sum := by decide
  have hdescent : baseEnd_2009268 < baseStart_2009268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009290 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_2009290 : Nat := 118140960795 + 2009290 * 2 ^ 59
def prefixEnd_2009290 : Nat := 4983230072969 + 3 ^ 40 * 2009290 * 2
def baseEnd_2009290 : Nat := 687821029515032584889633

theorem tailTrace_2009290 : CollatzResearch.WordTrace tailWord_2009290 prefixEnd_2009290 687821029515032584889633 := by
  unfold tailWord_2009290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321206722673241064198331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48856551260461976171195549 18321206722673241064198331)
  ·
    refine ⟨27481810084009861596297497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18321206722673241064198331 27481810084009861596297497)
    ·
      refine ⟨20611357563007396197223123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27481810084009861596297497 20611357563007396197223123)
      ·
        refine ⟨30917036344511094295834685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20611357563007396197223123 30917036344511094295834685)
        ·
          refine ⟨11593888629191660360938007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30917036344511094295834685 11593888629191660360938007)
          ·
            refine ⟨17390832943787490541407011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593888629191660360938007 17390832943787490541407011)
            ·
              refine ⟨26086249415681235812110517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390832943787490541407011 26086249415681235812110517)
              ·
                refine ⟨2445585882720115857385361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26086249415681235812110517 2445585882720115857385361)
                ·
                  refine ⟨1834189412040086893039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445585882720115857385361 1834189412040086893039021)
                  ·
                    refine ⟨687821029515032584889633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834189412040086893039021 687821029515032584889633)
                    ·
                      rfl

theorem cell22_2009290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_2009290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009290 prefixEnd_2009290 := by exact prefixLift 2009290
  have htrace : WordTrace (prefixWord ++ tailWord_2009290) baseStart_2009290 baseEnd_2009290 := by
    simpa [prefixWord, tailWord_2009290, baseEnd_2009290] using wordTrace_append hprefix tailTrace_2009290
  have hstable : (prefixWord ++ tailWord_2009290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009290).length < 2 ^ (prefixWord ++ tailWord_2009290).sum := by decide
  have hdescent : baseEnd_2009290 < baseStart_2009290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009386 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2009386 : Nat := 118140960795 + 2009386 * 2 ^ 59
def prefixEnd_2009386 : Nat := 4983230072969 + 3 ^ 40 * 2009386 * 2
def baseEnd_2009386 : Nat := 687853892276920334489339

theorem tailTrace_2009386 : CollatzResearch.WordTrace tailWord_2009386 prefixEnd_2009386 687853892276920334489339 := by
  unfold tailWord_2009386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322082074586293163072003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48858885532230115101525341 18322082074586293163072003)
  ·
    refine ⟨27483123111879439744608005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18322082074586293163072003 27483123111879439744608005)
    ·
      refine ⟨5153085583477394952114001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27483123111879439744608005 5153085583477394952114001)
      ·
        refine ⟨3864814187608046214085501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5153085583477394952114001 3864814187608046214085501)
        ·
          refine ⟨1449305320353017330282063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3864814187608046214085501 1449305320353017330282063)
          ·
            refine ⟨2173957980529525995423095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449305320353017330282063 2173957980529525995423095)
            ·
              refine ⟨3260936970794288993134643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173957980529525995423095 3260936970794288993134643)
              ·
                refine ⟨4891405456191433489701965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260936970794288993134643 4891405456191433489701965)
                ·
                  refine ⟨1834277046071787558638237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4891405456191433489701965 1834277046071787558638237)
                  ·
                    refine ⟨687853892276920334489339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834277046071787558638237 687853892276920334489339)
                    ·
                      rfl

theorem cell22_2009386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2009386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009386 prefixEnd_2009386 := by exact prefixLift 2009386
  have htrace : WordTrace (prefixWord ++ tailWord_2009386) baseStart_2009386 baseEnd_2009386 := by
    simpa [prefixWord, tailWord_2009386, baseEnd_2009386] using wordTrace_append hprefix tailTrace_2009386
  have hstable : (prefixWord ++ tailWord_2009386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009386).length < 2 ^ (prefixWord ++ tailWord_2009386).sum := by decide
  have hdescent : baseEnd_2009386 < baseStart_2009386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009425 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_2009425 : Nat := 118140960795 + 2009425 * 2 ^ 59
def prefixEnd_2009425 : Nat := 4983230072969 + 3 ^ 40 * 2009425 * 2
def baseEnd_2009425 : Nat := 687867242773937232764219

theorem tailTrace_2009425 : CollatzResearch.WordTrace tailWord_2009425 prefixEnd_2009425 687867242773937232764219 := by
  unfold tailWord_2009425
  simp only [CollatzResearch.WordTrace]
  refine ⟨73289750745203882312957729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48859833830135921541971819 73289750745203882312957729)
  ·
    refine ⟨54967313058902911734718297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73289750745203882312957729 54967313058902911734718297)
    ·
      refine ⟨41225484794177183801038723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54967313058902911734718297 41225484794177183801038723)
      ·
        refine ⟨61838227191265775701558085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41225484794177183801038723 61838227191265775701558085)
        ·
          refine ⟨11594667598362332944042141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61838227191265775701558085 11594667598362332944042141)
          ·
            refine ⟨4348000349385874854015803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11594667598362332944042141 4348000349385874854015803)
            ·
              refine ⟨6522000524078812281023705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348000349385874854015803 6522000524078812281023705)
              ·
                refine ⟨4891500393059109210767779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6522000524078812281023705 4891500393059109210767779)
                ·
                  refine ⟨7337250589588663816151669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891500393059109210767779 7337250589588663816151669)
                  ·
                    refine ⟨687867242773937232764219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7337250589588663816151669 687867242773937232764219)
                    ·
                      rfl

theorem cell22_2009425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_2009425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009425 prefixEnd_2009425 := by exact prefixLift 2009425
  have htrace : WordTrace (prefixWord ++ tailWord_2009425) baseStart_2009425 baseEnd_2009425 := by
    simpa [prefixWord, tailWord_2009425, baseEnd_2009425] using wordTrace_append hprefix tailTrace_2009425
  have hstable : (prefixWord ++ tailWord_2009425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009425).length < 2 ^ (prefixWord ++ tailWord_2009425).sum := by decide
  have hdescent : baseEnd_2009425 < baseStart_2009425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009429 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_2009429 : Nat := 118140960795 + 2009429 * 2 ^ 59
def prefixEnd_2009429 : Nat := 4983230072969 + 3 ^ 40 * 2009429 * 2
def baseEnd_2009429 : Nat := 687868612055682555664207

theorem tailTrace_2009429 : CollatzResearch.WordTrace tailWord_2009429 prefixEnd_2009429 687868612055682555664207 := by
  unfold tailWord_2009429
  simp only [CollatzResearch.WordTrace]
  refine ⟨73289896637189390996103341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48859931091459593997402227 73289896637189390996103341)
  ·
    refine ⟨27483711238946021623538753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73289896637189390996103341 27483711238946021623538753)
    ·
      refine ⟨20612783429209516217654065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27483711238946021623538753 20612783429209516217654065)
      ·
        refine ⟨15459587571907137163240549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20612783429209516217654065 15459587571907137163240549)
        ·
          refine ⟨2898672669732588218107603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15459587571907137163240549 2898672669732588218107603)
          ·
            refine ⟨4348009004598882327161405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898672669732588218107603 4348009004598882327161405)
            ·
              refine ⟨1630503376724580872685527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4348009004598882327161405 1630503376724580872685527)
              ·
                refine ⟨2445755065086871309028291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630503376724580872685527 2445755065086871309028291)
                ·
                  refine ⟨3668632597630306963542437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445755065086871309028291 3668632597630306963542437)
                  ·
                    refine ⟨687868612055682555664207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668632597630306963542437 687868612055682555664207)
                    ·
                      rfl

theorem cell22_2009429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_2009429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009429 prefixEnd_2009429 := by exact prefixLift 2009429
  have htrace : WordTrace (prefixWord ++ tailWord_2009429) baseStart_2009429 baseEnd_2009429 := by
    simpa [prefixWord, tailWord_2009429, baseEnd_2009429] using wordTrace_append hprefix tailTrace_2009429
  have hstable : (prefixWord ++ tailWord_2009429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009429).length < 2 ^ (prefixWord ++ tailWord_2009429).sum := by decide
  have hdescent : baseEnd_2009429 < baseStart_2009429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009474 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2009474 : Nat := 118140960795 + 2009474 * 2 ^ 59
def prefixEnd_2009474 : Nat := 4983230072969 + 3 ^ 40 * 2009474 * 2
def baseEnd_2009474 : Nat := 687884016475317438289069

theorem tailTrace_2009474 : CollatzResearch.WordTrace tailWord_2009474 prefixEnd_2009474 687884016475317438289069 := by
  unfold tailWord_2009474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322884480506590920372869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48861025281350909120994317 18322884480506590920372869)
  ·
    refine ⟨3435540840094985797569913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18322884480506590920372869 3435540840094985797569913)
    ·
      refine ⟨2576655630071239348177435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3435540840094985797569913 2576655630071239348177435)
      ·
        refine ⟨3864983445106859022266153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576655630071239348177435 3864983445106859022266153)
        ·
          refine ⟨2898737583830144266699615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864983445106859022266153 2898737583830144266699615)
          ·
            refine ⟨4348106375745216400049423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898737583830144266699615 4348106375745216400049423)
            ·
              refine ⟨6522159563617824600074135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348106375745216400049423 6522159563617824600074135)
              ·
                refine ⟨9783239345426736900111203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522159563617824600074135 9783239345426736900111203)
                ·
                  refine ⟨14674859018140105350166805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783239345426736900111203 14674859018140105350166805)
                  ·
                    refine ⟨687884016475317438289069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14674859018140105350166805 687884016475317438289069)
                    ·
                      rfl

theorem cell22_2009474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2009474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009474 prefixEnd_2009474 := by exact prefixLift 2009474
  have htrace : WordTrace (prefixWord ++ tailWord_2009474) baseStart_2009474 baseEnd_2009474 := by
    simpa [prefixWord, tailWord_2009474, baseEnd_2009474] using wordTrace_append hprefix tailTrace_2009474
  have hstable : (prefixWord ++ tailWord_2009474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009474).length < 2 ^ (prefixWord ++ tailWord_2009474).sum := by decide
  have hdescent : baseEnd_2009474 < baseStart_2009474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009504 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_2009504 : Nat := 118140960795 + 2009504 * 2 ^ 59
def prefixEnd_2009504 : Nat := 4983230072969 + 3 ^ 40 * 2009504 * 2
def baseEnd_2009504 : Nat := 687894286088407360038977

theorem tailTrace_2009504 : CollatzResearch.WordTrace tailWord_2009504 prefixEnd_2009504 687894286088407360038977 := by
  unfold tailWord_2009504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646316055958839402541783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48861754741278452536722377 36646316055958839402541783)
  ·
    refine ⟨54969474083938259103812675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646316055958839402541783 54969474083938259103812675)
    ·
      refine ⟨82454211125907388655719013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54969474083938259103812675 82454211125907388655719013)
      ·
        refine ⟨15460164586107635372947315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82454211125907388655719013 15460164586107635372947315)
        ·
          refine ⟨23190246879161453059420973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460164586107635372947315 23190246879161453059420973)
          ·
            refine ⟨8696342579685544897282865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23190246879161453059420973 8696342579685544897282865)
            ·
              refine ⟨6522256934764158672962149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8696342579685544897282865 6522256934764158672962149)
              ·
                refine ⟨1222923175268279751180403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6522256934764158672962149 1222923175268279751180403)
                ·
                  refine ⟨1834384762902419626770605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222923175268279751180403 1834384762902419626770605)
                  ·
                    refine ⟨687894286088407360038977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834384762902419626770605 687894286088407360038977)
                    ·
                      rfl

theorem cell22_2009504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_2009504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009504 prefixEnd_2009504 := by exact prefixLift 2009504
  have htrace : WordTrace (prefixWord ++ tailWord_2009504) baseStart_2009504 baseEnd_2009504 := by
    simpa [prefixWord, tailWord_2009504, baseEnd_2009504] using wordTrace_append hprefix tailTrace_2009504
  have hstable : (prefixWord ++ tailWord_2009504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009504).length < 2 ^ (prefixWord ++ tailWord_2009504).sum := by decide
  have hdescent : baseEnd_2009504 < baseStart_2009504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009530 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2009530 : Nat := 118140960795 + 2009530 * 2 ^ 59
def prefixEnd_2009530 : Nat := 4983230072969 + 3 ^ 40 * 2009530 * 2
def baseEnd_2009530 : Nat := 687903186419751958888897

theorem tailTrace_2009530 : CollatzResearch.WordTrace tailWord_2009530 prefixEnd_2009530 687903186419751958888897 := by
  unfold tailWord_2009530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323395102455871311382511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48862386939882323497020029 18323395102455871311382511)
  ·
    refine ⟨27485092653683806967073767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323395102455871311382511 27485092653683806967073767)
    ·
      refine ⟨41227638980525710450610651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27485092653683806967073767 41227638980525710450610651)
      ·
        refine ⟨61841458470788565675915977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41227638980525710450610651 61841458470788565675915977)
        ·
          refine ⟨46381093853091424256936983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61841458470788565675915977 46381093853091424256936983)
          ·
            refine ⟨69571640779637136385405475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46381093853091424256936983 69571640779637136385405475)
            ·
              refine ⟨104357461169455704578108213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69571640779637136385405475 104357461169455704578108213)
              ·
                refine ⟨9783511984636472304197645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104357461169455704578108213 9783511984636472304197645)
                ·
                  refine ⟨3668816994238677114074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9783511984636472304197645 3668816994238677114074117)
                  ·
                    refine ⟨687903186419751958888897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668816994238677114074117 687903186419751958888897)
                    ·
                      rfl

theorem cell22_2009530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2009530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009530 prefixEnd_2009530 := by exact prefixLift 2009530
  have htrace : WordTrace (prefixWord ++ tailWord_2009530) baseStart_2009530 baseEnd_2009530 := by
    simpa [prefixWord, tailWord_2009530, baseEnd_2009530] using wordTrace_append hprefix tailTrace_2009530
  have hstable : (prefixWord ++ tailWord_2009530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009530).length < 2 ^ (prefixWord ++ tailWord_2009530).sum := by decide
  have hdescent : baseEnd_2009530 < baseStart_2009530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009581 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2009581 : Nat := 118140960795 + 2009581 * 2 ^ 59
def prefixEnd_2009581 : Nat := 4983230072969 + 3 ^ 40 * 2009581 * 2
def baseEnd_2009581 : Nat := 687920644762004825863741

theorem tailTrace_2009581 : CollatzResearch.WordTrace tailWord_2009581 prefixEnd_2009581 687920644762004825863741 := by
  unfold tailWord_2009581
  simp only [CollatzResearch.WordTrace]
  refine ⟨73295440532638720955636597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48863627021759147303757731 73295440532638720955636597)
  ·
    refine ⟨6871447549934880089590931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73295440532638720955636597 6871447549934880089590931)
    ·
      refine ⟨10307171324902320134386397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871447549934880089590931 10307171324902320134386397)
      ·
        refine ⟨3865189246838370050394899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10307171324902320134386397 3865189246838370050394899)
        ·
          refine ⟨5797783870257555075592349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865189246838370050394899 5797783870257555075592349)
          ·
            refine ⟨2174168951346583153347131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5797783870257555075592349 2174168951346583153347131)
            ·
              refine ⟨3261253427019874730020697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174168951346583153347131 3261253427019874730020697)
              ·
                refine ⟨2445940070264906047515523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261253427019874730020697 2445940070264906047515523)
                ·
                  refine ⟨3668910105397359071273285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445940070264906047515523 3668910105397359071273285)
                  ·
                    refine ⟨687920644762004825863741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668910105397359071273285 687920644762004825863741)
                    ·
                      rfl

theorem cell22_2009581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2009581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009581 prefixEnd_2009581 := by exact prefixLift 2009581
  have htrace : WordTrace (prefixWord ++ tailWord_2009581) baseStart_2009581 baseEnd_2009581 := by
    simpa [prefixWord, tailWord_2009581, baseEnd_2009581] using wordTrace_append hprefix tailTrace_2009581
  have hstable : (prefixWord ++ tailWord_2009581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009581).length < 2 ^ (prefixWord ++ tailWord_2009581).sum := by decide
  have hdescent : baseEnd_2009581 < baseStart_2009581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009592 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_2009592 : Nat := 118140960795 + 2009592 * 2 ^ 59
def prefixEnd_2009592 : Nat := 4983230072969 + 3 ^ 40 * 2009592 * 2
def baseEnd_2009592 : Nat := 687924410286804463838707

theorem tailTrace_2009592 : CollatzResearch.WordTrace tailWord_2009592 prefixEnd_2009592 687924410286804463838707 := by
  unfold tailWord_2009592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647920867799434917143515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48863894490399246556191353 36647920867799434917143515)
  ·
    refine ⟨54971881301699152375715273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36647920867799434917143515 54971881301699152375715273)
    ·
      refine ⟨41228910976274364281786455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54971881301699152375715273 41228910976274364281786455)
      ·
        refine ⟨61843366464411546422679683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41228910976274364281786455 61843366464411546422679683)
        ·
          refine ⟨92765049696617319634019525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61843366464411546422679683 92765049696617319634019525)
          ·
            refine ⟨17393446818115747431378661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92765049696617319634019525 17393446818115747431378661)
            ·
              refine ⟨3261271278396702643383499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17393446818115747431378661 3261271278396702643383499)
              ·
                refine ⟨4891906917595053965075249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261271278396702643383499 4891906917595053965075249)
                ·
                  refine ⟨3668930188196290473806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891906917595053965075249 3668930188196290473806437)
                  ·
                    refine ⟨687924410286804463838707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668930188196290473806437 687924410286804463838707)
                    ·
                      rfl

theorem cell22_2009592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_2009592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009592 prefixEnd_2009592 := by exact prefixLift 2009592
  have htrace : WordTrace (prefixWord ++ tailWord_2009592) baseStart_2009592 baseEnd_2009592 := by
    simpa [prefixWord, tailWord_2009592, baseEnd_2009592] using wordTrace_append hprefix tailTrace_2009592
  have hstable : (prefixWord ++ tailWord_2009592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009592).length < 2 ^ (prefixWord ++ tailWord_2009592).sum := by decide
  have hdescent : baseEnd_2009592 < baseStart_2009592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009607 : List Nat := [1, 1, 4, 3, 4, 9]
def baseStart_2009607 : Nat := 118140960795 + 2009607 * 2 ^ 59
def prefixEnd_2009607 : Nat := 4983230072969 + 3 ^ 40 * 2009607 * 2
def baseEnd_2009607 : Nat := 8492957346831474379181

theorem tailTrace_2009607 : CollatzResearch.WordTrace tailWord_2009607 prefixEnd_2009607 8492957346831474379181 := by
  unfold tailWord_2009607
  simp only [CollatzResearch.WordTrace]
  refine ⟨73296388830544527396083075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48864259220363018264055383 73296388830544527396083075)
  ·
    refine ⟨109944583245816791094124613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73296388830544527396083075 109944583245816791094124613)
    ·
      refine ⟨20614609358590648330148365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109944583245816791094124613 20614609358590648330148365)
      ·
        refine ⟨7730478509471493123805637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20614609358590648330148365 7730478509471493123805637)
        ·
          refine ⟨1449464720525904960713557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7730478509471493123805637 1449464720525904960713557)
          ·
            refine ⟨8492957346831474379181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1449464720525904960713557 8492957346831474379181)
            ·
              rfl

theorem cell22_2009607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 9].length) (baseStart_2009607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009607 prefixEnd_2009607 := by exact prefixLift 2009607
  have htrace : WordTrace (prefixWord ++ tailWord_2009607) baseStart_2009607 baseEnd_2009607 := by
    simpa [prefixWord, tailWord_2009607, baseEnd_2009607] using wordTrace_append hprefix tailTrace_2009607
  have hstable : (prefixWord ++ tailWord_2009607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009607).length < 2 ^ (prefixWord ++ tailWord_2009607).sum := by decide
  have hdescent : baseEnd_2009607 < baseStart_2009607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009613 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2009613 : Nat := 118140960795 + 2009613 * 2 ^ 59
def prefixEnd_2009613 : Nat := 4983230072969 + 3 ^ 40 * 2009613 * 2
def baseEnd_2009613 : Nat := 229310533005322469687881

theorem tailTrace_2009613 : CollatzResearch.WordTrace tailWord_2009613 prefixEnd_2009613 229310533005322469687881 := by
  unfold tailWord_2009613
  simp only [CollatzResearch.WordTrace]
  refine ⟨73296607668522790420801493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48864405112348526947200995 73296607668522790420801493)
  ·
    refine ⟨1717889242231002900487535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 73296607668522790420801493 1717889242231002900487535)
    ·
      refine ⟨2576833863346504350731303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717889242231002900487535 2576833863346504350731303)
      ·
        refine ⟨3865250795019756526096955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576833863346504350731303 3865250795019756526096955)
        ·
          refine ⟨5797876192529634789145433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865250795019756526096955 5797876192529634789145433)
          ·
            refine ⟨4348407144397226091859075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797876192529634789145433 4348407144397226091859075)
            ·
              refine ⟨6522610716595839137788613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348407144397226091859075 6522610716595839137788613)
              ·
                refine ⟨1222989509361719838335365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6522610716595839137788613 1222989509361719838335365)
                ·
                  refine ⟨229310533005322469687881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222989509361719838335365 229310533005322469687881)
                  ·
                    rfl

theorem cell22_2009613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2009613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009613 prefixEnd_2009613 := by exact prefixLift 2009613
  have htrace : WordTrace (prefixWord ++ tailWord_2009613) baseStart_2009613 baseEnd_2009613 := by
    simpa [prefixWord, tailWord_2009613, baseEnd_2009613] using wordTrace_append hprefix tailTrace_2009613
  have hstable : (prefixWord ++ tailWord_2009613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009613).length < 2 ^ (prefixWord ++ tailWord_2009613).sum := by decide
  have hdescent : baseEnd_2009613 < baseStart_2009613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009656 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_2009656 : Nat := 118140960795 + 2009656 * 2 ^ 59
def prefixEnd_2009656 : Nat := 4983230072969 + 3 ^ 40 * 2009656 * 2
def baseEnd_2009656 : Nat := 687946318794729630238511

theorem tailTrace_2009656 : CollatzResearch.WordTrace tailWord_2009656 prefixEnd_2009656 687946318794729630238511 := by
  unfold tailWord_2009656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36649088003683504382308411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48865450671578005843077881 36649088003683504382308411)
  ·
    refine ⟨54973632005525256573462617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36649088003683504382308411 54973632005525256573462617)
    ·
      refine ⟨41230224004143942430096963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54973632005525256573462617 41230224004143942430096963)
      ·
        refine ⟨61845336006215913645145445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41230224004143942430096963 61845336006215913645145445)
        ·
          refine ⟨11596000501165483808464771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61845336006215913645145445 11596000501165483808464771)
          ·
            refine ⟨17394000751748225712697157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596000501165483808464771 17394000751748225712697157)
            ·
              refine ⟨3261375140952792321130717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17394000751748225712697157 3261375140952792321130717)
              ·
                refine ⟨1223015677857297120424019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3261375140952792321130717 1223015677857297120424019)
                ·
                  refine ⟨1834523516785945680636029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223015677857297120424019 1834523516785945680636029)
                  ·
                    refine ⟨687946318794729630238511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834523516785945680636029 687946318794729630238511)
                    ·
                      rfl

theorem cell22_2009656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_2009656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009656 prefixEnd_2009656 := by exact prefixLift 2009656
  have htrace : WordTrace (prefixWord ++ tailWord_2009656) baseStart_2009656 baseEnd_2009656 := by
    simpa [prefixWord, tailWord_2009656, baseEnd_2009656] using wordTrace_append hprefix tailTrace_2009656
  have hstable : (prefixWord ++ tailWord_2009656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009656).length < 2 ^ (prefixWord ++ tailWord_2009656).sum := by decide
  have hdescent : baseEnd_2009656 < baseStart_2009656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009669 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 5]
def baseStart_2009669 : Nat := 118140960795 + 2009669 * 2 ^ 59
def prefixEnd_2009669 : Nat := 4983230072969 + 3 ^ 40 * 2009669 * 2
def baseEnd_2009669 : Nat := 229316922986800643221157

theorem tailTrace_2009669 : CollatzResearch.WordTrace tailWord_2009669 prefixEnd_2009669 229316922986800643221157 := by
  unfold tailWord_2009669
  simp only [CollatzResearch.WordTrace]
  refine ⟨73298650156319911984840061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48865766770879941323226707 73298650156319911984840061)
  ·
    refine ⟨27486993808619966994315023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73298650156319911984840061 27486993808619966994315023)
    ·
      refine ⟨41230490712929950491472535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27486993808619966994315023 41230490712929950491472535)
      ·
        refine ⟨61845736069394925737208803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41230490712929950491472535 61845736069394925737208803)
        ·
          refine ⟨92768604104092388605813205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61845736069394925737208803 92768604104092388605813205)
          ·
            refine ⟨2174264158689665357948747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92768604104092388605813205 2174264158689665357948747)
            ·
              refine ⟨3261396238034498036923121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174264158689665357948747 3261396238034498036923121)
              ·
                refine ⟨2446047178525873527692341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261396238034498036923121 2446047178525873527692341)
                ·
                  refine ⟨229316922986800643221157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446047178525873527692341 229316922986800643221157)
                  ·
                    rfl

theorem cell22_2009669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_2009669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009669 prefixEnd_2009669 := by exact prefixLift 2009669
  have htrace : WordTrace (prefixWord ++ tailWord_2009669) baseStart_2009669 baseEnd_2009669 := by
    simpa [prefixWord, tailWord_2009669, baseEnd_2009669] using wordTrace_append hprefix tailTrace_2009669
  have hstable : (prefixWord ++ tailWord_2009669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009669).length < 2 ^ (prefixWord ++ tailWord_2009669).sum := by decide
  have hdescent : baseEnd_2009669 < baseStart_2009669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009697 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 6]
def baseStart_2009697 : Nat := 118140960795 + 2009697 * 2 ^ 59
def prefixEnd_2009697 : Nat := 4983230072969 + 3 ^ 40 * 2009697 * 2
def baseEnd_2009697 : Nat := 229320117977539729987795

theorem tailTrace_2009697 : CollatzResearch.WordTrace tailWord_2009697 prefixEnd_2009697 229320117977539729987795 := by
  unfold tailWord_2009697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73299671400218472766859345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48866447600145648511239563 73299671400218472766859345)
  ·
    refine ⟨54974753550163854575144509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73299671400218472766859345 54974753550163854575144509)
    ·
      refine ⟨20615532581311445465679191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54974753550163854575144509 20615532581311445465679191)
      ·
        refine ⟨30923298871967168198518787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20615532581311445465679191 30923298871967168198518787)
        ·
          refine ⟨46384948307950752297778181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30923298871967168198518787 46384948307950752297778181)
          ·
            refine ⟨8697177807740766055833409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46384948307950752297778181 8697177807740766055833409)
            ·
              refine ⟨6522883355805574541875057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697177807740766055833409 6522883355805574541875057)
              ·
                refine ⟨4892162516854180906406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6522883355805574541875057 4892162516854180906406293)
                ·
                  refine ⟨229320117977539729987795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4892162516854180906406293 229320117977539729987795)
                  ·
                    rfl

theorem cell22_2009697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_2009697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009697 prefixEnd_2009697 := by exact prefixLift 2009697
  have htrace : WordTrace (prefixWord ++ tailWord_2009697) baseStart_2009697 baseEnd_2009697 := by
    simpa [prefixWord, tailWord_2009697, baseEnd_2009697] using wordTrace_append hprefix tailTrace_2009697
  have hstable : (prefixWord ++ tailWord_2009697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009697).length < 2 ^ (prefixWord ++ tailWord_2009697).sum := by decide
  have hdescent : baseEnd_2009697 < baseStart_2009697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009699 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 1, 4]
def baseStart_2009699 : Nat := 118140960795 + 2009699 * 2 ^ 59
def prefixEnd_2009699 : Nat := 4983230072969 + 3 ^ 40 * 2009699 * 2
def baseEnd_2009699 : Nat := 687961038573491851413379

theorem tailTrace_2009699 : CollatzResearch.WordTrace tailWord_2009699 prefixEnd_2009699 687961038573491851413379 := by
  unfold tailWord_2009699
  simp only [CollatzResearch.WordTrace]
  refine ⟨73299744346211227108432151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48866496230807484738954767 73299744346211227108432151)
  ·
    refine ⟨109949616519316840662648227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73299744346211227108432151 109949616519316840662648227)
    ·
      refine ⟨164924424778975260993972341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109949616519316840662648227 164924424778975260993972341)
      ·
        refine ⟨15461664823028930718184907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164924424778975260993972341 15461664823028930718184907)
        ·
          refine ⟨23192497234543396077277361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15461664823028930718184907 23192497234543396077277361)
          ·
            refine ⟨17394372925907547057958021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23192497234543396077277361 17394372925907547057958021)
            ·
              refine ⟨3261444923607665073367129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17394372925907547057958021 3261444923607665073367129)
              ·
                refine ⟨2446083692705748805025347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261444923607665073367129 2446083692705748805025347)
                ·
                  refine ⟨3669125539058623207538021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446083692705748805025347 3669125539058623207538021)
                  ·
                    refine ⟨687961038573491851413379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669125539058623207538021 687961038573491851413379)
                    ·
                      rfl

theorem cell22_2009699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_2009699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009699 prefixEnd_2009699 := by exact prefixLift 2009699
  have htrace : WordTrace (prefixWord ++ tailWord_2009699) baseStart_2009699 baseEnd_2009699 := by
    simpa [prefixWord, tailWord_2009699, baseEnd_2009699] using wordTrace_append hprefix tailTrace_2009699
  have hstable : (prefixWord ++ tailWord_2009699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009699).length < 2 ^ (prefixWord ++ tailWord_2009699).sum := by decide
  have hdescent : baseEnd_2009699 < baseStart_2009699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009729 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2009729 : Nat := 118140960795 + 2009729 * 2 ^ 59
def prefixEnd_2009729 : Nat := 4983230072969 + 3 ^ 40 * 2009729 * 2
def baseEnd_2009729 : Nat := 687971308186581773163287

theorem tailTrace_2009729 : CollatzResearch.WordTrace tailWord_2009729 prefixEnd_2009729 687971308186581773163287 := by
  unfold tailWord_2009729
  simp only [CollatzResearch.WordTrace]
  refine ⟨73300838536102542232024241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48867225690735028154682827 73300838536102542232024241)
  ·
    refine ⟨54975628902076906674018181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73300838536102542232024241 54975628902076906674018181)
    ·
      refine ⟨10307930419139420001378409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54975628902076906674018181 10307930419139420001378409)
      ·
        refine ⟨7730947814354565001033807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307930419139420001378409 7730947814354565001033807)
        ·
          refine ⟨11596421721531847501550711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730947814354565001033807 11596421721531847501550711)
          ·
            refine ⟨17394632582297771252326067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596421721531847501550711 17394632582297771252326067)
            ·
              refine ⟨26091948873446656878489101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17394632582297771252326067 26091948873446656878489101)
              ·
                refine ⟨9784480827542496329433413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26091948873446656878489101 9784480827542496329433413)
                ·
                  refine ⟨1834590155164218061768765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9784480827542496329433413 1834590155164218061768765)
                  ·
                    refine ⟨687971308186581773163287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834590155164218061768765 687971308186581773163287)
                    ·
                      rfl

theorem cell22_2009729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2009729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009729 prefixEnd_2009729 := by exact prefixLift 2009729
  have htrace : WordTrace (prefixWord ++ tailWord_2009729) baseStart_2009729 baseEnd_2009729 := by
    simpa [prefixWord, tailWord_2009729, baseEnd_2009729] using wordTrace_append hprefix tailTrace_2009729
  have hstable : (prefixWord ++ tailWord_2009729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009729).length < 2 ^ (prefixWord ++ tailWord_2009729).sum := by decide
  have hdescent : baseEnd_2009729 < baseStart_2009729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009757 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2009757 : Nat := 118140960795 + 2009757 * 2 ^ 59
def prefixEnd_2009757 : Nat := 4983230072969 + 3 ^ 40 * 2009757 * 2
def baseEnd_2009757 : Nat := 687980893158799033463201

theorem tailTrace_2009757 : CollatzResearch.WordTrace tailWord_2009757 prefixEnd_2009757 687980893158799033463201 := by
  unfold tailWord_2009757
  simp only [CollatzResearch.WordTrace]
  refine ⟨73301859780001103014043525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48867906520000735342695683 73301859780001103014043525)
  ·
    refine ⟨13744098708750206815133161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73301859780001103014043525 13744098708750206815133161)
    ·
      refine ⟨10308074031562655111349871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13744098708750206815133161 10308074031562655111349871)
      ·
        refine ⟨15462111047343982667024807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308074031562655111349871 15462111047343982667024807)
        ·
          refine ⟨23193166571015974000537211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462111047343982667024807 23193166571015974000537211)
          ·
            refine ⟨34789749856523961000805817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23193166571015974000537211 34789749856523961000805817)
            ·
              refine ⟨26092312392392970750604363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34789749856523961000805817 26092312392392970750604363)
              ·
                refine ⟨39138468588589456125906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26092312392392970750604363 39138468588589456125906545)
                ·
                  refine ⟨29353851441442092094429909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39138468588589456125906545 29353851441442092094429909)
                  ·
                    refine ⟨687980893158799033463201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29353851441442092094429909 687980893158799033463201)
                    ·
                      rfl

theorem cell22_2009757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2009757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009757 prefixEnd_2009757 := by exact prefixLift 2009757
  have htrace : WordTrace (prefixWord ++ tailWord_2009757) baseStart_2009757 baseEnd_2009757 := by
    simpa [prefixWord, tailWord_2009757, baseEnd_2009757] using wordTrace_append hprefix tailTrace_2009757
  have hstable : (prefixWord ++ tailWord_2009757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009757).length < 2 ^ (prefixWord ++ tailWord_2009757).sum := by decide
  have hdescent : baseEnd_2009757 < baseStart_2009757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009761 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2009761 : Nat := 118140960795 + 2009761 * 2 ^ 59
def prefixEnd_2009761 : Nat := 4983230072969 + 3 ^ 40 * 2009761 * 2
def baseEnd_2009761 : Nat := 687982262440544356363189

theorem tailTrace_2009761 : CollatzResearch.WordTrace tailWord_2009761 prefixEnd_2009761 687982262440544356363189 := by
  unfold tailWord_2009761
  simp only [CollatzResearch.WordTrace]
  refine ⟨73302005671986611697189137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48868003781324407798126091 73302005671986611697189137)
  ·
    refine ⟨54976504253989958772891853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73302005671986611697189137 54976504253989958772891853)
    ·
      refine ⟨20616189095246234539834445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54976504253989958772891853 20616189095246234539834445)
      ·
        refine ⟨7731070910717337952437917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20616189095246234539834445 7731070910717337952437917)
        ·
          refine ⟨2899151591519001732164219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7731070910717337952437917 2899151591519001732164219)
          ·
            refine ⟨4348727387278502598246329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899151591519001732164219 4348727387278502598246329)
            ·
              refine ⟨3261545540458876948684747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348727387278502598246329 3261545540458876948684747)
              ·
                refine ⟨4892318310688315423027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261545540458876948684747 4892318310688315423027121)
                ·
                  refine ⟨3669238733016236567270341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4892318310688315423027121 3669238733016236567270341)
                  ·
                    refine ⟨687982262440544356363189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669238733016236567270341 687982262440544356363189)
                    ·
                      rfl

theorem cell22_2009761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2009761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009761 prefixEnd_2009761 := by exact prefixLift 2009761
  have htrace : WordTrace (prefixWord ++ tailWord_2009761) baseStart_2009761 baseEnd_2009761 := by
    simpa [prefixWord, tailWord_2009761, baseEnd_2009761] using wordTrace_append hprefix tailTrace_2009761
  have hstable : (prefixWord ++ tailWord_2009761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009761).length < 2 ^ (prefixWord ++ tailWord_2009761).sum := by decide
  have hdescent : baseEnd_2009761 < baseStart_2009761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009782 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2009782 : Nat := 118140960795 + 2009782 * 2 ^ 59
def prefixEnd_2009782 : Nat := 4983230072969 + 3 ^ 40 * 2009782 * 2
def baseEnd_2009782 : Nat := 229329817056569100529375

theorem tailTrace_2009782 : CollatzResearch.WordTrace tailWord_2009782 prefixEnd_2009782 229329817056569100529375 := by
  unfold tailWord_2009782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581423225306908267731475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48868514403273688189135733 4581423225306908267731475)
  ·
    refine ⟨6872134837960362401597213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581423225306908267731475 6872134837960362401597213)
    ·
      refine ⟨2577050564235135900598955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6872134837960362401597213 2577050564235135900598955)
      ·
        refine ⟨3865575846352703850898433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577050564235135900598955 3865575846352703850898433)
        ·
          refine ⟨2899181884764527888173825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3865575846352703850898433 2899181884764527888173825)
          ·
            refine ⟨2174386413573395916130369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899181884764527888173825 2174386413573395916130369)
            ·
              refine ⟨1630789810180046937097777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174386413573395916130369 1630789810180046937097777)
              ·
                refine ⟨1223092357635035202823333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630789810180046937097777 1223092357635035202823333)
                ·
                  refine ⟨229329817056569100529375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223092357635035202823333 229329817056569100529375)
                  ·
                    rfl

theorem cell22_2009782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2009782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009782 prefixEnd_2009782 := by exact prefixLift 2009782
  have htrace : WordTrace (prefixWord ++ tailWord_2009782) baseStart_2009782 baseEnd_2009782 := by
    simpa [prefixWord, tailWord_2009782, baseEnd_2009782] using wordTrace_append hprefix tailTrace_2009782
  have hstable : (prefixWord ++ tailWord_2009782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009782).length < 2 ^ (prefixWord ++ tailWord_2009782).sum := by decide
  have hdescent : baseEnd_2009782 < baseStart_2009782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009793 : List Nat := [1, 2, 6, 2, 1, 2, 1, 7]
def baseStart_2009793 : Nat := 118140960795 + 2009793 * 2 ^ 59
def prefixEnd_2009793 : Nat := 4983230072969 + 3 ^ 40 * 2009793 * 2
def baseEnd_2009793 : Nat := 76443690743834104395899

theorem tailTrace_2009793 : CollatzResearch.WordTrace tailWord_2009793 prefixEnd_2009793 76443690743834104395899 := by
  unfold tailWord_2009793
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303172807870681162354033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48868781871913787441569355 73303172807870681162354033)
  ·
    refine ⟨54977379605903010871765525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73303172807870681162354033 54977379605903010871765525)
    ·
      refine ⟨2577064669026703634614009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54977379605903010871765525 2577064669026703634614009)
      ·
        refine ⟨1932798501770027725960507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2577064669026703634614009 1932798501770027725960507)
        ·
          refine ⟨2899197752655041588940761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932798501770027725960507 2899197752655041588940761)
          ·
            refine ⟨2174398314491281191705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899197752655041588940761 2174398314491281191705571)
            ·
              refine ⟨3261597471736921787558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174398314491281191705571 3261597471736921787558357)
              ·
                refine ⟨76443690743834104395899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3261597471736921787558357 76443690743834104395899)
                ·
                  rfl

theorem cell22_2009793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 7].length) (baseStart_2009793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009793 prefixEnd_2009793 := by exact prefixLift 2009793
  have htrace : WordTrace (prefixWord ++ tailWord_2009793) baseStart_2009793 baseEnd_2009793 := by
    simpa [prefixWord, tailWord_2009793, baseEnd_2009793] using wordTrace_append hprefix tailTrace_2009793
  have hstable : (prefixWord ++ tailWord_2009793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009793).length < 2 ^ (prefixWord ++ tailWord_2009793).sum := by decide
  have hdescent : baseEnd_2009793 < baseStart_2009793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009896 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2009896 : Nat := 118140960795 + 2009896 * 2 ^ 59
def prefixEnd_2009896 : Nat := 4983230072969 + 3 ^ 40 * 2009896 * 2
def baseEnd_2009896 : Nat := 688028475699449004237775

theorem tailTrace_2009896 : CollatzResearch.WordTrace tailWord_2009896 prefixEnd_2009896 688028475699449004237775 := by
  unfold tailWord_2009896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36653464763248764876676771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48871286350998353168902361 36653464763248764876676771)
  ·
    refine ⟨54980197144873147315015157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36653464763248764876676771 54980197144873147315015157)
    ·
      refine ⟨5154393482331857560782671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54980197144873147315015157 5154393482331857560782671)
      ·
        refine ⟨7731590223497786341174007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154393482331857560782671 7731590223497786341174007)
        ·
          refine ⟨11597385335246679511761011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731590223497786341174007 11597385335246679511761011)
          ·
            refine ⟨17396078002870019267641517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597385335246679511761011 17396078002870019267641517)
            ·
              refine ⟨6523529251076257225365569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17396078002870019267641517 6523529251076257225365569)
              ·
                refine ⟨4892646938307192919024177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523529251076257225365569 4892646938307192919024177)
                ·
                  refine ⟨3669485203730394689268133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4892646938307192919024177 3669485203730394689268133)
                  ·
                    refine ⟨688028475699449004237775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669485203730394689268133 688028475699449004237775)
                    ·
                      rfl

theorem cell22_2009896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2009896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009896 prefixEnd_2009896 := by exact prefixLift 2009896
  have htrace : WordTrace (prefixWord ++ tailWord_2009896) baseStart_2009896 baseEnd_2009896 := by
    simpa [prefixWord, tailWord_2009896, baseEnd_2009896] using wordTrace_append hprefix tailTrace_2009896
  have hstable : (prefixWord ++ tailWord_2009896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009896).length < 2 ^ (prefixWord ++ tailWord_2009896).sum := by decide
  have hdescent : baseEnd_2009896 < baseStart_2009896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009956 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2009956 : Nat := 118140960795 + 2009956 * 2 ^ 59
def prefixEnd_2009956 : Nat := 4983230072969 + 3 ^ 40 * 2009956 * 2
def baseEnd_2009956 : Nat := 229349671641876282579197

theorem tailTrace_2009956 : CollatzResearch.WordTrace tailWord_2009956 prefixEnd_2009956 229349671641876282579197 := by
  unfold tailWord_2009956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654558953140080000268861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48872745270853440000358481 36654558953140080000268861)
  ·
    refine ⟨13745459607427530000100823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36654558953140080000268861 13745459607427530000100823)
    ·
      refine ⟨20618189411141295000151235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745459607427530000100823 20618189411141295000151235)
      ·
        refine ⟨30927284116711942500226853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618189411141295000151235 30927284116711942500226853)
        ·
          refine ⟨5798865771883489218792535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30927284116711942500226853 5798865771883489218792535)
          ·
            refine ⟨8698298657825233828188803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798865771883489218792535 8698298657825233828188803)
            ·
              refine ⟨13047447986737850742283205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698298657825233828188803 13047447986737850742283205)
              ·
                refine ⟨2446396497513347014178101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13047447986737850742283205 2446396497513347014178101)
                ·
                  refine ⟨229349671641876282579197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446396497513347014178101 229349671641876282579197)
                  ·
                    rfl

theorem cell22_2009956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2009956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009956 prefixEnd_2009956 := by exact prefixLift 2009956
  have htrace : WordTrace (prefixWord ++ tailWord_2009956) baseStart_2009956 baseEnd_2009956 := by
    simpa [prefixWord, tailWord_2009956, baseEnd_2009956] using wordTrace_append hprefix tailTrace_2009956
  have hstable : (prefixWord ++ tailWord_2009956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009956).length < 2 ^ (prefixWord ++ tailWord_2009956).sum := by decide
  have hdescent : baseEnd_2009956 < baseStart_2009956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009960 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2009960 : Nat := 118140960795 + 2009960 * 2 ^ 59
def prefixEnd_2009960 : Nat := 4983230072969 + 3 ^ 40 * 2009960 * 2
def baseEnd_2009960 : Nat := 688050384207374170637579

theorem tailTrace_2009960 : CollatzResearch.WordTrace tailWord_2009960 prefixEnd_2009960 688050384207374170637579 := by
  unfold tailWord_2009960
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654631899132834341841667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48872842532177112455788889 36654631899132834341841667)
  ·
    refine ⟨54981947848699251512762501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654631899132834341841667 54981947848699251512762501)
    ·
      refine ⟨10309115221631109658642969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54981947848699251512762501 10309115221631109658642969)
      ·
        refine ⟨7731836416223332243982227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10309115221631109658642969 7731836416223332243982227)
        ·
          refine ⟨11597754624334998365973341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731836416223332243982227 11597754624334998365973341)
          ·
            refine ⟨4349157984125624387240003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11597754624334998365973341 4349157984125624387240003)
            ·
              refine ⟨6523736976188436580860005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349157984125624387240003 6523736976188436580860005)
              ·
                refine ⟨1223200683035331858911251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6523736976188436580860005 1223200683035331858911251)
                ·
                  refine ⟨1834801024552997788366877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223200683035331858911251 1834801024552997788366877)
                  ·
                    refine ⟨688050384207374170637579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834801024552997788366877 688050384207374170637579)
                    ·
                      rfl

theorem cell22_2009960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2009960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2009960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2009960 prefixEnd_2009960 := by exact prefixLift 2009960
  have htrace : WordTrace (prefixWord ++ tailWord_2009960) baseStart_2009960 baseEnd_2009960 := by
    simpa [prefixWord, tailWord_2009960, baseEnd_2009960] using wordTrace_append hprefix tailTrace_2009960
  have hstable : (prefixWord ++ tailWord_2009960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009960).length < 2 ^ (prefixWord ++ tailWord_2009960).sum := by decide
  have hdescent : baseEnd_2009960 < baseStart_2009960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010018 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2010018 : Nat := 118140960795 + 2010018 * 2 ^ 59
def prefixEnd_2010018 : Nat := 4983230072969 + 3 ^ 40 * 2010018 * 2
def baseEnd_2010018 : Nat := 229356746264227117562467

theorem tailTrace_2010018 : CollatzResearch.WordTrace tailWord_2010018 prefixEnd_2010018 229356746264227117562467 := by
  unfold tailWord_2010018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327844808013886147323677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48874252821370363059529805 18327844808013886147323677)
  ·
    refine ⟨6872941803005207305246379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18327844808013886147323677 6872941803005207305246379)
    ·
      refine ⟨10309412704507810957869569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872941803005207305246379 10309412704507810957869569)
      ·
        refine ⟨7732059528380858218402177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10309412704507810957869569 7732059528380858218402177)
        ·
          refine ⟨5799044646285643663801633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7732059528380858218402177 5799044646285643663801633)
          ·
            refine ⟨4349283484714232747851225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799044646285643663801633 4349283484714232747851225)
            ·
              refine ⟨3261962613535674560888419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349283484714232747851225 3261962613535674560888419)
              ·
                refine ⟨4892943920303511841332629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261962613535674560888419 4892943920303511841332629)
                ·
                  refine ⟨229356746264227117562467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4892943920303511841332629 229356746264227117562467)
                  ·
                    rfl

theorem cell22_2010018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2010018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010018 prefixEnd_2010018 := by exact prefixLift 2010018
  have htrace : WordTrace (prefixWord ++ tailWord_2010018) baseStart_2010018 baseEnd_2010018 := by
    simpa [prefixWord, tailWord_2010018, baseEnd_2010018] using wordTrace_append hprefix tailTrace_2010018
  have hstable : (prefixWord ++ tailWord_2010018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010018).length < 2 ^ (prefixWord ++ tailWord_2010018).sum := by decide
  have hdescent : baseEnd_2010018 < baseStart_2010018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010046 : List Nat := [4, 2, 1, 1, 1, 2, 3, 8]
def baseStart_2010046 : Nat := 118140960795 + 2010046 * 2 ^ 59
def prefixEnd_2010046 : Nat := 4983230072969 + 3 ^ 40 * 2010046 * 2
def baseEnd_2010046 : Nat := 76453313751655401443035

theorem tailTrace_2010046 : CollatzResearch.WordTrace tailWord_2010046 prefixEnd_2010046 76453313751655401443035 := by
  unfold tailWord_2010046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164050059494263171414249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48874933650636070247542661 9164050059494263171414249)
  ·
    refine ⟨6873037544620697378560687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164050059494263171414249 6873037544620697378560687)
    ·
      refine ⟨10309556316931046067841031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873037544620697378560687 10309556316931046067841031)
      ·
        refine ⟨15464334475396569101761547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10309556316931046067841031 15464334475396569101761547)
        ·
          refine ⟨23196501713094853652642321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15464334475396569101761547 23196501713094853652642321)
          ·
            refine ⟨17397376284821140239481741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23196501713094853652642321 17397376284821140239481741)
            ·
              refine ⟨6524016106807927589805653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17397376284821140239481741 6524016106807927589805653)
              ·
                refine ⟨76453313751655401443035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6524016106807927589805653 76453313751655401443035)
                ·
                  rfl

theorem cell22_2010046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_2010046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010046 prefixEnd_2010046 := by exact prefixLift 2010046
  have htrace : WordTrace (prefixWord ++ tailWord_2010046) baseStart_2010046 baseEnd_2010046 := by
    simpa [prefixWord, tailWord_2010046, baseEnd_2010046] using wordTrace_append hprefix tailTrace_2010046
  have hstable : (prefixWord ++ tailWord_2010046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010046).length < 2 ^ (prefixWord ++ tailWord_2010046).sum := by decide
  have hdescent : baseEnd_2010046 < baseStart_2010046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010168 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_2010168 : Nat := 118140960795 + 2010168 * 2 ^ 59
def prefixEnd_2010168 : Nat := 4983230072969 + 3 ^ 40 * 2010168 * 2
def baseEnd_2010168 : Nat := 688121586858130961436941

theorem tailTrace_2010168 : CollatzResearch.WordTrace tailWord_2010168 prefixEnd_2010168 688121586858130961436941 := by
  unfold tailWord_2010168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658425090756060103627579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48877900121008080138170105 36658425090756060103627579)
  ·
    refine ⟨54987637636134090155441369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36658425090756060103627579 54987637636134090155441369)
    ·
      refine ⟨41240728227100567616581027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54987637636134090155441369 41240728227100567616581027)
      ·
        refine ⟨61861092340650851424871541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41240728227100567616581027 61861092340650851424871541)
        ·
          refine ⟨5799477406936017321081707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61861092340650851424871541 5799477406936017321081707)
          ·
            refine ⟨8699216110404025981622561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799477406936017321081707 8699216110404025981622561)
            ·
              refine ⟨6524412082803019486216921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8699216110404025981622561 6524412082803019486216921)
              ·
                refine ⟨4893309062102264614662691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524412082803019486216921 4893309062102264614662691)
                ·
                  refine ⟨7339963593153396921994037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893309062102264614662691 7339963593153396921994037)
                  ·
                    refine ⟨688121586858130961436941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7339963593153396921994037 688121586858130961436941)
                    ·
                      rfl

theorem cell22_2010168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_2010168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010168 prefixEnd_2010168 := by exact prefixLift 2010168
  have htrace : WordTrace (prefixWord ++ tailWord_2010168) baseStart_2010168 baseEnd_2010168 := by
    simpa [prefixWord, tailWord_2010168, baseEnd_2010168] using wordTrace_append hprefix tailTrace_2010168
  have hstable : (prefixWord ++ tailWord_2010168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010168).length < 2 ^ (prefixWord ++ tailWord_2010168).sum := by decide
  have hdescent : baseEnd_2010168 < baseStart_2010168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010172 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2010172 : Nat := 118140960795 + 2010172 * 2 ^ 59
def prefixEnd_2010172 : Nat := 4983230072969 + 3 ^ 40 * 2010172 * 2
def baseEnd_2010172 : Nat := 688122956139876284336929

theorem tailTrace_2010172 : CollatzResearch.WordTrace tailWord_2010172 prefixEnd_2010172 688122956139876284336929 := by
  unfold tailWord_2010172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658498036748814445200385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48877997382331752593600513 36658498036748814445200385)
  ·
    refine ⟨27493873527561610833900289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36658498036748814445200385 27493873527561610833900289)
    ·
      refine ⟨20620405145671208125425217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27493873527561610833900289 20620405145671208125425217)
      ·
        refine ⟨15465303859253406094068913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20620405145671208125425217 15465303859253406094068913)
        ·
          refine ⟨11598977894440054570551685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15465303859253406094068913 11598977894440054570551685)
          ·
            refine ⟨2174808355207510231978441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11598977894440054570551685 2174808355207510231978441)
            ·
              refine ⟨1631106266405632673983831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174808355207510231978441 1631106266405632673983831)
              ·
                refine ⟨2446659399608449010975747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631106266405632673983831 2446659399608449010975747)
                ·
                  refine ⟨3669989099412673516463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446659399608449010975747 3669989099412673516463621)
                  ·
                    refine ⟨688122956139876284336929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669989099412673516463621 688122956139876284336929)
                    ·
                      rfl

theorem cell22_2010172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2010172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010172 prefixEnd_2010172 := by exact prefixLift 2010172
  have htrace : WordTrace (prefixWord ++ tailWord_2010172) baseStart_2010172 baseEnd_2010172 := by
    simpa [prefixWord, tailWord_2010172, baseEnd_2010172] using wordTrace_append hprefix tailTrace_2010172
  have hstable : (prefixWord ++ tailWord_2010172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010172).length < 2 ^ (prefixWord ++ tailWord_2010172).sum := by decide
  have hdescent : baseEnd_2010172 < baseStart_2010172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010215 : List Nat := [1, 1, 5, 1, 1, 5, 2, 6]
def baseStart_2010215 : Nat := 118140960795 + 2010215 * 2 ^ 59
def prefixEnd_2010215 : Nat := 4983230072969 + 3 ^ 40 * 2010215 * 2
def baseEnd_2010215 : Nat := 76459741768737611723533

theorem tailTrace_2010215 : CollatzResearch.WordTrace tailWord_2010215 prefixEnd_2010215 76459741768737611723533 := by
  unfold tailWord_2010215
  simp only [CollatzResearch.WordTrace]
  refine ⟨73318564412341847234216099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48879042941561231489477399 73318564412341847234216099)
  ·
    refine ⟨109977846618512770851324149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73318564412341847234216099 109977846618512770851324149)
    ·
      refine ⟨10310423120485572267311639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109977846618512770851324149 10310423120485572267311639)
      ·
        refine ⟨15465634680728358400967459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310423120485572267311639 15465634680728358400967459)
        ·
          refine ⟨23198452021092537601451189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15465634680728358400967459 23198452021092537601451189)
          ·
            refine ⟨2174854876977425400136049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23198452021092537601451189 2174854876977425400136049)
            ·
              refine ⟨1631141157733069050102037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174854876977425400136049 1631141157733069050102037)
              ·
                refine ⟨76459741768737611723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1631141157733069050102037 76459741768737611723533)
                ·
                  rfl

theorem cell22_2010215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 6].length) (baseStart_2010215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010215 prefixEnd_2010215 := by exact prefixLift 2010215
  have htrace : WordTrace (prefixWord ++ tailWord_2010215) baseStart_2010215 baseEnd_2010215 := by
    simpa [prefixWord, tailWord_2010215, baseEnd_2010215] using wordTrace_append hprefix tailTrace_2010215
  have hstable : (prefixWord ++ tailWord_2010215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010215).length < 2 ^ (prefixWord ++ tailWord_2010215).sum := by decide
  have hdescent : baseEnd_2010215 < baseStart_2010215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010238 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2010238 : Nat := 118140960795 + 2010238 * 2 ^ 59
def prefixEnd_2010238 : Nat := 4983230072969 + 3 ^ 40 * 2010238 * 2
def baseEnd_2010238 : Nat := 229381849762891370728909

theorem tailTrace_2010238 : CollatzResearch.WordTrace tailWord_2010238 prefixEnd_2010238 229381849762891370728909 := by
  unfold tailWord_2010238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164925411407315270287921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48879602194172348108202245 9164925411407315270287921)
  ·
    refine ⟨6873694058555486452715941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164925411407315270287921 6873694058555486452715941)
    ·
      refine ⟨1288817635979153709884239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6873694058555486452715941 1288817635979153709884239)
      ·
        refine ⟨1933226453968730564826359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288817635979153709884239 1933226453968730564826359)
        ·
          refine ⟨2899839680953095847239539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933226453968730564826359 2899839680953095847239539)
          ·
            refine ⟨4349759521429643770859309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899839680953095847239539 4349759521429643770859309)
            ·
              refine ⟨1631159820536116414072241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4349759521429643770859309 1631159820536116414072241)
              ·
                refine ⟨1223369865402087310554181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631159820536116414072241 1223369865402087310554181)
                ·
                  refine ⟨229381849762891370728909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223369865402087310554181 229381849762891370728909)
                  ·
                    rfl

theorem cell22_2010238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2010238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010238 prefixEnd_2010238 := by exact prefixLift 2010238
  have htrace : WordTrace (prefixWord ++ tailWord_2010238) baseStart_2010238 baseEnd_2010238 := by
    simpa [prefixWord, tailWord_2010238, baseEnd_2010238] using wordTrace_append hprefix tailTrace_2010238
  have hstable : (prefixWord ++ tailWord_2010238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010238).length < 2 ^ (prefixWord ++ tailWord_2010238).sum := by decide
  have hdescent : baseEnd_2010238 < baseStart_2010238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010243 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 5]
def baseStart_2010243 : Nat := 118140960795 + 2010243 * 2 ^ 59
def prefixEnd_2010243 : Nat := 4983230072969 + 3 ^ 40 * 2010243 * 2
def baseEnd_2010243 : Nat := 229382420296951921937237

theorem tailTrace_2010243 : CollatzResearch.WordTrace tailWord_2010243 prefixEnd_2010243 229382420296951921937237 := by
  unfold tailWord_2010243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73319585656240408016235383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48879723770826938677490255 73319585656240408016235383)
  ·
    refine ⟨109979378484360612024353075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73319585656240408016235383 109979378484360612024353075)
    ·
      refine ⟨164969067726540918036529613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109979378484360612024353075 164969067726540918036529613)
      ·
        refine ⟨61863400397452844263698605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164969067726540918036529613 61863400397452844263698605)
        ·
          refine ⟨23198775149044816598886977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61863400397452844263698605 23198775149044816598886977)
          ·
            refine ⟨17399081361783612449165233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23198775149044816598886977 17399081361783612449165233)
            ·
              refine ⟨13049311021337709336873925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17399081361783612449165233 13049311021337709336873925)
              ·
                refine ⟨2446745816500820500663861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13049311021337709336873925 2446745816500820500663861)
                ·
                  refine ⟨229382420296951921937237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446745816500820500663861 229382420296951921937237)
                  ·
                    rfl

theorem cell22_2010243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].length) (baseStart_2010243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010243 prefixEnd_2010243 := by exact prefixLift 2010243
  have htrace : WordTrace (prefixWord ++ tailWord_2010243) baseStart_2010243 baseEnd_2010243 := by
    simpa [prefixWord, tailWord_2010243, baseEnd_2010243] using wordTrace_append hprefix tailTrace_2010243
  have hstable : (prefixWord ++ tailWord_2010243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010243).length < 2 ^ (prefixWord ++ tailWord_2010243).sum := by decide
  have hdescent : baseEnd_2010243 < baseStart_2010243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010335 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_2010335 : Nat := 118140960795 + 2010335 * 2 ^ 59
def prefixEnd_2010335 : Nat := 4983230072969 + 3 ^ 40 * 2010335 * 2
def baseEnd_2010335 : Nat := 688178754370998192511429

theorem tailTrace_2010335 : CollatzResearch.WordTrace tailWord_2010335 prefixEnd_2010335 688178754370998192511429 := by
  unfold tailWord_2010335
  simp only [CollatzResearch.WordTrace]
  refine ⟨73322941171907107728584459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48881960781271405152389639 73322941171907107728584459)
  ·
    refine ⟨109984411757860661592876689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73322941171907107728584459 109984411757860661592876689)
    ·
      refine ⟨82488308818395496194657517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109984411757860661592876689 82488308818395496194657517)
      ·
        refine ⟨30933115806898311072996569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82488308818395496194657517 30933115806898311072996569)
        ·
          refine ⟨23199836855173733304747427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30933115806898311072996569 23199836855173733304747427)
          ·
            refine ⟨34799755282760599957121141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23199836855173733304747427 34799755282760599957121141)
            ·
              refine ⟨3262477057758806245980107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34799755282760599957121141 3262477057758806245980107)
              ·
                refine ⟨4893715586638209368970161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262477057758806245980107 4893715586638209368970161)
                ·
                  refine ⟨3670286689978657026727621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893715586638209368970161 3670286689978657026727621)
                  ·
                    refine ⟨688178754370998192511429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670286689978657026727621 688178754370998192511429)
                    ·
                      rfl

theorem cell22_2010335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_2010335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010335 prefixEnd_2010335 := by exact prefixLift 2010335
  have htrace : WordTrace (prefixWord ++ tailWord_2010335) baseStart_2010335 baseEnd_2010335 := by
    simpa [prefixWord, tailWord_2010335, baseEnd_2010335] using wordTrace_append hprefix tailTrace_2010335
  have hstable : (prefixWord ++ tailWord_2010335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010335).length < 2 ^ (prefixWord ++ tailWord_2010335).sum := by decide
  have hdescent : baseEnd_2010335 < baseStart_2010335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010341 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_2010341 : Nat := 118140960795 + 2010341 * 2 ^ 59
def prefixEnd_2010341 : Nat := 4983230072969 + 3 ^ 40 * 2010341 * 2
def baseEnd_2010341 : Nat := 688180808293616176861411

theorem tailTrace_2010341 : CollatzResearch.WordTrace tailWord_2010341 prefixEnd_2010341 688180808293616176861411 := by
  unfold tailWord_2010341
  simp only [CollatzResearch.WordTrace]
  refine ⟨73323160009885370753302877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48882106673256913835535251 73323160009885370753302877)
  ·
    refine ⟨27496185003707014032488579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73323160009885370753302877 27496185003707014032488579)
    ·
      refine ⟨41244277505560521048732869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27496185003707014032488579 41244277505560521048732869)
      ·
        refine ⟨7733302032292597696637413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41244277505560521048732869 7733302032292597696637413)
        ·
          refine ⟨1449994131054862068119515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7733302032292597696637413 1449994131054862068119515)
          ·
            refine ⟨2174991196582293102179273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449994131054862068119515 2174991196582293102179273)
            ·
              refine ⟨1631243397436719826634455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174991196582293102179273 1631243397436719826634455)
              ·
                refine ⟨2446865096155079739951683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631243397436719826634455 2446865096155079739951683)
                ·
                  refine ⟨3670297644232619609927525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446865096155079739951683 3670297644232619609927525)
                  ·
                    refine ⟨688180808293616176861411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670297644232619609927525 688180808293616176861411)
                    ·
                      rfl

theorem cell22_2010341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_2010341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010341 prefixEnd_2010341 := by exact prefixLift 2010341
  have htrace : WordTrace (prefixWord ++ tailWord_2010341) baseStart_2010341 baseEnd_2010341 := by
    simpa [prefixWord, tailWord_2010341, baseEnd_2010341] using wordTrace_append hprefix tailTrace_2010341
  have hstable : (prefixWord ++ tailWord_2010341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010341).length < 2 ^ (prefixWord ++ tailWord_2010341).sum := by decide
  have hdescent : baseEnd_2010341 < baseStart_2010341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010356 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2010356 : Nat := 118140960795 + 2010356 * 2 ^ 59
def prefixEnd_2010356 : Nat := 4983230072969 + 3 ^ 40 * 2010356 * 2
def baseEnd_2010356 : Nat := 229395314366720379245455

theorem tailTrace_2010356 : CollatzResearch.WordTrace tailWord_2010356 prefixEnd_2010356 229395314366720379245455 := by
  unfold tailWord_2010356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36661853552415514157549461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48882471403220685543399281 36661853552415514157549461)
  ·
    refine ⟨1718524385269477226135131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36661853552415514157549461 1718524385269477226135131)
    ·
      refine ⟨2577786577904215839202697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718524385269477226135131 2577786577904215839202697)
      ·
        refine ⟨1933339933428161879402023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2577786577904215839202697 1933339933428161879402023)
        ·
          refine ⟨2900009900142242819103035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933339933428161879402023 2900009900142242819103035)
          ·
            refine ⟨4350014850213364228654553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900009900142242819103035 4350014850213364228654553)
            ·
              refine ⟨3262511137660023171490915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350014850213364228654553 3262511137660023171490915)
              ·
                refine ⟨4893766706490034757236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262511137660023171490915 4893766706490034757236373)
                ·
                  refine ⟨229395314366720379245455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4893766706490034757236373 229395314366720379245455)
                  ·
                    rfl

theorem cell22_2010356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2010356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010356 prefixEnd_2010356 := by exact prefixLift 2010356
  have htrace : WordTrace (prefixWord ++ tailWord_2010356) baseStart_2010356 baseEnd_2010356 := by
    simpa [prefixWord, tailWord_2010356, baseEnd_2010356] using wordTrace_append hprefix tailTrace_2010356
  have hstable : (prefixWord ++ tailWord_2010356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010356).length < 2 ^ (prefixWord ++ tailWord_2010356).sum := by decide
  have hdescent : baseEnd_2010356 < baseStart_2010356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010382 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2010382 : Nat := 118140960795 + 2010382 * 2 ^ 59
def prefixEnd_2010382 : Nat := 4983230072969 + 3 ^ 40 * 2010382 * 2
def baseEnd_2010382 : Nat := 688194843431505736586285

theorem tailTrace_2010382 : CollatzResearch.WordTrace tailWord_2010382 prefixEnd_2010382 688194843431505736586285 := by
  unfold tailWord_2010382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165581925342104344443175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48883103601824556503696933 9165581925342104344443175)
  ·
    refine ⟨13748372888013156516664763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9165581925342104344443175 13748372888013156516664763)
    ·
      refine ⟨20622559332019734774997145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13748372888013156516664763 20622559332019734774997145)
      ·
        refine ⟨15466919499014801081247859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20622559332019734774997145 15466919499014801081247859)
        ·
          refine ⟨23200379248522201621871789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15466919499014801081247859 23200379248522201621871789)
          ·
            refine ⟨8700142218195825608201921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23200379248522201621871789 8700142218195825608201921)
            ·
              refine ⟨6525106663646869206151441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700142218195825608201921 6525106663646869206151441)
              ·
                refine ⟨4893829997735151904613581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525106663646869206151441 4893829997735151904613581)
                ·
                  refine ⟨1835186249150681964230093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4893829997735151904613581 1835186249150681964230093)
                  ·
                    refine ⟨688194843431505736586285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835186249150681964230093 688194843431505736586285)
                    ·
                      rfl

theorem cell22_2010382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2010382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010382 prefixEnd_2010382 := by exact prefixLift 2010382
  have htrace : WordTrace (prefixWord ++ tailWord_2010382) baseStart_2010382 baseEnd_2010382 := by
    simpa [prefixWord, tailWord_2010382, baseEnd_2010382] using wordTrace_append hprefix tailTrace_2010382
  have hstable : (prefixWord ++ tailWord_2010382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010382).length < 2 ^ (prefixWord ++ tailWord_2010382).sum := by decide
  have hdescent : baseEnd_2010382 < baseStart_2010382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010429 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2010429 : Nat := 118140960795 + 2010429 * 2 ^ 59
def prefixEnd_2010429 : Nat := 4983230072969 + 3 ^ 40 * 2010429 * 2
def baseEnd_2010429 : Nat := 229403644164004426887047

theorem tailTrace_2010429 : CollatzResearch.WordTrace tailWord_2010429 prefixEnd_2010429 229403644164004426887047 := by
  unfold tailWord_2010429
  simp only [CollatzResearch.WordTrace]
  refine ⟨73326369633566561782506341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48884246422377707855004227 73326369633566561782506341)
  ·
    refine ⟨13748694306293730334219939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73326369633566561782506341 13748694306293730334219939)
    ·
      refine ⟨20623041459440595501329909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13748694306293730334219939 20623041459440595501329909)
      ·
        refine ⟨1933410136822555828249679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20623041459440595501329909 1933410136822555828249679)
        ·
          refine ⟨2900115205233833742374519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933410136822555828249679 2900115205233833742374519)
          ·
            refine ⟨4350172807850750613561779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900115205233833742374519 4350172807850750613561779)
            ·
              refine ⟨6525259211776125920342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350172807850750613561779 6525259211776125920342669)
              ·
                refine ⟨2446972204416047220128501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525259211776125920342669 2446972204416047220128501)
                ·
                  refine ⟨229403644164004426887047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446972204416047220128501 229403644164004426887047)
                  ·
                    rfl

theorem cell22_2010429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2010429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010429 prefixEnd_2010429 := by exact prefixLift 2010429
  have htrace : WordTrace (prefixWord ++ tailWord_2010429) baseStart_2010429 baseEnd_2010429 := by
    simpa [prefixWord, tailWord_2010429, baseEnd_2010429] using wordTrace_append hprefix tailTrace_2010429
  have hstable : (prefixWord ++ tailWord_2010429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010429).length < 2 ^ (prefixWord ++ tailWord_2010429).sum := by decide
  have hdescent : baseEnd_2010429 < baseStart_2010429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010455 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2010455 : Nat := 118140960795 + 2010455 * 2 ^ 59
def prefixEnd_2010455 : Nat := 4983230072969 + 3 ^ 40 * 2010455 * 2
def baseEnd_2010455 : Nat := 688219832823357879511061

theorem tailTrace_2010455 : CollatzResearch.WordTrace tailWord_2010455 prefixEnd_2010455 688219832823357879511061 := by
  unfold tailWord_2010455
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327317931472368222952819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48884878620981578815301879 73327317931472368222952819)
  ·
    refine ⟨109990976897208552334429229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73327317931472368222952819 109990976897208552334429229)
    ·
      refine ⟨41246616336453207125410961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109990976897208552334429229 41246616336453207125410961)
      ·
        refine ⟨30934962252339905344058221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41246616336453207125410961 30934962252339905344058221)
        ·
          refine ⟨11600610844627464504021833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30934962252339905344058221 11600610844627464504021833)
          ·
            refine ⟨8700458133470598378016375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600610844627464504021833 8700458133470598378016375)
            ·
              refine ⟨13050687200205897567024563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700458133470598378016375 13050687200205897567024563)
              ·
                refine ⟨19576030800308846350536845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050687200205897567024563 19576030800308846350536845)
                ·
                  refine ⟨7341011550115817381451317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19576030800308846350536845 7341011550115817381451317)
                  ·
                    refine ⟨688219832823357879511061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7341011550115817381451317 688219832823357879511061)
                    ·
                      rfl

theorem cell22_2010455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2010455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010455 prefixEnd_2010455 := by exact prefixLift 2010455
  have htrace : WordTrace (prefixWord ++ tailWord_2010455) baseStart_2010455 baseEnd_2010455 := by
    simpa [prefixWord, tailWord_2010455, baseEnd_2010455] using wordTrace_append hprefix tailTrace_2010455
  have hstable : (prefixWord ++ tailWord_2010455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010455).length < 2 ^ (prefixWord ++ tailWord_2010455).sum := by decide
  have hdescent : baseEnd_2010455 < baseStart_2010455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010504 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2010504 : Nat := 118140960795 + 2010504 * 2 ^ 59
def prefixEnd_2010504 : Nat := 4983230072969 + 3 ^ 40 * 2010504 * 2
def baseEnd_2010504 : Nat := 688236606524738085035911

theorem tailTrace_2010504 : CollatzResearch.WordTrace tailWord_2010504 prefixEnd_2010504 688236606524738085035911 := by
  unfold tailWord_2010504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36664552554147424795743283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48886070072196566394324377 36664552554147424795743283)
  ·
    refine ⟨54996828831221137193614925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36664552554147424795743283 54996828831221137193614925)
    ·
      refine ⟨20623810811707926447605597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54996828831221137193614925 20623810811707926447605597)
      ·
        refine ⟨7733929054390472417852099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20623810811707926447605597 7733929054390472417852099)
        ·
          refine ⟨11600893581585708626778149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733929054390472417852099 11600893581585708626778149)
          ·
            refine ⟨2175167546547320367520903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11600893581585708626778149 2175167546547320367520903)
            ·
              refine ⟨3262751319820980551281355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175167546547320367520903 3262751319820980551281355)
              ·
                refine ⟨4894126979731470826922033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262751319820980551281355 4894126979731470826922033)
                ·
                  refine ⟨3670595234798603120191525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894126979731470826922033 3670595234798603120191525)
                  ·
                    refine ⟨688236606524738085035911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670595234798603120191525 688236606524738085035911)
                    ·
                      rfl

theorem cell22_2010504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2010504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010504 prefixEnd_2010504 := by exact prefixLift 2010504
  have htrace : WordTrace (prefixWord ++ tailWord_2010504) baseStart_2010504 baseEnd_2010504 := by
    simpa [prefixWord, tailWord_2010504, baseEnd_2010504] using wordTrace_append hprefix tailTrace_2010504
  have hstable : (prefixWord ++ tailWord_2010504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010504).length < 2 ^ (prefixWord ++ tailWord_2010504).sum := by decide
  have hdescent : baseEnd_2010504 < baseStart_2010504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010575 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 8]
def baseStart_2010575 : Nat := 118140960795 + 2010575 * 2 ^ 59
def prefixEnd_2010575 : Nat := 4983230072969 + 3 ^ 40 * 2010575 * 2
def baseEnd_2010575 : Nat := 229420303758572522170231

theorem tailTrace_2010575 : CollatzResearch.WordTrace tailWord_2010575 prefixEnd_2010575 229420303758572522170231 := by
  unfold tailWord_2010575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73331694691037628717321179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48887796460691752478214119 73331694691037628717321179)
  ·
    refine ⟨109997542036556443075981769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73331694691037628717321179 109997542036556443075981769)
    ·
      refine ⟨82498156527417332306986327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109997542036556443075981769 82498156527417332306986327)
      ·
        refine ⟨123747234791125998460479491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82498156527417332306986327 123747234791125998460479491)
        ·
          refine ⟨185620852186688997690719237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123747234791125998460479491 185620852186688997690719237)
          ·
            refine ⟨34803909785004187067009857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185620852186688997690719237 34803909785004187067009857)
            ·
              refine ⟨26102932338753140300257393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34803909785004187067009857 26102932338753140300257393)
              ·
                refine ⟨19577199254064855225193045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26102932338753140300257393 19577199254064855225193045)
                ·
                  refine ⟨229420303758572522170231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19577199254064855225193045 229420303758572522170231)
                  ·
                    rfl

theorem cell22_2010575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_2010575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010575 prefixEnd_2010575 := by exact prefixLift 2010575
  have htrace : WordTrace (prefixWord ++ tailWord_2010575) baseStart_2010575 baseEnd_2010575 := by
    simpa [prefixWord, tailWord_2010575, baseEnd_2010575] using wordTrace_append hprefix tailTrace_2010575
  have hstable : (prefixWord ++ tailWord_2010575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010575).length < 2 ^ (prefixWord ++ tailWord_2010575).sum := by decide
  have hdescent : baseEnd_2010575 < baseStart_2010575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010628 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2010628 : Nat := 118140960795 + 2010628 * 2 ^ 59
def prefixEnd_2010628 : Nat := 4983230072969 + 3 ^ 40 * 2010628 * 2
def baseEnd_2010628 : Nat := 688279054258843094935531

theorem tailTrace_2010628 : CollatzResearch.WordTrace tailWord_2010628 prefixEnd_2010628 688279054258843094935531 := by
  unfold tailWord_2010628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36666813879922809384500269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48889085173230412512667025 36666813879922809384500269)
  ·
    refine ⟨13750055204971053519187601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36666813879922809384500269 13750055204971053519187601)
    ·
      refine ⟨10312541403728290139390701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13750055204971053519187601 10312541403728290139390701)
      ·
        refine ⟨3867203026398108802271513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10312541403728290139390701 3867203026398108802271513)
        ·
          refine ⟨2900402269798581601703635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867203026398108802271513 2900402269798581601703635)
          ·
            refine ⟨4350603404697872402555453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900402269798581601703635 4350603404697872402555453)
            ·
              refine ⟨1631476276761702150958295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350603404697872402555453 1631476276761702150958295)
              ·
                refine ⟨2447214415142553226437443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631476276761702150958295 2447214415142553226437443)
                ·
                  refine ⟨3670821622713829839656165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447214415142553226437443 3670821622713829839656165)
                  ·
                    refine ⟨688279054258843094935531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3670821622713829839656165 688279054258843094935531)
                    ·
                      rfl

theorem cell22_2010628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2010628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010628 prefixEnd_2010628 := by exact prefixLift 2010628
  have htrace : WordTrace (prefixWord ++ tailWord_2010628) baseStart_2010628 baseEnd_2010628 := by
    simpa [prefixWord, tailWord_2010628, baseEnd_2010628] using wordTrace_append hprefix tailTrace_2010628
  have hstable : (prefixWord ++ tailWord_2010628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010628).length < 2 ^ (prefixWord ++ tailWord_2010628).sum := by decide
  have hdescent : baseEnd_2010628 < baseStart_2010628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010682 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_2010682 : Nat := 118140960795 + 2010682 * 2 ^ 59
def prefixEnd_2010682 : Nat := 4983230072969 + 3 ^ 40 * 2010682 * 2
def baseEnd_2010682 : Nat := 229432513187468318028455

theorem tailTrace_2010682 : CollatzResearch.WordTrace tailWord_2010682 prefixEnd_2010682 229432513187468318028455 := by
  unfold tailWord_2010682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333899325412496497866575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48890398201099990660977533 18333899325412496497866575)
  ·
    refine ⟨27500848988118744746799863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333899325412496497866575 27500848988118744746799863)
    ·
      refine ⟨41251273482178117120199795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500848988118744746799863 41251273482178117120199795)
      ·
        refine ⟨61876910223267175680299693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41251273482178117120199795 61876910223267175680299693)
        ·
          refine ⟨23203841333725190880112385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61876910223267175680299693 23203841333725190880112385)
          ·
            refine ⟨17402881000293893160084289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23203841333725190880112385 17402881000293893160084289)
            ·
              refine ⟨13052160750220419870063217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17402881000293893160084289 13052160750220419870063217)
              ·
                refine ⟨9789120562665314902547413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13052160750220419870063217 9789120562665314902547413)
                ·
                  refine ⟨229432513187468318028455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9789120562665314902547413 229432513187468318028455)
                  ·
                    rfl

theorem cell22_2010682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_2010682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010682 prefixEnd_2010682 := by exact prefixLift 2010682
  have htrace : WordTrace (prefixWord ++ tailWord_2010682) baseStart_2010682 baseEnd_2010682 := by
    simpa [prefixWord, tailWord_2010682, baseEnd_2010682] using wordTrace_append hprefix tailTrace_2010682
  have hstable : (prefixWord ++ tailWord_2010682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010682).length < 2 ^ (prefixWord ++ tailWord_2010682).sum := by decide
  have hdescent : baseEnd_2010682 < baseStart_2010682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010729 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_2010729 : Nat := 118140960795 + 2010729 * 2 ^ 59
def prefixEnd_2010729 : Nat := 4983230072969 + 3 ^ 40 * 2010729 * 2
def baseEnd_2010729 : Nat := 688313628622912498160221

theorem tailTrace_2010729 : CollatzResearch.WordTrace tailWord_2010729 prefixEnd_2010729 688313628622912498160221 := by
  unfold tailWord_2010729
  simp only [CollatzResearch.WordTrace]
  refine ⟨73337311532479713018427241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48891541021653142012284827 73337311532479713018427241)
  ·
    refine ⟨55002983649359784763820431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73337311532479713018427241 55002983649359784763820431)
    ·
      refine ⟨82504475474039677145730647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55002983649359784763820431 82504475474039677145730647)
      ·
        refine ⟨123756713211059515718595971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82504475474039677145730647 123756713211059515718595971)
        ·
          refine ⟨185635069816589273577893957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123756713211059515718595971 185635069816589273577893957)
          ·
            refine ⟨34806575590610488795855117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185635069816589273577893957 34806575590610488795855117)
            ·
              refine ⟨13052465846478933298445669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34806575590610488795855117 13052465846478933298445669)
              ·
                refine ⟨2447337346214799993458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13052465846478933298445669 2447337346214799993458563)
                ·
                  refine ⟨3671006019322199990187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447337346214799993458563 3671006019322199990187845)
                  ·
                    refine ⟨688313628622912498160221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671006019322199990187845 688313628622912498160221)
                    ·
                      rfl

theorem cell22_2010729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_2010729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010729 prefixEnd_2010729 := by exact prefixLift 2010729
  have htrace : WordTrace (prefixWord ++ tailWord_2010729) baseStart_2010729 baseEnd_2010729 := by
    simpa [prefixWord, tailWord_2010729, baseEnd_2010729] using wordTrace_append hprefix tailTrace_2010729
  have hstable : (prefixWord ++ tailWord_2010729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010729).length < 2 ^ (prefixWord ++ tailWord_2010729).sum := by decide
  have hdescent : baseEnd_2010729 < baseStart_2010729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010780 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2010780 : Nat := 118140960795 + 2010780 * 2 ^ 59
def prefixEnd_2010780 : Nat := 4983230072969 + 3 ^ 40 * 2010780 * 2
def baseEnd_2010780 : Nat := 688331086965165365135065

theorem tailTrace_2010780 : CollatzResearch.WordTrace tailWord_2010780 prefixEnd_2010780 688331086965165365135065 := by
  unfold tailWord_2010780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669585827647474364266897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48892781103529965819022529 36669585827647474364266897)
  ·
    refine ⟨27502189370735605773200173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36669585827647474364266897 27502189370735605773200173)
    ·
      refine ⟨10313321014025852164950065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27502189370735605773200173 10313321014025852164950065)
      ·
        refine ⟨7734990760519389123712549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10313321014025852164950065 7734990760519389123712549)
        ·
          refine ⟨1450310767597385460696103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7734990760519389123712549 1450310767597385460696103)
          ·
            refine ⟨2175466151396078191044155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450310767597385460696103 2175466151396078191044155)
            ·
              refine ⟨3263199227094117286566233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175466151396078191044155 3263199227094117286566233)
              ·
                refine ⟨2447399420320587964924675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263199227094117286566233 2447399420320587964924675)
                ·
                  refine ⟨3671099130480881947387013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447399420320587964924675 3671099130480881947387013)
                  ·
                    refine ⟨688331086965165365135065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671099130480881947387013 688331086965165365135065)
                    ·
                      rfl

theorem cell22_2010780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2010780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010780 prefixEnd_2010780 := by exact prefixLift 2010780
  have htrace : WordTrace (prefixWord ++ tailWord_2010780) baseStart_2010780 baseEnd_2010780 := by
    simpa [prefixWord, tailWord_2010780, baseEnd_2010780] using wordTrace_append hprefix tailTrace_2010780
  have hstable : (prefixWord ++ tailWord_2010780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010780).length < 2 ^ (prefixWord ++ tailWord_2010780).sum := by decide
  have hdescent : baseEnd_2010780 < baseStart_2010780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010806 : List Nat := [5, 1, 3, 1, 1, 11]
def baseStart_2010806 : Nat := 118140960795 + 2010806 * 2 ^ 59
def prefixEnd_2010806 : Nat := 4983230072969 + 3 ^ 40 * 2010806 * 2
def baseEnd_2010806 : Nat := 8498024534524814370185

theorem tailTrace_2010806 : CollatzResearch.WordTrace tailWord_2010806 prefixEnd_2010806 8498024534524814370185 := by
  unfold tailWord_2010806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583757497075047198061267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48893413302133836779320181 4583757497075047198061267)
  ·
    refine ⟨6875636245612570797091901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583757497075047198061267 6875636245612570797091901)
    ·
      refine ⟨2578363592104714048909463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6875636245612570797091901 2578363592104714048909463)
      ·
        refine ⟨3867545388157071073364195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578363592104714048909463 3867545388157071073364195)
        ·
          refine ⟨5801318082235606610046293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867545388157071073364195 5801318082235606610046293)
          ·
            refine ⟨8498024534524814370185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5801318082235606610046293 8498024534524814370185)
            ·
              rfl

theorem cell22_2010806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 11].length) (baseStart_2010806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010806 prefixEnd_2010806 := by exact prefixLift 2010806
  have htrace : WordTrace (prefixWord ++ tailWord_2010806) baseStart_2010806 baseEnd_2010806 := by
    simpa [prefixWord, tailWord_2010806, baseEnd_2010806] using wordTrace_append hprefix tailTrace_2010806
  have hstable : (prefixWord ++ tailWord_2010806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010806).length < 2 ^ (prefixWord ++ tailWord_2010806).sum := by decide
  have hdescent : baseEnd_2010806 < baseStart_2010806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_2010864 : Nat := 118140960795 + 2010864 * 2 ^ 59
def prefixEnd_2010864 : Nat := 4983230072969 + 3 ^ 40 * 2010864 * 2
def baseEnd_2010864 : Nat := 688359841881817146034807

theorem tailTrace_2010864 : CollatzResearch.WordTrace tailWord_2010864 prefixEnd_2010864 688359841881817146034807 := by
  unfold tailWord_2010864
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671117693495315537295823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48894823591327087383061097 36671117693495315537295823)
  ·
    refine ⟨55006676540242973305943735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36671117693495315537295823 55006676540242973305943735)
    ·
      refine ⟨82510014810364459958915603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55006676540242973305943735 82510014810364459958915603)
      ·
        refine ⟨123765022215546689938373405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82510014810364459958915603 123765022215546689938373405)
        ·
          refine ⟨46411883330830008726890027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123765022215546689938373405 46411883330830008726890027)
          ·
            refine ⟨69617824996245013090335041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46411883330830008726890027 69617824996245013090335041)
            ·
              refine ⟨52213368747183759817751281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69617824996245013090335041 52213368747183759817751281)
              ·
                refine ⟨39160026560387819863313461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52213368747183759817751281 39160026560387819863313461)
                ·
                  refine ⟨3671252490036358112185637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39160026560387819863313461 3671252490036358112185637)
                  ·
                    refine ⟨688359841881817146034807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3671252490036358112185637 688359841881817146034807)
                    ·
                      rfl

theorem cell22_2010864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_2010864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010864 prefixEnd_2010864 := by exact prefixLift 2010864
  have htrace : WordTrace (prefixWord ++ tailWord_2010864) baseStart_2010864 baseEnd_2010864 := by
    simpa [prefixWord, tailWord_2010864, baseEnd_2010864] using wordTrace_append hprefix tailTrace_2010864
  have hstable : (prefixWord ++ tailWord_2010864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010864).length < 2 ^ (prefixWord ++ tailWord_2010864).sum := by decide
  have hdescent : baseEnd_2010864 < baseStart_2010864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010879 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 6]
def baseStart_2010879 : Nat := 118140960795 + 2010879 * 2 ^ 59
def prefixEnd_2010879 : Nat := 4983230072969 + 3 ^ 40 * 2010879 * 2
def baseEnd_2010879 : Nat := 229454992229454035636587

theorem tailTrace_2010879 : CollatzResearch.WordTrace tailWord_2010879 prefixEnd_2010879 229454992229454035636587 := by
  unfold tailWord_2010879
  simp only [CollatzResearch.WordTrace]
  refine ⟨73342782481936288636387691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48895188321290859090925127 73342782481936288636387691)
  ·
    refine ⟨110014173722904432954581537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73342782481936288636387691 110014173722904432954581537)
    ·
      refine ⟨82510630292178324715936153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110014173722904432954581537 82510630292178324715936153)
      ·
        refine ⟨61882972719133743536952115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82510630292178324715936153 61882972719133743536952115)
        ·
          refine ⟨92824459078700615305428173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61882972719133743536952115 92824459078700615305428173)
          ·
            refine ⟨34809172154512730739535565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92824459078700615305428173 34809172154512730739535565)
            ·
              refine ⟨13053439557942274027325837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34809172154512730739535565 13053439557942274027325837)
              ·
                refine ⟨4895039834228352760247189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13053439557942274027325837 4895039834228352760247189)
                ·
                  refine ⟨229454992229454035636587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4895039834228352760247189 229454992229454035636587)
                  ·
                    rfl

theorem cell22_2010879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_2010879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010879 prefixEnd_2010879 := by exact prefixLift 2010879
  have htrace : WordTrace (prefixWord ++ tailWord_2010879) baseStart_2010879 baseEnd_2010879 := by
    simpa [prefixWord, tailWord_2010879, baseEnd_2010879] using wordTrace_append hprefix tailTrace_2010879
  have hstable : (prefixWord ++ tailWord_2010879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010879).length < 2 ^ (prefixWord ++ tailWord_2010879).sum := by decide
  have hdescent : baseEnd_2010879 < baseStart_2010879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010911 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 6, 3]
def baseStart_2010911 : Nat := 118140960795 + 2010911 * 2 ^ 59
def prefixEnd_2010911 : Nat := 4983230072969 + 3 ^ 40 * 2010911 * 2
def baseEnd_2010911 : Nat := 688375930942324690109663

theorem tailTrace_2010911 : CollatzResearch.WordTrace tailWord_2010911 prefixEnd_2010911 688375930942324690109663 := by
  unfold tailWord_2010911
  simp only [CollatzResearch.WordTrace]
  refine ⟨73343949617820358101552587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48895966411880238734368391 73343949617820358101552587)
  ·
    refine ⟨110015924426730537152328881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73343949617820358101552587 110015924426730537152328881)
    ·
      refine ⟨82511943320047902864246661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110015924426730537152328881 82511943320047902864246661)
      ·
        refine ⟨15470989372508981787046249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82511943320047902864246661 15470989372508981787046249)
        ·
          refine ⟨11603242029381736340284687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15470989372508981787046249 11603242029381736340284687)
          ·
            refine ⟨17404863044072604510427031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603242029381736340284687 17404863044072604510427031)
            ·
              refine ⟨26107294566108906765640547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17404863044072604510427031 26107294566108906765640547)
              ·
                refine ⟨39160941849163360148460821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26107294566108906765640547 39160941849163360148460821)
                ·
                  refine ⟨1835669149179532506959101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39160941849163360148460821 1835669149179532506959101)
                  ·
                    refine ⟨688375930942324690109663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835669149179532506959101 688375930942324690109663)
                    ·
                      rfl

theorem cell22_2010911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_2010911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010911 prefixEnd_2010911 := by exact prefixLift 2010911
  have htrace : WordTrace (prefixWord ++ tailWord_2010911) baseStart_2010911 baseEnd_2010911 := by
    simpa [prefixWord, tailWord_2010911, baseEnd_2010911] using wordTrace_append hprefix tailTrace_2010911
  have hstable : (prefixWord ++ tailWord_2010911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010911).length < 2 ^ (prefixWord ++ tailWord_2010911).sum := by decide
  have hdescent : baseEnd_2010911 < baseStart_2010911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010913 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 4]
def baseStart_2010913 : Nat := 118140960795 + 2010913 * 2 ^ 59
def prefixEnd_2010913 : Nat := 4983230072969 + 3 ^ 40 * 2010913 * 2
def baseEnd_2010913 : Nat := 229458871861065783853219

theorem tailTrace_2010913 : CollatzResearch.WordTrace tailWord_2010913 prefixEnd_2010913 229458871861065783853219 := by
  unfold tailWord_2010913
  simp only [CollatzResearch.WordTrace]
  refine ⟨73344022563813112443125393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48896015042542074962083595 73344022563813112443125393)
  ·
    refine ⟨55008016922859834332344045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73344022563813112443125393 55008016922859834332344045)
    ·
      refine ⟨20628006346072437874629017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55008016922859834332344045 20628006346072437874629017)
      ·
        refine ⟨15471004759554328405971763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20628006346072437874629017 15471004759554328405971763)
        ·
          refine ⟨23206507139331492608957645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471004759554328405971763 23206507139331492608957645)
          ·
            refine ⟨8702440177249309728359117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23206507139331492608957645 8702440177249309728359117)
            ·
              refine ⟨3263415066468491148134669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8702440177249309728359117 3263415066468491148134669)
              ·
                refine ⟨1223780649925684180550501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263415066468491148134669 1223780649925684180550501)
                ·
                  refine ⟨229458871861065783853219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223780649925684180550501 229458871861065783853219)
                  ·
                    rfl

theorem cell22_2010913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_2010913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010913 prefixEnd_2010913 := by exact prefixLift 2010913
  have htrace : WordTrace (prefixWord ++ tailWord_2010913) baseStart_2010913 baseEnd_2010913 := by
    simpa [prefixWord, tailWord_2010913, baseEnd_2010913] using wordTrace_append hprefix tailTrace_2010913
  have hstable : (prefixWord ++ tailWord_2010913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010913).length < 2 ^ (prefixWord ++ tailWord_2010913).sum := by decide
  have hdescent : baseEnd_2010913 < baseStart_2010913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010924 : List Nat := [2, 2, 1, 1, 1, 5, 10]
def baseStart_2010924 : Nat := 118140960795 + 2010924 * 2 ^ 59
def prefixEnd_2010924 : Nat := 4983230072969 + 3 ^ 40 * 2010924 * 2
def baseEnd_2010924 : Nat := 25495569670666555167949

theorem tailTrace_2010924 : CollatzResearch.WordTrace tailWord_2010924 prefixEnd_2010924 25495569670666555167949 := by
  unfold tailWord_2010924
  simp only [CollatzResearch.WordTrace]
  refine ⟨36672211883386630660887913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48896282511182174214517217 36672211883386630660887913)
  ·
    refine ⟨27504158912539972995665935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36672211883386630660887913 27504158912539972995665935)
    ·
      refine ⟨41256238368809959493498903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27504158912539972995665935 41256238368809959493498903)
      ·
        refine ⟨61884357553214939240248355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41256238368809959493498903 61884357553214939240248355)
        ·
          refine ⟨92826536329822408860372533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61884357553214939240248355 92826536329822408860372533)
          ·
            refine ⟨8702487780920850830659925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92826536329822408860372533 8702487780920850830659925)
            ·
              refine ⟨25495569670666555167949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8702487780920850830659925 25495569670666555167949)
              ·
                rfl

theorem cell22_2010924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 10].length) (baseStart_2010924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010924 prefixEnd_2010924 := by exact prefixLift 2010924
  have htrace : WordTrace (prefixWord ++ tailWord_2010924) baseStart_2010924 baseEnd_2010924 := by
    simpa [prefixWord, tailWord_2010924, baseEnd_2010924] using wordTrace_append hprefix tailTrace_2010924
  have hstable : (prefixWord ++ tailWord_2010924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010924).length < 2 ^ (prefixWord ++ tailWord_2010924).sum := by decide
  have hdescent : baseEnd_2010924 < baseStart_2010924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010930 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2010930 : Nat := 118140960795 + 2010930 * 2 ^ 59
def prefixEnd_2010930 : Nat := 4983230072969 + 3 ^ 40 * 2010930 * 2
def baseEnd_2010930 : Nat := 229460811676871657961535

theorem tailTrace_2010930 : CollatzResearch.WordTrace tailWord_2010930 prefixEnd_2010930 229460811676871657961535 := by
  unfold tailWord_2010930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336160651187881086623561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48896428403167682897662829 18336160651187881086623561)
  ·
    refine ⟨13752120488390910814967671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18336160651187881086623561 13752120488390910814967671)
    ·
      refine ⟨20628180732586366222451507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752120488390910814967671 20628180732586366222451507)
      ·
        refine ⟨30942271098879549333677261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628180732586366222451507 30942271098879549333677261)
        ·
          refine ⟨11603351662079831000128973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30942271098879549333677261 11603351662079831000128973)
          ·
            refine ⟨4351256873279936625048365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11603351662079831000128973 4351256873279936625048365)
            ·
              refine ⟨1631721327479976234393137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4351256873279936625048365 1631721327479976234393137)
              ·
                refine ⟨1223790995609982175794853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631721327479976234393137 1223790995609982175794853)
                ·
                  refine ⟨229460811676871657961535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223790995609982175794853 229460811676871657961535)
                  ·
                    rfl

theorem cell22_2010930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2010930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010930 prefixEnd_2010930 := by exact prefixLift 2010930
  have htrace : WordTrace (prefixWord ++ tailWord_2010930) baseStart_2010930 baseEnd_2010930 := by
    simpa [prefixWord, tailWord_2010930, baseEnd_2010930] using wordTrace_append hprefix tailTrace_2010930
  have hstable : (prefixWord ++ tailWord_2010930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010930).length < 2 ^ (prefixWord ++ tailWord_2010930).sum := by decide
  have hdescent : baseEnd_2010930 < baseStart_2010930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010941 : List Nat := [1, 4, 1, 4, 1, 1, 1, 9]
def baseStart_2010941 : Nat := 118140960795 + 2010941 * 2 ^ 59
def prefixEnd_2010941 : Nat := 4983230072969 + 3 ^ 40 * 2010941 * 2
def baseEnd_2010941 : Nat := 76487355617268290206619

theorem tailTrace_2010941 : CollatzResearch.WordTrace tailWord_2010941 prefixEnd_2010941 76487355617268290206619 := by
  unfold tailWord_2010941
  simp only [CollatzResearch.WordTrace]
  refine ⟨73345043807711673225144677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48896695871807782150096451 73345043807711673225144677)
  ·
    refine ⟨13752195713945938729714627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73345043807711673225144677 13752195713945938729714627)
    ·
      refine ⟨20628293570918908094571941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752195713945938729714627 20628293570918908094571941)
      ·
        refine ⟨3867805044547295267732239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20628293570918908094571941 3867805044547295267732239)
        ·
          refine ⟨5801707566820942901598359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867805044547295267732239 5801707566820942901598359)
          ·
            refine ⟨8702561350231414352397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801707566820942901598359 8702561350231414352397539)
            ·
              refine ⟨13053842025347121528596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702561350231414352397539 13053842025347121528596309)
              ·
                refine ⟨76487355617268290206619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13053842025347121528596309 76487355617268290206619)
                ·
                  rfl

theorem cell22_2010941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 9].length) (baseStart_2010941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2010941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2010941 prefixEnd_2010941 := by exact prefixLift 2010941
  have htrace : WordTrace (prefixWord ++ tailWord_2010941) baseStart_2010941 baseEnd_2010941 := by
    simpa [prefixWord, tailWord_2010941, baseEnd_2010941] using wordTrace_append hprefix tailTrace_2010941
  have hstable : (prefixWord ++ tailWord_2010941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010941).length < 2 ^ (prefixWord ++ tailWord_2010941).sum := by decide
  have hdescent : baseEnd_2010941 < baseStart_2010941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011001 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_2011001 : Nat := 118140960795 + 2011001 * 2 ^ 59
def prefixEnd_2011001 : Nat := 4983230072969 + 3 ^ 40 * 2011001 * 2
def baseEnd_2011001 : Nat := 688406739781594455359387

theorem tailTrace_2011001 : CollatzResearch.WordTrace tailWord_2011001 prefixEnd_2011001 688406739781594455359387 := by
  unfold tailWord_2011001
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347232187494303472328857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898154791662868981552571 73347232187494303472328857)
  ·
    refine ⟨55010424140620727604246643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73347232187494303472328857 55010424140620727604246643)
    ·
      refine ⟨82515636210931091406369965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55010424140620727604246643 82515636210931091406369965)
      ·
        refine ⟨30943363579099159277388737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82515636210931091406369965 30943363579099159277388737)
        ·
          refine ⟨23207522684324369458041553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30943363579099159277388737 23207522684324369458041553)
          ·
            refine ⟨17405642013243277093531165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23207522684324369458041553 17405642013243277093531165)
            ·
              refine ⟨6527115754966228910074187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17405642013243277093531165 6527115754966228910074187)
              ·
                refine ⟨9790673632449343365111281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527115754966228910074187 9790673632449343365111281)
                ·
                  refine ⟨7343005224337007523833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9790673632449343365111281 7343005224337007523833461)
                  ·
                    refine ⟨688406739781594455359387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7343005224337007523833461 688406739781594455359387)
                    ·
                      rfl

theorem cell22_2011001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_2011001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011001 prefixEnd_2011001 := by exact prefixLift 2011001
  have htrace : WordTrace (prefixWord ++ tailWord_2011001) baseStart_2011001 baseEnd_2011001 := by
    simpa [prefixWord, tailWord_2011001, baseEnd_2011001] using wordTrace_append hprefix tailTrace_2011001
  have hstable : (prefixWord ++ tailWord_2011001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011001).length < 2 ^ (prefixWord ++ tailWord_2011001).sum := by decide
  have hdescent : baseEnd_2011001 < baseStart_2011001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011093 : List Nat := [1, 3, 2, 3, 2, 3, 8]
def baseStart_2011093 : Nat := 118140960795 + 2011093 * 2 ^ 59
def prefixEnd_2011093 : Nat := 4983230072969 + 3 ^ 40 * 2011093 * 2
def baseEnd_2011093 : Nat := 25497712343027291928115

theorem tailTrace_2011093 : CollatzResearch.WordTrace tailWord_2011093 prefixEnd_2011093 25497712343027291928115 := by
  unfold tailWord_2011093
  simp only [CollatzResearch.WordTrace]
  refine ⟨73350587703161003184677933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48900391802107335456451955 73350587703161003184677933)
  ·
    refine ⟨27506470388685376194254225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73350587703161003184677933 27506470388685376194254225)
    ·
      refine ⟨20629852791514032145690669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27506470388685376194254225 20629852791514032145690669)
      ·
        refine ⟨7736194796817762054634001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20629852791514032145690669 7736194796817762054634001)
        ·
          refine ⟨5802146097613321540975501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7736194796817762054634001 5802146097613321540975501)
          ·
            refine ⟨2175804786604995577865813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5802146097613321540975501 2175804786604995577865813)
            ·
              refine ⟨25497712343027291928115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2175804786604995577865813 25497712343027291928115)
              ·
                rfl

theorem cell22_2011093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 8].length) (baseStart_2011093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011093 prefixEnd_2011093 := by exact prefixLift 2011093
  have htrace : WordTrace (prefixWord ++ tailWord_2011093) baseStart_2011093 baseEnd_2011093 := by
    simpa [prefixWord, tailWord_2011093, baseEnd_2011093] using wordTrace_append hprefix tailTrace_2011093
  have hstable : (prefixWord ++ tailWord_2011093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011093).length < 2 ^ (prefixWord ++ tailWord_2011093).sum := by decide
  have hdescent : baseEnd_2011093 < baseStart_2011093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_2011136 : Nat := 118140960795 + 2011136 * 2 ^ 59
def prefixEnd_2011136 : Nat := 4983230072969 + 3 ^ 40 * 2011136 * 2
def baseEnd_2011136 : Nat := 688452953040499103233973

theorem tailTrace_2011136 : CollatzResearch.WordTrace tailWord_2011136 prefixEnd_2011136 688452953040499103233973 := by
  unfold tailWord_2011136
  simp only [CollatzResearch.WordTrace]
  refine ⟨36676078021002610764246631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48901437361336814352328841 36676078021002610764246631)
  ·
    refine ⟨55014117031503916146369947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36676078021002610764246631 55014117031503916146369947)
    ·
      refine ⟨82521175547255874219554921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55014117031503916146369947 82521175547255874219554921)
      ·
        refine ⟨61890881660441905664666191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82521175547255874219554921 61890881660441905664666191)
        ·
          refine ⟨92836322490662858496999287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61890881660441905664666191 92836322490662858496999287)
          ·
            refine ⟨139254483735994287745498931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92836322490662858496999287 139254483735994287745498931)
            ·
              refine ⟨208881725603991431618248397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139254483735994287745498931 208881725603991431618248397)
              ·
                refine ⟨78330647101496786856843149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208881725603991431618248397 78330647101496786856843149)
                ·
                  refine ⟨29373992663061295071316181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78330647101496786856843149 29373992663061295071316181)
                  ·
                    refine ⟨688452953040499103233973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29373992663061295071316181 688452953040499103233973)
                    ·
                      rfl

theorem cell22_2011136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_2011136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011136 prefixEnd_2011136 := by exact prefixLift 2011136
  have htrace : WordTrace (prefixWord ++ tailWord_2011136) baseStart_2011136 baseEnd_2011136 := by
    simpa [prefixWord, tailWord_2011136, baseEnd_2011136] using wordTrace_append hprefix tailTrace_2011136
  have hstable : (prefixWord ++ tailWord_2011136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011136).length < 2 ^ (prefixWord ++ tailWord_2011136).sum := by decide
  have hdescent : baseEnd_2011136 < baseStart_2011136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011159 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2011159 : Nat := 118140960795 + 2011159 * 2 ^ 59
def prefixEnd_2011159 : Nat := 4983230072969 + 3 ^ 40 * 2011159 * 2
def baseEnd_2011159 : Nat := 688460826410534709908903

theorem tailTrace_2011159 : CollatzResearch.WordTrace tailWord_2011159 prefixEnd_2011159 688460826410534709908903 := by
  unfold tailWord_2011159
  simp only [CollatzResearch.WordTrace]
  refine ⟨73352994920921896456580531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48901996613947930971053687 73352994920921896456580531)
  ·
    refine ⟨110029492381382844684870797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73352994920921896456580531 110029492381382844684870797)
    ·
      refine ⟨41261059643018566756826549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110029492381382844684870797 41261059643018566756826549)
      ·
        refine ⟨3868224341532990633452489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41261059643018566756826549 3868224341532990633452489)
        ·
          refine ⟨2901168256149742975089367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868224341532990633452489 2901168256149742975089367)
          ·
            refine ⟨4351752384224614462634051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901168256149742975089367 4351752384224614462634051)
            ·
              refine ⟨6527628576336921693951077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351752384224614462634051 6527628576336921693951077)
              ·
                refine ⟨1223930358063172817615827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6527628576336921693951077 1223930358063172817615827)
                ·
                  refine ⟨1835895537094759226423741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223930358063172817615827 1835895537094759226423741)
                  ·
                    refine ⟨688460826410534709908903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835895537094759226423741 688460826410534709908903)
                    ·
                      rfl

theorem cell22_2011159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2011159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011159 prefixEnd_2011159 := by exact prefixLift 2011159
  have htrace : WordTrace (prefixWord ++ tailWord_2011159) baseStart_2011159 baseEnd_2011159 := by
    simpa [prefixWord, tailWord_2011159, baseEnd_2011159] using wordTrace_append hprefix tailTrace_2011159
  have hstable : (prefixWord ++ tailWord_2011159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011159).length < 2 ^ (prefixWord ++ tailWord_2011159).sum := by decide
  have hdescent : baseEnd_2011159 < baseStart_2011159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011200 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_2011200 : Nat := 118140960795 + 2011200 * 2 ^ 59
def prefixEnd_2011200 : Nat := 4983230072969 + 3 ^ 40 * 2011200 * 2
def baseEnd_2011200 : Nat := 229491620516141423211259

theorem tailTrace_2011200 : CollatzResearch.WordTrace tailWord_2011200 prefixEnd_2011200 229491620516141423211259 := by
  unfold tailWord_2011200
  simp only [CollatzResearch.WordTrace]
  refine ⟨36677245156886680229411527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48902993542515573639215369 36677245156886680229411527)
  ·
    refine ⟨55015867735330020344117291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36677245156886680229411527 55015867735330020344117291)
    ·
      refine ⟨82523801602995030516175937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55015867735330020344117291 82523801602995030516175937)
      ·
        refine ⟨61892851202246272887131953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82523801602995030516175937 61892851202246272887131953)
        ·
          refine ⟨46419638401684704665348965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61892851202246272887131953 46419638401684704665348965)
          ·
            refine ⟨8703682200315882124752931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46419638401684704665348965 8703682200315882124752931)
            ·
              refine ⟨13055523300473823187129397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703682200315882124752931 13055523300473823187129397)
              ·
                refine ⟨1223955309419420923793381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13055523300473823187129397 1223955309419420923793381)
                ·
                  refine ⟨229491620516141423211259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223955309419420923793381 229491620516141423211259)
                  ·
                    rfl

theorem cell22_2011200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_2011200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011200 prefixEnd_2011200 := by exact prefixLift 2011200
  have htrace : WordTrace (prefixWord ++ tailWord_2011200) baseStart_2011200 baseEnd_2011200 := by
    simpa [prefixWord, tailWord_2011200, baseEnd_2011200] using wordTrace_append hprefix tailTrace_2011200
  have hstable : (prefixWord ++ tailWord_2011200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011200).length < 2 ^ (prefixWord ++ tailWord_2011200).sum := by decide
  have hdescent : baseEnd_2011200 < baseStart_2011200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011273 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 7]
def baseStart_2011273 : Nat := 118140960795 + 2011273 * 2 ^ 59
def prefixEnd_2011273 : Nat := 4983230072969 + 3 ^ 40 * 2011273 * 2
def baseEnd_2011273 : Nat := 229499950313425470852851

theorem tailTrace_2011273 : CollatzResearch.WordTrace tailWord_2011273 prefixEnd_2011273 229499950313425470852851 := by
  unfold tailWord_2011273
  simp only [CollatzResearch.WordTrace]
  refine ⟨73357152842508893926230473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48904768561672595950820315 73357152842508893926230473)
  ·
    refine ⟨55017864631881670444672855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73357152842508893926230473 55017864631881670444672855)
    ·
      refine ⟨82526796947822505667009283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55017864631881670444672855 82526796947822505667009283)
      ·
        refine ⟨123790195421733758500513925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82526796947822505667009283 123790195421733758500513925)
        ·
          refine ⟨23210661641575079718846361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123790195421733758500513925 23210661641575079718846361)
          ·
            refine ⟨17407996231181309789134771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23210661641575079718846361 17407996231181309789134771)
            ·
              refine ⟨26111994346771964683702157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17407996231181309789134771 26111994346771964683702157)
              ·
                refine ⟨9791997880039486756388309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26111994346771964683702157 9791997880039486756388309)
                ·
                  refine ⟨229499950313425470852851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9791997880039486756388309 229499950313425470852851)
                  ·
                    rfl

theorem cell22_2011273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_2011273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011273 prefixEnd_2011273 := by exact prefixLift 2011273
  have htrace : WordTrace (prefixWord ++ tailWord_2011273) baseStart_2011273 baseEnd_2011273 := by
    simpa [prefixWord, tailWord_2011273, baseEnd_2011273] using wordTrace_append hprefix tailTrace_2011273
  have hstable : (prefixWord ++ tailWord_2011273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011273).length < 2 ^ (prefixWord ++ tailWord_2011273).sum := by decide
  have hdescent : baseEnd_2011273 < baseStart_2011273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011367 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2011367 : Nat := 118140960795 + 2011367 * 2 ^ 59
def prefixEnd_2011367 : Nat := 4983230072969 + 3 ^ 40 * 2011367 * 2
def baseEnd_2011367 : Nat := 688532029061291500708265

theorem tailTrace_2011367 : CollatzResearch.WordTrace tailWord_2011367 prefixEnd_2011367 688532029061291500708265 := by
  unfold tailWord_2011367
  simp only [CollatzResearch.WordTrace]
  refine ⟨73360581304168347980152355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48907054202778898653434903 73360581304168347980152355)
  ·
    refine ⟨110040871956252521970228533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73360581304168347980152355 110040871956252521970228533)
    ·
      refine ⟨10316331745898673934708925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110040871956252521970228533 10316331745898673934708925)
      ·
        refine ⟨3868624404712002725515847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10316331745898673934708925 3868624404712002725515847)
        ·
          refine ⟨5802936607068004088273771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868624404712002725515847 5802936607068004088273771)
          ·
            refine ⟨8704404910602006132410657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802936607068004088273771 8704404910602006132410657)
            ·
              refine ⟨6528303682951504599307993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8704404910602006132410657 6528303682951504599307993)
              ·
                refine ⟨4896227762213628449480995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6528303682951504599307993 4896227762213628449480995)
                ·
                  refine ⟨7344341643320442674221493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896227762213628449480995 7344341643320442674221493)
                  ·
                    refine ⟨688532029061291500708265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7344341643320442674221493 688532029061291500708265)
                    ·
                      rfl

theorem cell22_2011367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2011367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011367 prefixEnd_2011367 := by exact prefixLift 2011367
  have htrace : WordTrace (prefixWord ++ tailWord_2011367) baseStart_2011367 baseEnd_2011367 := by
    simpa [prefixWord, tailWord_2011367, baseEnd_2011367] using wordTrace_append hprefix tailTrace_2011367
  have hstable : (prefixWord ++ tailWord_2011367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011367).length < 2 ^ (prefixWord ++ tailWord_2011367).sum := by decide
  have hdescent : baseEnd_2011367 < baseStart_2011367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011382 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2011382 : Nat := 118140960795 + 2011382 * 2 ^ 59
def prefixEnd_2011382 : Nat := 4983230072969 + 3 ^ 40 * 2011382 * 2
def baseEnd_2011382 : Nat := 688537163867836461583219

theorem tailTrace_2011382 : CollatzResearch.WordTrace tailWord_2011382 prefixEnd_2011382 688537163867836461583219 := by
  unfold tailWord_2011382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585070524944625346371775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48907418932742670361298933 4585070524944625346371775)
  ·
    refine ⟨6877605787416938019557663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4585070524944625346371775 6877605787416938019557663)
    ·
      refine ⟨10316408681125407029336495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877605787416938019557663 10316408681125407029336495)
      ·
        refine ⟨15474613021688110544004743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316408681125407029336495 15474613021688110544004743)
        ·
          refine ⟨23211919532532165816007115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474613021688110544004743 23211919532532165816007115)
          ·
            refine ⟨34817879298798248724010673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23211919532532165816007115 34817879298798248724010673)
            ·
              refine ⟨26113409474098686543008005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34817879298798248724010673 26113409474098686543008005)
              ·
                refine ⟨4896264276393503726814001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26113409474098686543008005 4896264276393503726814001)
                ·
                  refine ⟨3672198207295127795110501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896264276393503726814001 3672198207295127795110501)
                  ·
                    refine ⟨688537163867836461583219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672198207295127795110501 688537163867836461583219)
                    ·
                      rfl

theorem cell22_2011382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2011382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011382 prefixEnd_2011382 := by exact prefixLift 2011382
  have htrace : WordTrace (prefixWord ++ tailWord_2011382) baseStart_2011382 baseEnd_2011382 := by
    simpa [prefixWord, tailWord_2011382, baseEnd_2011382] using wordTrace_append hprefix tailTrace_2011382
  have hstable : (prefixWord ++ tailWord_2011382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011382).length < 2 ^ (prefixWord ++ tailWord_2011382).sum := by decide
  have hdescent : baseEnd_2011382 < baseStart_2011382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011425 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 7]
def baseStart_2011425 : Nat := 118140960795 + 2011425 * 2 ^ 59
def prefixEnd_2011425 : Nat := 4983230072969 + 3 ^ 40 * 2011425 * 2
def baseEnd_2011425 : Nat := 229517294548866227586029

theorem tailTrace_2011425 : CollatzResearch.WordTrace tailWord_2011425 prefixEnd_2011425 229517294548866227586029 := by
  unfold tailWord_2011425
  simp only [CollatzResearch.WordTrace]
  refine ⟨73362696737958223885763729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48908464491972149257175819 73362696737958223885763729)
  ·
    refine ⟨55022022553468667914322797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73362696737958223885763729 55022022553468667914322797)
    ·
      refine ⟨20633258457550750467871049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55022022553468667914322797 20633258457550750467871049)
      ·
        refine ⟨15474943843163062850903287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20633258457550750467871049 15474943843163062850903287)
        ·
          refine ⟨23212415764744594276354931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474943843163062850903287 23212415764744594276354931)
          ·
            refine ⟨34818623647116891414532397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212415764744594276354931 34818623647116891414532397)
            ·
              refine ⟨13056983867668834280449649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34818623647116891414532397 13056983867668834280449649)
              ·
                refine ⟨9792737900751625710337237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13056983867668834280449649 9792737900751625710337237)
                ·
                  refine ⟨229517294548866227586029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9792737900751625710337237 229517294548866227586029)
                  ·
                    rfl

theorem cell22_2011425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_2011425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011425 prefixEnd_2011425 := by exact prefixLift 2011425
  have htrace : WordTrace (prefixWord ++ tailWord_2011425) baseStart_2011425 baseEnd_2011425 := by
    simpa [prefixWord, tailWord_2011425, baseEnd_2011425] using wordTrace_append hprefix tailTrace_2011425
  have hstable : (prefixWord ++ tailWord_2011425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011425).length < 2 ^ (prefixWord ++ tailWord_2011425).sum := by decide
  have hdescent : baseEnd_2011425 < baseStart_2011425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011431 : List Nat := [1, 1, 8, 1, 1, 2, 8]
def baseStart_2011431 : Nat := 118140960795 + 2011431 * 2 ^ 59
def prefixEnd_2011431 : Nat := 4983230072969 + 3 ^ 40 * 2011431 * 2
def baseEnd_2011431 : Nat := 25501997687748765448447

theorem tailTrace_2011431 : CollatzResearch.WordTrace tailWord_2011431 prefixEnd_2011431 25501997687748765448447 := by
  unfold tailWord_2011431
  simp only [CollatzResearch.WordTrace]
  refine ⟨73362915575936486910482147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48908610383957657940321431 73362915575936486910482147)
  ·
    refine ⟨110044373363904730365723221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73362915575936486910482147 110044373363904730365723221)
    ·
      refine ⟨1289582500358258558973319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 110044373363904730365723221 1289582500358258558973319)
      ·
        refine ⟨1934373750537387838459979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289582500358258558973319 1934373750537387838459979)
        ·
          refine ⟨2901560625806081757689969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934373750537387838459979 2901560625806081757689969)
          ·
            refine ⟨2176170469354561318267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901560625806081757689969 2176170469354561318267477)
            ·
              refine ⟨25501997687748765448447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2176170469354561318267477 25501997687748765448447)
              ·
                rfl

theorem cell22_2011431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 8].length) (baseStart_2011431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011431 prefixEnd_2011431 := by exact prefixLift 2011431
  have htrace : WordTrace (prefixWord ++ tailWord_2011431) baseStart_2011431 baseEnd_2011431 := by
    simpa [prefixWord, tailWord_2011431, baseEnd_2011431] using wordTrace_append hprefix tailTrace_2011431
  have hstable : (prefixWord ++ tailWord_2011431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011431).length < 2 ^ (prefixWord ++ tailWord_2011431).sum := by decide
  have hdescent : baseEnd_2011431 < baseStart_2011431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011440 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_2011440 : Nat := 118140960795 + 2011440 * 2 ^ 59
def prefixEnd_2011440 : Nat := 4983230072969 + 3 ^ 40 * 2011440 * 2
def baseEnd_2011440 : Nat := 688557018453143643633041

theorem tailTrace_2011440 : CollatzResearch.WordTrace tailWord_2011440 prefixEnd_2011440 688557018453143643633041 := by
  unfold tailWord_2011440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36681621916451940723779887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48908829221935920965039849 36681621916451940723779887)
  ·
    refine ⟨55022432874677911085669831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36681621916451940723779887 55022432874677911085669831)
    ·
      refine ⟨82533649312016866628504747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55022432874677911085669831 82533649312016866628504747)
      ·
        refine ⟨123800473968025299942757121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82533649312016866628504747 123800473968025299942757121)
        ·
          refine ⟨92850355476018974957067841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123800473968025299942757121 92850355476018974957067841)
          ·
            refine ⟨69637766607014231217800881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92850355476018974957067841 69637766607014231217800881)
            ·
              refine ⟨52228324955260673413350661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69637766607014231217800881 52228324955260673413350661)
              ·
                refine ⟨9792810929111376265003249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52228324955260673413350661 9792810929111376265003249)
                ·
                  refine ⟨7344608196833532198752437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792810929111376265003249 7344608196833532198752437)
                  ·
                    refine ⟨688557018453143643633041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7344608196833532198752437 688557018453143643633041)
                    ·
                      rfl

theorem cell22_2011440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_2011440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011440 prefixEnd_2011440 := by exact prefixLift 2011440
  have htrace : WordTrace (prefixWord ++ tailWord_2011440) baseStart_2011440 baseEnd_2011440 := by
    simpa [prefixWord, tailWord_2011440, baseEnd_2011440] using wordTrace_append hprefix tailTrace_2011440
  have hstable : (prefixWord ++ tailWord_2011440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011440).length < 2 ^ (prefixWord ++ tailWord_2011440).sum := by decide
  have hdescent : baseEnd_2011440 < baseStart_2011440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011472 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_2011472 : Nat := 118140960795 + 2011472 * 2 ^ 59
def prefixEnd_2011472 : Nat := 4983230072969 + 3 ^ 40 * 2011472 * 2
def baseEnd_2011472 : Nat := 688567972707106226832943

theorem tailTrace_2011472 : CollatzResearch.WordTrace tailWord_2011472 prefixEnd_2011472 688567972707106226832943 := by
  unfold tailWord_2011472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682205484393975456362335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48909607312525300608483113 36682205484393975456362335)
  ·
    refine ⟨55023308226590963184543503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36682205484393975456362335 55023308226590963184543503)
    ·
      refine ⟨82534962339886444776815255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55023308226590963184543503 82534962339886444776815255)
      ·
        refine ⟨123802443509829667165222883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82534962339886444776815255 123802443509829667165222883)
        ·
          refine ⟨185703665264744500747834325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123802443509829667165222883 185703665264744500747834325)
          ·
            refine ⟨4352429654642449236277367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185703665264744500747834325 4352429654642449236277367)
            ·
              refine ⟨6528644481963673854416051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352429654642449236277367 6528644481963673854416051)
              ·
                refine ⟨9792966722945510781624077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528644481963673854416051 9792966722945510781624077)
                ·
                  refine ⟨3672362521104566543109029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792966722945510781624077 3672362521104566543109029)
                  ·
                    refine ⟨688567972707106226832943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672362521104566543109029 688567972707106226832943)
                    ·
                      rfl

theorem cell22_2011472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_2011472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011472 prefixEnd_2011472 := by exact prefixLift 2011472
  have htrace : WordTrace (prefixWord ++ tailWord_2011472) baseStart_2011472 baseEnd_2011472 := by
    simpa [prefixWord, tailWord_2011472, baseEnd_2011472] using wordTrace_append hprefix tailTrace_2011472
  have hstable : (prefixWord ++ tailWord_2011472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011472).length < 2 ^ (prefixWord ++ tailWord_2011472).sum := by decide
  have hdescent : baseEnd_2011472 < baseStart_2011472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011504 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_2011504 : Nat := 118140960795 + 2011504 * 2 ^ 59
def prefixEnd_2011504 : Nat := 4983230072969 + 3 ^ 40 * 2011504 * 2
def baseEnd_2011504 : Nat := 229526308987022936677615

theorem tailTrace_2011504 : CollatzResearch.WordTrace tailWord_2011504 prefixEnd_2011504 229526308987022936677615 := by
  unfold tailWord_2011504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682789052336010188944783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48910385403114680251926377 36682789052336010188944783)
  ·
    refine ⟨55024183578504015283417175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36682789052336010188944783 55024183578504015283417175)
    ·
      refine ⟨82536275367756022925125763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55024183578504015283417175 82536275367756022925125763)
      ·
        refine ⟨123804413051634034387688645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82536275367756022925125763 123804413051634034387688645)
        ·
          refine ⟨23213327447181381447691621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123804413051634034387688645 23213327447181381447691621)
          ·
            refine ⟨4352498896346509021442179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23213327447181381447691621 4352498896346509021442179)
            ·
              refine ⟨6528748344519763532163269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352498896346509021442179 6528748344519763532163269)
              ·
                refine ⟨1224140314597455662280613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6528748344519763532163269 1224140314597455662280613)
                ·
                  refine ⟨229526308987022936677615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224140314597455662280613 229526308987022936677615)
                  ·
                    rfl

theorem cell22_2011504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_2011504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011504 prefixEnd_2011504 := by exact prefixLift 2011504
  have htrace : WordTrace (prefixWord ++ tailWord_2011504) baseStart_2011504 baseEnd_2011504 := by
    simpa [prefixWord, tailWord_2011504, baseEnd_2011504] using wordTrace_append hprefix tailTrace_2011504
  have hstable : (prefixWord ++ tailWord_2011504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011504).length < 2 ^ (prefixWord ++ tailWord_2011504).sum := by decide
  have hdescent : baseEnd_2011504 < baseStart_2011504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011534 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2011534 : Nat := 118140960795 + 2011534 * 2 ^ 59
def prefixEnd_2011534 : Nat := 4983230072969 + 3 ^ 40 * 2011534 * 2
def baseEnd_2011534 : Nat := 688589196574158731782753

theorem tailTrace_2011534 : CollatzResearch.WordTrace tailWord_2011534 prefixEnd_2011534 688589196574158731782753 := by
  unfold tailWord_2011534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170834036820416937685207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48911114863042223667654437 9170834036820416937685207)
  ·
    refine ⟨13756251055230625406527811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9170834036820416937685207 13756251055230625406527811)
    ·
      refine ⟨20634376582845938109791717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756251055230625406527811 20634376582845938109791717)
      ·
        refine ⟨3868945609283613395585947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20634376582845938109791717 3868945609283613395585947)
        ·
          refine ⟨5803418413925420093378921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868945609283613395585947 5803418413925420093378921)
          ·
            refine ⟨4352563810444065070034191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5803418413925420093378921 4352563810444065070034191)
            ·
              refine ⟨6528845715666097605051287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352563810444065070034191 6528845715666097605051287)
              ·
                refine ⟨9793268573499146407576931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528845715666097605051287 9793268573499146407576931)
                ·
                  refine ⟨14689902860248719611365397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793268573499146407576931 14689902860248719611365397)
                  ·
                    refine ⟨688589196574158731782753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14689902860248719611365397 688589196574158731782753)
                    ·
                      rfl

theorem cell22_2011534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2011534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011534 prefixEnd_2011534 := by exact prefixLift 2011534
  have htrace : WordTrace (prefixWord ++ tailWord_2011534) baseStart_2011534 baseEnd_2011534 := by
    simpa [prefixWord, tailWord_2011534, baseEnd_2011534] using wordTrace_append hprefix tailTrace_2011534
  have hstable : (prefixWord ++ tailWord_2011534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011534).length < 2 ^ (prefixWord ++ tailWord_2011534).sum := by decide
  have hdescent : baseEnd_2011534 < baseStart_2011534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011540 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2011540 : Nat := 118140960795 + 2011540 * 2 ^ 59
def prefixEnd_2011540 : Nat := 4983230072969 + 3 ^ 40 * 2011540 * 2
def baseEnd_2011540 : Nat := 688591250496776716132735

theorem tailTrace_2011540 : CollatzResearch.WordTrace tailWord_2011540 prefixEnd_2011540 688591250496776716132735 := by
  unfold tailWord_2011540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683445566270799263100037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48911260755027732350800049 36683445566270799263100037)
  ·
    refine ⟨6878146043675774861831257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36683445566270799263100037 6878146043675774861831257)
    ·
      refine ⟨5158609532756831146373443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6878146043675774861831257 5158609532756831146373443)
      ·
        refine ⟨7737914299135246719560165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158609532756831146373443 7737914299135246719560165)
        ·
          refine ⟨1450858931087858759917531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7737914299135246719560165 1450858931087858759917531)
          ·
            refine ⟨2176288396631788139876297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450858931087858759917531 2176288396631788139876297)
            ·
              refine ⟨1632216297473841104907223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176288396631788139876297 1632216297473841104907223)
              ·
                refine ⟨2448324446210761657360835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632216297473841104907223 2448324446210761657360835)
                ·
                  refine ⟨3672486669316142486041253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448324446210761657360835 3672486669316142486041253)
                  ·
                    refine ⟨688591250496776716132735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672486669316142486041253 688591250496776716132735)
                    ·
                      rfl

theorem cell22_2011540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2011540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011540 prefixEnd_2011540 := by exact prefixLift 2011540
  have htrace : WordTrace (prefixWord ++ tailWord_2011540) baseStart_2011540 baseEnd_2011540 := by
    simpa [prefixWord, tailWord_2011540, baseEnd_2011540] using wordTrace_append hprefix tailTrace_2011540
  have hstable : (prefixWord ++ tailWord_2011540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011540).length < 2 ^ (prefixWord ++ tailWord_2011540).sum := by decide
  have hdescent : baseEnd_2011540 < baseStart_2011540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2011607 : Nat := 118140960795 + 2011607 * 2 ^ 59
def prefixEnd_2011607 : Nat := 4983230072969 + 3 ^ 40 * 2011607 * 2
def baseEnd_2011607 : Nat := 688614185966010874707529

theorem tailTrace_2011607 : CollatzResearch.WordTrace tailWord_2011607 prefixEnd_2011607 688614185966010874707529 := by
  unfold tailWord_2011607
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369334823298868968889075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48912889882199245979259383 73369334823298868968889075)
  ·
    refine ⟨110054002234948303453333613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73369334823298868968889075 110054002234948303453333613)
    ·
      refine ⟨41270250838105613795000105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110054002234948303453333613 41270250838105613795000105)
      ·
        refine ⟨30952688128579210346250079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41270250838105613795000105 30952688128579210346250079)
        ·
          refine ⟨46429032192868815519375119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30952688128579210346250079 46429032192868815519375119)
          ·
            refine ⟨69643548289303223279062679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46429032192868815519375119 69643548289303223279062679)
            ·
              refine ⟨104465322433954834918594019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69643548289303223279062679 104465322433954834918594019)
              ·
                refine ⟨156697983650932252377891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104465322433954834918594019 156697983650932252377891029)
                ·
                  refine ⟨3672608991818724665106821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 156697983650932252377891029 3672608991818724665106821)
                  ·
                    refine ⟨688614185966010874707529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672608991818724665106821 688614185966010874707529)
                    ·
                      rfl

theorem cell22_2011607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2011607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011607 prefixEnd_2011607 := by exact prefixLift 2011607
  have htrace : WordTrace (prefixWord ++ tailWord_2011607) baseStart_2011607 baseEnd_2011607 := by
    simpa [prefixWord, tailWord_2011607, baseEnd_2011607] using wordTrace_append hprefix tailTrace_2011607
  have hstable : (prefixWord ++ tailWord_2011607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011607).length < 2 ^ (prefixWord ++ tailWord_2011607).sum := by decide
  have hdescent : baseEnd_2011607 < baseStart_2011607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011669 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2011669 : Nat := 118140960795 + 2011669 * 2 ^ 59
def prefixEnd_2011669 : Nat := 4983230072969 + 3 ^ 40 * 2011669 * 2
def baseEnd_2011669 : Nat := 688635409833063379657339

theorem tailTrace_2011669 : CollatzResearch.WordTrace tailWord_2011669 prefixEnd_2011669 688635409833063379657339 := by
  unfold tailWord_2011669
  simp only [CollatzResearch.WordTrace]
  refine ⟨73371596149074253557646061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48914397432716169038430707 73371596149074253557646061)
  ·
    refine ⟨27514348555902845084117273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73371596149074253557646061 27514348555902845084117273)
    ·
      refine ⟨20635761416927133813087955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27514348555902845084117273 20635761416927133813087955)
      ·
        refine ⟨30953642125390700719631933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20635761416927133813087955 30953642125390700719631933)
        ·
          refine ⟨11607615797021512769861975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30953642125390700719631933 11607615797021512769861975)
          ·
            refine ⟨17411423695532269154792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11607615797021512769861975 17411423695532269154792963)
            ·
              refine ⟨26117135543298403732189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17411423695532269154792963 26117135543298403732189445)
              ·
                refine ⟨4896962914368450699785521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26117135543298403732189445 4896962914368450699785521)
                ·
                  refine ⟨3672722185776338024839141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4896962914368450699785521 3672722185776338024839141)
                  ·
                    refine ⟨688635409833063379657339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672722185776338024839141 688635409833063379657339)
                    ·
                      rfl

theorem cell22_2011669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2011669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011669 prefixEnd_2011669 := by exact prefixLift 2011669
  have htrace : WordTrace (prefixWord ++ tailWord_2011669) baseStart_2011669 baseEnd_2011669 := by
    simpa [prefixWord, tailWord_2011669, baseEnd_2011669] using wordTrace_append hprefix tailTrace_2011669
  have hstable : (prefixWord ++ tailWord_2011669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011669).length < 2 ^ (prefixWord ++ tailWord_2011669).sum := by decide
  have hdescent : baseEnd_2011669 < baseStart_2011669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011688 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2011688 : Nat := 118140960795 + 2011688 * 2 ^ 59
def prefixEnd_2011688 : Nat := 4983230072969 + 3 ^ 40 * 2011688 * 2
def baseEnd_2011688 : Nat := 688641913921353663432281

theorem tailTrace_2011688 : CollatzResearch.WordTrace tailWord_2011688 prefixEnd_2011688 688641913921353663432281 := by
  unfold tailWord_2011688
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686144568002709901293859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48914859424003613201725145 36686144568002709901293859)
  ·
    refine ⟨55029216852004064851940789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36686144568002709901293859 55029216852004064851940789)
    ·
      refine ⟨5158989079875381079869449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55029216852004064851940789 5158989079875381079869449)
      ·
        refine ⟨3869241809906535809902087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5158989079875381079869449 3869241809906535809902087)
        ·
          refine ⟨5803862714859803714853131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869241809906535809902087 5803862714859803714853131)
          ·
            refine ⟨8705794072289705572279697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803862714859803714853131 8705794072289705572279697)
            ·
              refine ⟨6529345554217279179209773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705794072289705572279697 6529345554217279179209773)
              ·
                refine ⟨2448504582831479692203665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6529345554217279179209773 2448504582831479692203665)
                ·
                  refine ⟨1836378437123609769152749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2448504582831479692203665 1836378437123609769152749)
                  ·
                    refine ⟨688641913921353663432281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836378437123609769152749 688641913921353663432281)
                    ·
                      rfl

theorem cell22_2011688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2011688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011688 prefixEnd_2011688 := by exact prefixLift 2011688
  have htrace : WordTrace (prefixWord ++ tailWord_2011688) baseStart_2011688 baseEnd_2011688 := by
    simpa [prefixWord, tailWord_2011688, baseEnd_2011688] using wordTrace_append hprefix tailTrace_2011688
  have hstable : (prefixWord ++ tailWord_2011688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011688).length < 2 ^ (prefixWord ++ tailWord_2011688).sum := by decide
  have hdescent : baseEnd_2011688 < baseStart_2011688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011729 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 7]
def baseStart_2011729 : Nat := 118140960795 + 2011729 * 2 ^ 59
def prefixEnd_2011729 : Nat := 4983230072969 + 3 ^ 40 * 2011729 * 2
def baseEnd_2011729 : Nat := 229551983019747741052385

theorem tailTrace_2011729 : CollatzResearch.WordTrace tailWord_2011729 prefixEnd_2011729 229551983019747741052385 := by
  unfold tailWord_2011729
  simp only [CollatzResearch.WordTrace]
  refine ⟨73373784528856883804830241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48915856352571255869886827 73373784528856883804830241)
  ·
    refine ⟨55030338396642662853622681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73373784528856883804830241 55030338396642662853622681)
    ·
      refine ⟨41272753797481997140217011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55030338396642662853622681 41272753797481997140217011)
      ·
        refine ⟨61909130696222995710325517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41272753797481997140217011 61909130696222995710325517)
        ·
          refine ⟨23215924011083623391372069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61909130696222995710325517 23215924011083623391372069)
          ·
            refine ⟨4352985752078179385882263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23215924011083623391372069 4352985752078179385882263)
            ·
              refine ⟨6529478628117269078823395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352985752078179385882263 6529478628117269078823395)
              ·
                refine ⟨9794217942175903618235093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529478628117269078823395 9794217942175903618235093)
                ·
                  refine ⟨229551983019747741052385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9794217942175903618235093 229551983019747741052385)
                  ·
                    rfl

theorem cell22_2011729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_2011729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011729 prefixEnd_2011729 := by exact prefixLift 2011729
  have htrace : WordTrace (prefixWord ++ tailWord_2011729) baseStart_2011729 baseEnd_2011729 := by
    simpa [prefixWord, tailWord_2011729, baseEnd_2011729] using wordTrace_append hprefix tailTrace_2011729
  have hstable : (prefixWord ++ tailWord_2011729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011729).length < 2 ^ (prefixWord ++ tailWord_2011729).sum := by decide
  have hdescent : baseEnd_2011729 < baseStart_2011729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011733 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_2011733 : Nat := 118140960795 + 2011733 * 2 ^ 59
def prefixEnd_2011733 : Nat := 4983230072969 + 3 ^ 40 * 2011733 * 2
def baseEnd_2011733 : Nat := 688657318340988546057143

theorem tailTrace_2011733 : CollatzResearch.WordTrace tailWord_2011733 prefixEnd_2011733 688657318340988546057143 := by
  unfold tailWord_2011733
  simp only [CollatzResearch.WordTrace]
  refine ⟨73373930420842392487975853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48915953613894928325317235 73373930420842392487975853)
  ·
    refine ⟨27515223907815897182990945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73373930420842392487975853 27515223907815897182990945)
    ·
      refine ⟨20636417930861922887243209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27515223907815897182990945 20636417930861922887243209)
      ·
        refine ⟨15477313448146442165432407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20636417930861922887243209 15477313448146442165432407)
        ·
          refine ⟨23215970172219663248148611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477313448146442165432407 23215970172219663248148611)
          ·
            refine ⟨34823955258329494872222917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23215970172219663248148611 34823955258329494872222917)
            ·
              refine ⟨6529491610936780288541797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34823955258329494872222917 6529491610936780288541797)
              ·
                refine ⟨1224279677050646304101587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6529491610936780288541797 1224279677050646304101587)
                ·
                  refine ⟨1836419515575969456152381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224279677050646304101587 1836419515575969456152381)
                  ·
                    refine ⟨688657318340988546057143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836419515575969456152381 688657318340988546057143)
                    ·
                      rfl

theorem cell22_2011733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_2011733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011733 prefixEnd_2011733 := by exact prefixLift 2011733
  have htrace : WordTrace (prefixWord ++ tailWord_2011733) baseStart_2011733 baseEnd_2011733 := by
    simpa [prefixWord, tailWord_2011733, baseEnd_2011733] using wordTrace_append hprefix tailTrace_2011733
  have hstable : (prefixWord ++ tailWord_2011733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011733).length < 2 ^ (prefixWord ++ tailWord_2011733).sum := by decide
  have hdescent : baseEnd_2011733 < baseStart_2011733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011744 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_2011744 : Nat := 118140960795 + 2011744 * 2 ^ 59
def prefixEnd_2011744 : Nat := 4983230072969 + 3 ^ 40 * 2011744 * 2
def baseEnd_2011744 : Nat := 688661083865788184032109

theorem tailTrace_2011744 : CollatzResearch.WordTrace tailWord_2011744 prefixEnd_2011744 688661083865788184032109 := by
  unfold tailWord_2011744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687165811901270683313143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48916221082535027577750857 36687165811901270683313143)
  ·
    refine ⟨55030748717851906024969715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36687165811901270683313143 55030748717851906024969715)
    ·
      refine ⟨82546123076777859037454573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55030748717851906024969715 82546123076777859037454573)
      ·
        refine ⟨30954796153791697139045465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82546123076777859037454573 30954796153791697139045465)
        ·
          refine ⟨23216097115343772854284099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30954796153791697139045465 23216097115343772854284099)
          ·
            refine ⟨34824145673015659281426149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23216097115343772854284099 34824145673015659281426149)
            ·
              refine ⟨6529527313690436115267403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34824145673015659281426149 6529527313690436115267403)
              ·
                refine ⟨9794290970535654172901105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529527313690436115267403 9794290970535654172901105)
                ·
                  refine ⟨7345718227901740629675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794290970535654172901105 7345718227901740629675829)
                  ·
                    refine ⟨688661083865788184032109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7345718227901740629675829 688661083865788184032109)
                    ·
                      rfl

theorem cell22_2011744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_2011744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011744 prefixEnd_2011744 := by exact prefixLift 2011744
  have htrace : WordTrace (prefixWord ++ tailWord_2011744) baseStart_2011744 baseEnd_2011744 := by
    simpa [prefixWord, tailWord_2011744, baseEnd_2011744] using wordTrace_append hprefix tailTrace_2011744
  have hstable : (prefixWord ++ tailWord_2011744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011744).length < 2 ^ (prefixWord ++ tailWord_2011744).sum := by decide
  have hdescent : baseEnd_2011744 < baseStart_2011744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011759 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_2011759 : Nat := 118140960795 + 2011759 * 2 ^ 59
def prefixEnd_2011759 : Nat := 4983230072969 + 3 ^ 40 * 2011759 * 2
def baseEnd_2011759 : Nat := 688666218672333144907063

theorem tailTrace_2011759 : CollatzResearch.WordTrace tailWord_2011759 prefixEnd_2011759 688666218672333144907063 := by
  unfold tailWord_2011759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73374878718748198928422331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48916585812498799285614887 73374878718748198928422331)
  ·
    refine ⟨110062318078122298392633497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73374878718748198928422331 110062318078122298392633497)
    ·
      refine ⟨82546738558591723794475123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110062318078122298392633497 82546738558591723794475123)
      ·
        refine ⟨123820107837887585691712685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82546738558591723794475123 123820107837887585691712685)
        ·
          refine ⟨46432540439207844634392257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123820107837887585691712685 46432540439207844634392257)
          ·
            refine ⟨34824405329405883475794193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46432540439207844634392257 34824405329405883475794193)
            ·
              refine ⟨26118303997054412606845645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34824405329405883475794193 26118303997054412606845645)
              ·
                refine ⟨9794363998895404727567117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26118303997054412606845645 9794363998895404727567117)
                ·
                  refine ⟨3672886499585776772837669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9794363998895404727567117 3672886499585776772837669)
                  ·
                    refine ⟨688666218672333144907063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672886499585776772837669 688666218672333144907063)
                    ·
                      rfl

theorem cell22_2011759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_2011759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011759 prefixEnd_2011759 := by exact prefixLift 2011759
  have htrace : WordTrace (prefixWord ++ tailWord_2011759) baseStart_2011759 baseEnd_2011759 := by
    simpa [prefixWord, tailWord_2011759, baseEnd_2011759] using wordTrace_append hprefix tailTrace_2011759
  have hstable : (prefixWord ++ tailWord_2011759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011759).length < 2 ^ (prefixWord ++ tailWord_2011759).sum := by decide
  have hdescent : baseEnd_2011759 < baseStart_2011759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011776 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_2011776 : Nat := 118140960795 + 2011776 * 2 ^ 59
def prefixEnd_2011776 : Nat := 4983230072969 + 3 ^ 40 * 2011776 * 2
def baseEnd_2011776 : Nat := 688672038119750767232011

theorem tailTrace_2011776 : CollatzResearch.WordTrace tailWord_2011776 prefixEnd_2011776 688672038119750767232011 := by
  unfold tailWord_2011776
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687749379843305415895591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48916999173124407221194121 36687749379843305415895591)
  ·
    refine ⟨55031624069764958123843387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36687749379843305415895591 55031624069764958123843387)
    ·
      refine ⟨82547436104647437185765081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55031624069764958123843387 82547436104647437185765081)
      ·
        refine ⟨61910577078485577889323811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82547436104647437185765081 61910577078485577889323811)
        ·
          refine ⟨92865865617728366833985717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61910577078485577889323811 92865865617728366833985717)
          ·
            refine ⟨8706174901662034390686161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92865865617728366833985717 8706174901662034390686161)
            ·
              refine ⟨6529631176246525793014621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706174901662034390686161 6529631176246525793014621)
              ·
                refine ⟨2448611691092447172380483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6529631176246525793014621 2448611691092447172380483)
                ·
                  refine ⟨3672917536638670758570725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448611691092447172380483 3672917536638670758570725)
                  ·
                    refine ⟨688672038119750767232011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3672917536638670758570725 688672038119750767232011)
                    ·
                      rfl

theorem cell22_2011776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_2011776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011776 prefixEnd_2011776 := by exact prefixLift 2011776
  have htrace : WordTrace (prefixWord ++ tailWord_2011776) baseStart_2011776 baseEnd_2011776 := by
    simpa [prefixWord, tailWord_2011776, baseEnd_2011776] using wordTrace_append hprefix tailTrace_2011776
  have hstable : (prefixWord ++ tailWord_2011776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011776).length < 2 ^ (prefixWord ++ tailWord_2011776).sum := by decide
  have hdescent : baseEnd_2011776 < baseStart_2011776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011902 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2011902 : Nat := 118140960795 + 2011902 * 2 ^ 59
def prefixEnd_2011902 : Nat := 4983230072969 + 3 ^ 40 * 2011902 * 2
def baseEnd_2011902 : Nat := 688715170494728438581625

theorem tailTrace_2011902 : CollatzResearch.WordTrace tailWord_2011902 prefixEnd_2011902 688715170494728438581625 := by
  unfold tailWord_2011902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172511794653766793859745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48920062904820089567251973 9172511794653766793859745)
  ·
    refine ⟨6879383845990325095394809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9172511794653766793859745 6879383845990325095394809)
    ·
      refine ⟨5159537884492743821546107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6879383845990325095394809 5159537884492743821546107)
      ·
        refine ⟨7739306826739115732319161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159537884492743821546107 7739306826739115732319161)
        ·
          refine ⟨5804480120054336799239371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739306826739115732319161 5804480120054336799239371)
          ·
            refine ⟨8706720180081505198859057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804480120054336799239371 8706720180081505198859057)
            ·
              refine ⟨6530040135061128899144293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706720180081505198859057 6530040135061128899144293)
              ·
                refine ⟨1224382525323961668589555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6530040135061128899144293 1224382525323961668589555)
                ·
                  refine ⟨1836573787985942502884333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224382525323961668589555 1836573787985942502884333)
                  ·
                    refine ⟨688715170494728438581625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836573787985942502884333 688715170494728438581625)
                    ·
                      rfl

theorem cell22_2011902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2011902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011902 prefixEnd_2011902 := by exact prefixLift 2011902
  have htrace : WordTrace (prefixWord ++ tailWord_2011902) baseStart_2011902 baseEnd_2011902 := by
    simpa [prefixWord, tailWord_2011902, baseEnd_2011902] using wordTrace_append hprefix tailTrace_2011902
  have hstable : (prefixWord ++ tailWord_2011902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011902).length < 2 ^ (prefixWord ++ tailWord_2011902).sum := by decide
  have hdescent : baseEnd_2011902 < baseStart_2011902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011941 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2011941 : Nat := 118140960795 + 2011941 * 2 ^ 59
def prefixEnd_2011941 : Nat := 4983230072969 + 3 ^ 40 * 2011941 * 2
def baseEnd_2011941 : Nat := 688728520991745336856505

theorem tailTrace_2011941 : CollatzResearch.WordTrace tailWord_2011941 prefixEnd_2011941 688728520991745336856505 := by
  unfold tailWord_2011941
  simp only [CollatzResearch.WordTrace]
  refine ⟨73381516804088844011547677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48921011202725896007698451 73381516804088844011547677)
  ·
    refine ⟨27518068801533316504330379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73381516804088844011547677 27518068801533316504330379)
    ·
      refine ⟨41277103202299974756495569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27518068801533316504330379 41277103202299974756495569)
      ·
        refine ⟨30957827401724981067371677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41277103202299974756495569 30957827401724981067371677)
        ·
          refine ⟨11609185275646867900264379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30957827401724981067371677 11609185275646867900264379)
          ·
            refine ⟨17413777913470301850396569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11609185275646867900264379 17413777913470301850396569)
            ·
              refine ⟨13060333435102726387797427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17413777913470301850396569 13060333435102726387797427)
              ·
                refine ⟨19590500152654089581696141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060333435102726387797427 19590500152654089581696141)
                ·
                  refine ⟨7346437557245283593136053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19590500152654089581696141 7346437557245283593136053)
                  ·
                    refine ⟨688728520991745336856505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7346437557245283593136053 688728520991745336856505)
                    ·
                      rfl

theorem cell22_2011941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2011941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011941 prefixEnd_2011941 := by exact prefixLift 2011941
  have htrace : WordTrace (prefixWord ++ tailWord_2011941) baseStart_2011941 baseEnd_2011941 := by
    simpa [prefixWord, tailWord_2011941, baseEnd_2011941] using wordTrace_append hprefix tailTrace_2011941
  have hstable : (prefixWord ++ tailWord_2011941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011941).length < 2 ^ (prefixWord ++ tailWord_2011941).sum := by decide
  have hdescent : baseEnd_2011941 < baseStart_2011941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011960 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_2011960 : Nat := 118140960795 + 2011960 * 2 ^ 59
def prefixEnd_2011960 : Nat := 4983230072969 + 3 ^ 40 * 2011960 * 2
def baseEnd_2011960 : Nat := 229578341693345206877149

theorem tailTrace_2011960 : CollatzResearch.WordTrace tailWord_2011960 prefixEnd_2011960 229578341693345206877149 := by
  unfold tailWord_2011960
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691104895510005128244667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48921473194013340170992889 36691104895510005128244667)
  ·
    refine ⟨55036657343265007692367001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36691104895510005128244667 55036657343265007692367001)
    ·
      refine ⟨41277493007448755769275251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55036657343265007692367001 41277493007448755769275251)
      ·
        refine ⟨61916239511173133653912877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41277493007448755769275251 61916239511173133653912877)
        ·
          refine ⟨23218589816689925120217329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61916239511173133653912877 23218589816689925120217329)
          ·
            refine ⟨17413942362517443840162997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23218589816689925120217329 17413942362517443840162997)
            ·
              refine ⟨1632557096486010360015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17413942362517443840162997 1632557096486010360015281)
              ·
                refine ⟨1224417822364507770011461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632557096486010360015281 1224417822364507770011461)
                ·
                  refine ⟨229578341693345206877149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224417822364507770011461 229578341693345206877149)
                  ·
                    rfl

theorem cell22_2011960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_2011960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011960 prefixEnd_2011960 := by exact prefixLift 2011960
  have htrace : WordTrace (prefixWord ++ tailWord_2011960) baseStart_2011960 baseEnd_2011960 := by
    simpa [prefixWord, tailWord_2011960, baseEnd_2011960] using wordTrace_append hprefix tailTrace_2011960
  have hstable : (prefixWord ++ tailWord_2011960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011960).length < 2 ^ (prefixWord ++ tailWord_2011960).sum := by decide
  have hdescent : baseEnd_2011960 < baseStart_2011960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011971 : List Nat := [1, 1, 1, 3, 1, 4, 4, 7]
def baseStart_2011971 : Nat := 118140960795 + 2011971 * 2 ^ 59
def prefixEnd_2011971 : Nat := 4983230072969 + 3 ^ 40 * 2011971 * 2
def baseEnd_2011971 : Nat := 76526532289426139845157

theorem tailTrace_2011971 : CollatzResearch.WordTrace tailWord_2011971 prefixEnd_2011971 76526532289426139845157 := by
  unfold tailWord_2011971
  simp only [CollatzResearch.WordTrace]
  refine ⟨73382610993980159135139767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48921740662653439423426511 73382610993980159135139767)
  ·
    refine ⟨110073916490970238702709651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73382610993980159135139767 110073916490970238702709651)
    ·
      refine ⟨165110874736455358054064477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110073916490970238702709651 165110874736455358054064477)
      ·
        refine ⟨61916578026170759270274179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165110874736455358054064477 61916578026170759270274179)
        ·
          refine ⟨92874867039256138905411269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61916578026170759270274179 92874867039256138905411269)
          ·
            refine ⟨17414037569860526044764613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92874867039256138905411269 17414037569860526044764613)
            ·
              refine ⟨3265132044348848633393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17414037569860526044764613 3265132044348848633393365)
              ·
                refine ⟨76526532289426139845157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3265132044348848633393365 76526532289426139845157)
                ·
                  rfl

theorem cell22_2011971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 7].length) (baseStart_2011971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2011971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2011971 prefixEnd_2011971 := by exact prefixLift 2011971
  have htrace : WordTrace (prefixWord ++ tailWord_2011971) baseStart_2011971 baseEnd_2011971 := by
    simpa [prefixWord, tailWord_2011971, baseEnd_2011971] using wordTrace_append hprefix tailTrace_2011971
  have hstable : (prefixWord ++ tailWord_2011971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011971).length < 2 ^ (prefixWord ++ tailWord_2011971).sum := by decide
  have hdescent : baseEnd_2011971 < baseStart_2011971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012016 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_2012016 : Nat := 118140960795 + 2012016 * 2 ^ 59
def prefixEnd_2012016 : Nat := 4983230072969 + 3 ^ 40 * 2012016 * 2
def baseEnd_2012016 : Nat := 229584731674823380410425

theorem tailTrace_2012016 : CollatzResearch.WordTrace tailWord_2012016 prefixEnd_2012016 229584731674823380410425 := by
  unfold tailWord_2012016
  simp only [CollatzResearch.WordTrace]
  refine ⟨36692126139408565910263951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48922834852544754547018601 36692126139408565910263951)
  ·
    refine ⟨55038189209112848865395927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36692126139408565910263951 55038189209112848865395927)
    ·
      refine ⟨82557283813669273298093891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55038189209112848865395927 82557283813669273298093891)
      ·
        refine ⟨123835925720503909947140837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82557283813669273298093891 123835925720503909947140837)
        ·
          refine ⟨23219236072594483115088907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123835925720503909947140837 23219236072594483115088907)
          ·
            refine ⟨34828854108891724672633361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23219236072594483115088907 34828854108891724672633361)
            ·
              refine ⟨26121640581668793504475021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34828854108891724672633361 26121640581668793504475021)
              ·
                refine ⟨9795615218125797564178133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26121640581668793504475021 9795615218125797564178133)
                ·
                  refine ⟨229584731674823380410425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9795615218125797564178133 229584731674823380410425)
                  ·
                    rfl

theorem cell22_2012016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_2012016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012016 prefixEnd_2012016 := by exact prefixLift 2012016
  have htrace : WordTrace (prefixWord ++ tailWord_2012016) baseStart_2012016 baseEnd_2012016 := by
    simpa [prefixWord, tailWord_2012016, baseEnd_2012016] using wordTrace_append hprefix tailTrace_2012016
  have hstable : (prefixWord ++ tailWord_2012016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012016).length < 2 ^ (prefixWord ++ tailWord_2012016).sum := by decide
  have hdescent : baseEnd_2012016 < baseStart_2012016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012031 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_2012031 : Nat := 118140960795 + 2012031 * 2 ^ 59
def prefixEnd_2012031 : Nat := 4983230072969 + 3 ^ 40 * 2012031 * 2
def baseEnd_2012031 : Nat := 688759329831015102106229

theorem tailTrace_2012031 : CollatzResearch.WordTrace tailWord_2012031 prefixEnd_2012031 688759329831015102106229 := by
  unfold tailWord_2012031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73384799373762789382323947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48923199582508526254882631 73384799373762789382323947)
  ·
    refine ⟨110077199060644184073485921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73384799373762789382323947 110077199060644184073485921)
    ·
      refine ⟨82557899295483138055114441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110077199060644184073485921 82557899295483138055114441)
      ·
        refine ⟨61918424471612353541335831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82557899295483138055114441 61918424471612353541335831)
        ·
          refine ⟨92877636707418530312003747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61918424471612353541335831 92877636707418530312003747)
          ·
            refine ⟨139316455061127795468005621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92877636707418530312003747 139316455061127795468005621)
            ·
              refine ⟨13060917661980730825125527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139316455061127795468005621 13060917661980730825125527)
              ·
                refine ⟨19591376492971096237688291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060917661980730825125527 19591376492971096237688291)
                ·
                  refine ⟨29387064739456644356532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19591376492971096237688291 29387064739456644356532437)
                  ·
                    refine ⟨688759329831015102106229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29387064739456644356532437 688759329831015102106229)
                    ·
                      rfl

theorem cell22_2012031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_2012031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012031 prefixEnd_2012031 := by exact prefixLift 2012031
  have htrace : WordTrace (prefixWord ++ tailWord_2012031) baseStart_2012031 baseEnd_2012031 := by
    simpa [prefixWord, tailWord_2012031, baseEnd_2012031] using wordTrace_append hprefix tailTrace_2012031
  have hstable : (prefixWord ++ tailWord_2012031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012031).length < 2 ^ (prefixWord ++ tailWord_2012031).sum := by decide
  have hdescent : baseEnd_2012031 < baseStart_2012031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012084 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2012084 : Nat := 118140960795 + 2012084 * 2 ^ 59
def prefixEnd_2012084 : Nat := 4983230072969 + 3 ^ 40 * 2012084 * 2
def baseEnd_2012084 : Nat := 229592490938046876843689

theorem tailTrace_2012084 : CollatzResearch.WordTrace tailWord_2012084 prefixEnd_2012084 229592490938046876843689 := by
  unfold tailWord_2012084
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693366221285389717001653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48924488295047186289335537 36693366221285389717001653)
  ·
    refine ⟨3440003083245505285968905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36693366221285389717001653 3440003083245505285968905)
    ·
      refine ⟨2580002312434128964476679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3440003083245505285968905 2580002312434128964476679)
      ·
        refine ⟨3870003468651193446715019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580002312434128964476679 3870003468651193446715019)
        ·
          refine ⟨5805005202976790170072529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870003468651193446715019 5805005202976790170072529)
          ·
            refine ⟨4353753902232592627554397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5805005202976790170072529 4353753902232592627554397)
            ·
              refine ⟨1632657713337222235332899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4353753902232592627554397 1632657713337222235332899)
              ·
                refine ⟨2448986570005833352999349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632657713337222235332899 2448986570005833352999349)
                ·
                  refine ⟨229592490938046876843689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2448986570005833352999349 229592490938046876843689)
                  ·
                    rfl

theorem cell22_2012084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2012084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012084 prefixEnd_2012084 := by exact prefixLift 2012084
  have htrace : WordTrace (prefixWord ++ tailWord_2012084) baseStart_2012084 baseEnd_2012084 := by
    simpa [prefixWord, tailWord_2012084, baseEnd_2012084] using wordTrace_append hprefix tailTrace_2012084
  have hstable : (prefixWord ++ tailWord_2012084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012084).length < 2 ^ (prefixWord ++ tailWord_2012084).sum := by decide
  have hdescent : baseEnd_2012084 < baseStart_2012084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012108 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_2012108 : Nat := 118140960795 + 2012108 * 2 ^ 59
def prefixEnd_2012108 : Nat := 4983230072969 + 3 ^ 40 * 2012108 * 2
def baseEnd_2012108 : Nat := 688785688504612567930993

theorem tailTrace_2012108 : CollatzResearch.WordTrace tailWord_2012108 prefixEnd_2012108 688785688504612567930993 := by
  unfold tailWord_2012108
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693803897241915766438489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48925071862989221021917985 36693803897241915766438489)
  ·
    refine ⟨27520352922931436824828867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36693803897241915766438489 27520352922931436824828867)
    ·
      refine ⟨41280529384397155237243301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27520352922931436824828867 41280529384397155237243301)
      ·
        refine ⟨7740099259574466606983119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41280529384397155237243301 7740099259574466606983119)
        ·
          refine ⟨11610148889361699910474679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740099259574466606983119 11610148889361699910474679)
          ·
            refine ⟨17415223334042549865712019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610148889361699910474679 17415223334042549865712019)
            ·
              refine ⟨26122835001063824798568029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17415223334042549865712019 26122835001063824798568029)
              ·
                refine ⟨9796063125398934299463011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26122835001063824798568029 9796063125398934299463011)
                ·
                  refine ⟨14694094688098401449194517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9796063125398934299463011 14694094688098401449194517)
                  ·
                    refine ⟨688785688504612567930993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14694094688098401449194517 688785688504612567930993)
                    ·
                      rfl

theorem cell22_2012108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_2012108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012108 prefixEnd_2012108 := by exact prefixLift 2012108
  have htrace : WordTrace (prefixWord ++ tailWord_2012108) baseStart_2012108 baseEnd_2012108 := by
    simpa [prefixWord, tailWord_2012108, baseEnd_2012108] using wordTrace_append hprefix tailTrace_2012108
  have hstable : (prefixWord ++ tailWord_2012108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012108).length < 2 ^ (prefixWord ++ tailWord_2012108).sum := by decide
  have hdescent : baseEnd_2012108 < baseStart_2012108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012110 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2012110 : Nat := 118140960795 + 2012110 * 2 ^ 59
def prefixEnd_2012110 : Nat := 4983230072969 + 3 ^ 40 * 2012110 * 2
def baseEnd_2012110 : Nat := 688786373145485229380987

theorem tailTrace_2012110 : CollatzResearch.WordTrace tailWord_2012110 prefixEnd_2012110 688786373145485229380987 := by
  unfold tailWord_2012110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173460092559573234306223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48925120493651057249633189 9173460092559573234306223)
  ·
    refine ⟨13760190138839359851459335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9173460092559573234306223 13760190138839359851459335)
    ·
      refine ⟨20640285208259039777189003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13760190138839359851459335 20640285208259039777189003)
      ·
        refine ⟨30960427812388559665783505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640285208259039777189003 30960427812388559665783505)
        ·
          refine ⟨23220320859291419749337629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30960427812388559665783505 23220320859291419749337629)
          ·
            refine ⟨8707620322234282406001611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23220320859291419749337629 8707620322234282406001611)
            ·
              refine ⟨13061430483351423609002417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707620322234282406001611 13061430483351423609002417)
              ·
                refine ⟨9796072862513567706751813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13061430483351423609002417 9796072862513567706751813)
                ·
                  refine ⟨1836763661721293945015965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9796072862513567706751813 1836763661721293945015965)
                  ·
                    refine ⟨688786373145485229380987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836763661721293945015965 688786373145485229380987)
                    ·
                      rfl

theorem cell22_2012110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2012110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012110 prefixEnd_2012110 := by exact prefixLift 2012110
  have htrace : WordTrace (prefixWord ++ tailWord_2012110) baseStart_2012110 baseEnd_2012110 := by
    simpa [prefixWord, tailWord_2012110, baseEnd_2012110] using wordTrace_append hprefix tailTrace_2012110
  have hstable : (prefixWord ++ tailWord_2012110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012110).length < 2 ^ (prefixWord ++ tailWord_2012110).sum := by decide
  have hdescent : baseEnd_2012110 < baseStart_2012110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012125 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2012125 : Nat := 118140960795 + 2012125 * 2 ^ 59
def prefixEnd_2012125 : Nat := 4983230072969 + 3 ^ 40 * 2012125 * 2
def baseEnd_2012125 : Nat := 688791507952030190255941

theorem tailTrace_2012125 : CollatzResearch.WordTrace tailWord_2012125 prefixEnd_2012125 688791507952030190255941 := by
  unfold tailWord_2012125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73388227835422243436245829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48925485223614828957497219 73388227835422243436245829)
  ·
    refine ⟨13760292719141670644296093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73388227835422243436245829 13760292719141670644296093)
    ·
      refine ⟨5160109769678126491611035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13760292719141670644296093 5160109769678126491611035)
      ·
        refine ⟨7740164654517189737416553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160109769678126491611035 7740164654517189737416553)
        ·
          refine ⟨5805123490887892303062415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7740164654517189737416553 5805123490887892303062415)
          ·
            refine ⟨8707685236331838454593623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805123490887892303062415 8707685236331838454593623)
            ·
              refine ⟨13061527854497757681890435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707685236331838454593623 13061527854497757681890435)
              ·
                refine ⟨19592291781746636522835653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061527854497757681890435 19592291781746636522835653)
                ·
                  refine ⟨3673554709077494348031685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19592291781746636522835653 3673554709077494348031685)
                  ·
                    refine ⟨688791507952030190255941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673554709077494348031685 688791507952030190255941)
                    ·
                      rfl

theorem cell22_2012125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2012125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012125 prefixEnd_2012125 := by exact prefixLift 2012125
  have htrace : WordTrace (prefixWord ++ tailWord_2012125) baseStart_2012125 baseEnd_2012125 := by
    simpa [prefixWord, tailWord_2012125, baseEnd_2012125] using wordTrace_append hprefix tailTrace_2012125
  have hstable : (prefixWord ++ tailWord_2012125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012125).length < 2 ^ (prefixWord ++ tailWord_2012125).sum := by decide
  have hdescent : baseEnd_2012125 < baseStart_2012125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012178 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2012178 : Nat := 118140960795 + 2012178 * 2 ^ 59
def prefixEnd_2012178 : Nat := 4983230072969 + 3 ^ 40 * 2012178 * 2
def baseEnd_2012178 : Nat := 688809650935155718680779

theorem tailTrace_2012178 : CollatzResearch.WordTrace tailWord_2012178 prefixEnd_2012178 688809650935155718680779 := by
  unfold tailWord_2012178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347540226057558371981297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48926773936153488991950125 18347540226057558371981297)
  ·
    refine ⟨13760655169543168778985973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18347540226057558371981297 13760655169543168778985973)
    ·
      refine ⟨1290061422144672073029935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13760655169543168778985973 1290061422144672073029935)
      ·
        refine ⟨1935092133217008109544903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290061422144672073029935 1935092133217008109544903)
        ·
          refine ⟨2902638199825512164317355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935092133217008109544903 2902638199825512164317355)
          ·
            refine ⟨4353957299738268246476033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902638199825512164317355 4353957299738268246476033)
            ·
              refine ⟨3265467974803701184857025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353957299738268246476033 3265467974803701184857025)
              ·
                refine ⟨2449100981102775888642769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265467974803701184857025 2449100981102775888642769)
                ·
                  refine ⟨1836825735827081916482077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449100981102775888642769 1836825735827081916482077)
                  ·
                    refine ⟨688809650935155718680779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836825735827081916482077 688809650935155718680779)
                    ·
                      rfl

theorem cell22_2012178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2012178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012178 prefixEnd_2012178 := by exact prefixLift 2012178
  have htrace : WordTrace (prefixWord ++ tailWord_2012178) baseStart_2012178 baseEnd_2012178 := by
    simpa [prefixWord, tailWord_2012178, baseEnd_2012178] using wordTrace_append hprefix tailTrace_2012178
  have hstable : (prefixWord ++ tailWord_2012178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012178).length < 2 ^ (prefixWord ++ tailWord_2012178).sum := by decide
  have hdescent : baseEnd_2012178 < baseStart_2012178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012215 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2012215 : Nat := 118140960795 + 2012215 * 2 ^ 59
def prefixEnd_2012215 : Nat := 4983230072969 + 3 ^ 40 * 2012215 * 2
def baseEnd_2012215 : Nat := 688822316791299955505665

theorem tailTrace_2012215 : CollatzResearch.WordTrace tailWord_2012215 prefixEnd_2012215 688822316791299955505665 := by
  unfold tailWord_2012215
  simp only [CollatzResearch.WordTrace]
  refine ⟨73391510405096188807022099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48927673603397459204681399 73391510405096188807022099)
  ·
    refine ⟨110087265607644283210533149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73391510405096188807022099 110087265607644283210533149)
    ·
      refine ⟨41282724602866606203949931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110087265607644283210533149 41282724602866606203949931)
      ·
        refine ⟨61924086904299909305924897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41282724602866606203949931 61924086904299909305924897)
        ·
          refine ⟨46443065178224931979443673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61924086904299909305924897 46443065178224931979443673)
          ·
            refine ⟨34832298883668698984582755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46443065178224931979443673 34832298883668698984582755)
            ·
              refine ⟨52248448325503048476874133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34832298883668698984582755 52248448325503048476874133)
              ·
                refine ⟨2449146015257955397353475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52248448325503048476874133 2449146015257955397353475)
                ·
                  refine ⟨3673719022886933096030213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449146015257955397353475 3673719022886933096030213)
                  ·
                    refine ⟨688822316791299955505665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3673719022886933096030213 688822316791299955505665)
                    ·
                      rfl

theorem cell22_2012215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2012215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012215 prefixEnd_2012215 := by exact prefixLift 2012215
  have htrace : WordTrace (prefixWord ++ tailWord_2012215) baseStart_2012215 baseEnd_2012215 := by
    simpa [prefixWord, tailWord_2012215, baseEnd_2012215] using wordTrace_append hprefix tailTrace_2012215
  have hstable : (prefixWord ++ tailWord_2012215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012215).length < 2 ^ (prefixWord ++ tailWord_2012215).sum := by decide
  have hdescent : baseEnd_2012215 < baseStart_2012215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012243 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_2012243 : Nat := 118140960795 + 2012243 * 2 ^ 59
def prefixEnd_2012243 : Nat := 4983230072969 + 3 ^ 40 * 2012243 * 2
def baseEnd_2012243 : Nat := 688831901763517215805579

theorem tailTrace_2012243 : CollatzResearch.WordTrace tailWord_2012243 prefixEnd_2012243 688831901763517215805579 := by
  unfold tailWord_2012243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392531648994749589041383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48928354432663166392694255 73392531648994749589041383)
  ·
    refine ⟨110088797473492124383562075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73392531648994749589041383 110088797473492124383562075)
    ·
      refine ⟨165133196210238186575343113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110088797473492124383562075 165133196210238186575343113)
      ·
        refine ⟨123849897157678639931507335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165133196210238186575343113 123849897157678639931507335)
        ·
          refine ⟨185774845736517959897261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123849897157678639931507335 185774845736517959897261003)
          ·
            refine ⟨278662268604776939845891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185774845736517959897261003 278662268604776939845891505)
            ·
              refine ⟨208996701453582704884418629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278662268604776939845891505 208996701453582704884418629)
              ·
                refine ⟨39186881522546757165828493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208996701453582704884418629 39186881522546757165828493)
                ·
                  refine ⟨14695080570955033937185685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39186881522546757165828493 14695080570955033937185685)
                  ·
                    refine ⟨688831901763517215805579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14695080570955033937185685 688831901763517215805579)
                    ·
                      rfl

theorem cell22_2012243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_2012243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012243 prefixEnd_2012243 := by exact prefixLift 2012243
  have htrace : WordTrace (prefixWord ++ tailWord_2012243) baseStart_2012243 baseEnd_2012243 := by
    simpa [prefixWord, tailWord_2012243, baseEnd_2012243] using wordTrace_append hprefix tailTrace_2012243
  have hstable : (prefixWord ++ tailWord_2012243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012243).length < 2 ^ (prefixWord ++ tailWord_2012243).sum := by decide
  have hdescent : baseEnd_2012243 < baseStart_2012243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012281 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 4]
def baseStart_2012281 : Nat := 118140960795 + 2012281 * 2 ^ 59
def prefixEnd_2012281 : Nat := 4983230072969 + 3 ^ 40 * 2012281 * 2
def baseEnd_2012281 : Nat := 229614969980032594451821

theorem tailTrace_2012281 : CollatzResearch.WordTrace tailWord_2012281 prefixEnd_2012281 229614969980032594451821 := by
  unfold tailWord_2012281
  simp only [CollatzResearch.WordTrace]
  refine ⟨73393917622857082078924697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48929278415238054719283131 73393917622857082078924697)
  ·
    refine ⟨55045438217142811559193523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73393917622857082078924697 55045438217142811559193523)
    ·
      refine ⟨82568157325714217338790285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55045438217142811559193523 82568157325714217338790285)
      ·
        refine ⟨30963058997142831502046357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82568157325714217338790285 30963058997142831502046357)
        ·
          refine ⟨1451393390491070226658423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30963058997142831502046357 1451393390491070226658423)
          ·
            refine ⟨2177090085736605339987635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451393390491070226658423 2177090085736605339987635)
            ·
              refine ⟨3265635128604908009981453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177090085736605339987635 3265635128604908009981453)
              ·
                refine ⟨1224613173226840503743045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3265635128604908009981453 1224613173226840503743045)
                ·
                  refine ⟨229614969980032594451821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224613173226840503743045 229614969980032594451821)
                  ·
                    rfl

theorem cell22_2012281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_2012281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012281 prefixEnd_2012281 := by exact prefixLift 2012281
  have htrace : WordTrace (prefixWord ++ tailWord_2012281) baseStart_2012281 baseEnd_2012281 := by
    simpa [prefixWord, tailWord_2012281, baseEnd_2012281] using wordTrace_append hprefix tailTrace_2012281
  have hstable : (prefixWord ++ tailWord_2012281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012281).length < 2 ^ (prefixWord ++ tailWord_2012281).sum := by decide
  have hdescent : baseEnd_2012281 < baseStart_2012281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012307 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 3, 3]
def baseStart_2012307 : Nat := 118140960795 + 2012307 * 2 ^ 59
def prefixEnd_2012307 : Nat := 4983230072969 + 3 ^ 40 * 2012307 * 2
def baseEnd_2012307 : Nat := 688853810271442382205383

theorem tailTrace_2012307 : CollatzResearch.WordTrace tailWord_2012307 prefixEnd_2012307 688853810271442382205383 := by
  unfold tailWord_2012307
  simp only [CollatzResearch.WordTrace]
  refine ⟨73394865920762888519371175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48929910613841925679580783 73394865920762888519371175)
  ·
    refine ⟨110092298881144332779056763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73394865920762888519371175 110092298881144332779056763)
    ·
      refine ⟨165138448321716499168585145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110092298881144332779056763 165138448321716499168585145)
      ·
        refine ⟨123853836241287374376438859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165138448321716499168585145 123853836241287374376438859)
        ·
          refine ⟨185780754361931061564658289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123853836241287374376438859 185780754361931061564658289)
          ·
            refine ⟨139335565771448296173493717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185780754361931061564658289 139335565771448296173493717)
            ·
              refine ⟨3265677322768319441566259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139335565771448296173493717 3265677322768319441566259)
              ·
                refine ⟨4898515984152479162349389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265677322768319441566259 4898515984152479162349389)
                ·
                  refine ⟨1836943494057179685881021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898515984152479162349389 1836943494057179685881021)
                  ·
                    refine ⟨688853810271442382205383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836943494057179685881021 688853810271442382205383)
                    ·
                      rfl

theorem cell22_2012307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].length) (baseStart_2012307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012307 prefixEnd_2012307 := by exact prefixLift 2012307
  have htrace : WordTrace (prefixWord ++ tailWord_2012307) baseStart_2012307 baseEnd_2012307 := by
    simpa [prefixWord, tailWord_2012307, baseEnd_2012307] using wordTrace_append hprefix tailTrace_2012307
  have hstable : (prefixWord ++ tailWord_2012307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012307).length < 2 ^ (prefixWord ++ tailWord_2012307).sum := by decide
  have hdescent : baseEnd_2012307 < baseStart_2012307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012410 : List Nat := [3, 1, 1, 1, 1, 4, 11]
def baseStart_2012410 : Nat := 118140960795 + 2012410 * 2 ^ 59
def prefixEnd_2012410 : Nat := 4983230072969 + 3 ^ 40 * 2012410 * 2
def baseEnd_2012410 : Nat := 25514409973199423958521

theorem tailTrace_2012410 : CollatzResearch.WordTrace tailWord_2012410 prefixEnd_2012410 25514409973199423958521 := by
  unfold tailWord_2012410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18349655659847434277592671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48932415092926491406913789 18349655659847434277592671)
  ·
    refine ⟨27524483489771151416389007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18349655659847434277592671 27524483489771151416389007)
    ·
      refine ⟨41286725234656727124583511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27524483489771151416389007 41286725234656727124583511)
      ·
        refine ⟨61930087851985090686875267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41286725234656727124583511 61930087851985090686875267)
        ·
          refine ⟨92895131777977636030312901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61930087851985090686875267 92895131777977636030312901)
          ·
            refine ⟨17417837208370806755683669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92895131777977636030312901 17417837208370806755683669)
            ·
              refine ⟨25514409973199423958521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17417837208370806755683669 25514409973199423958521)
              ·
                rfl

theorem cell22_2012410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 11].length) (baseStart_2012410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012410 prefixEnd_2012410 := by exact prefixLift 2012410
  have htrace : WordTrace (prefixWord ++ tailWord_2012410) baseStart_2012410 baseEnd_2012410 := by
    simpa [prefixWord, tailWord_2012410, baseEnd_2012410] using wordTrace_append hprefix tailTrace_2012410
  have hstable : (prefixWord ++ tailWord_2012410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012410).length < 2 ^ (prefixWord ++ tailWord_2012410).sum := by decide
  have hdescent : baseEnd_2012410 < baseStart_2012410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012472 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_2012472 : Nat := 118140960795 + 2012472 * 2 ^ 59
def prefixEnd_2012472 : Nat := 4983230072969 + 3 ^ 40 * 2012472 * 2
def baseEnd_2012472 : Nat := 229636764381145650609959

theorem tailTrace_2012472 : CollatzResearch.WordTrace tailWord_2012472 prefixEnd_2012472 229636764381145650609959 := by
  unfold tailWord_2012472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700441982582560849563835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48933922643443414466085113 36700441982582560849563835)
  ·
    refine ⟨55050662973873841274345753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36700441982582560849563835 55050662973873841274345753)
    ·
      refine ⟨41287997230405380955759315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55050662973873841274345753 41287997230405380955759315)
      ·
        refine ⟨61931995845608071433638973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41287997230405380955759315 61931995845608071433638973)
        ·
          refine ⟨23224498442103026787614615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61931995845608071433638973 23224498442103026787614615)
          ·
            refine ⟨34836747663154540181421923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23224498442103026787614615 34836747663154540181421923)
            ·
              refine ⟨52255121494731810272132885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836747663154540181421923 52255121494731810272132885)
              ·
                refine ⟨2449458820065553606506229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52255121494731810272132885 2449458820065553606506229)
                ·
                  refine ⟨229636764381145650609959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2449458820065553606506229 229636764381145650609959)
                  ·
                    rfl

theorem cell22_2012472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_2012472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012472 prefixEnd_2012472 := by exact prefixLift 2012472
  have htrace : WordTrace (prefixWord ++ tailWord_2012472) baseStart_2012472 baseEnd_2012472 := by
    simpa [prefixWord, tailWord_2012472, baseEnd_2012472] using wordTrace_append hprefix tailTrace_2012472
  have hstable : (prefixWord ++ tailWord_2012472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012472).length < 2 ^ (prefixWord ++ tailWord_2012472).sum := by decide
  have hdescent : baseEnd_2012472 < baseStart_2012472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012476 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2012476 : Nat := 118140960795 + 2012476 * 2 ^ 59
def prefixEnd_2012476 : Nat := 4983230072969 + 3 ^ 40 * 2012476 * 2
def baseEnd_2012476 : Nat := 688911662425182274729865

theorem tailTrace_2012476 : CollatzResearch.WordTrace tailWord_2012476 prefixEnd_2012476 688911662425182274729865 := by
  unfold tailWord_2012476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700514928575315191136641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48934019904767086921515521 36700514928575315191136641)
  ·
    refine ⟨27525386196431486393352481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36700514928575315191136641 27525386196431486393352481)
    ·
      refine ⟨20644039647323614795014361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27525386196431486393352481 20644039647323614795014361)
      ·
        refine ⟨15483029735492711096260771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20644039647323614795014361 15483029735492711096260771)
        ·
          refine ⟨23224544603239066644391157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483029735492711096260771 23224544603239066644391157)
          ·
            refine ⟨2177301056553662497911671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23224544603239066644391157 2177301056553662497911671)
            ·
              refine ⟨3265951584830493746867507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177301056553662497911671 3265951584830493746867507)
              ·
                refine ⟨4898927377245740620301261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265951584830493746867507 4898927377245740620301261)
                ·
                  refine ⟨1837097766467152732612973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898927377245740620301261 1837097766467152732612973)
                  ·
                    refine ⟨688911662425182274729865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837097766467152732612973 688911662425182274729865)
                    ·
                      rfl

theorem cell22_2012476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2012476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012476 prefixEnd_2012476 := by exact prefixLift 2012476
  have htrace : WordTrace (prefixWord ++ tailWord_2012476) baseStart_2012476 baseEnd_2012476 := by
    simpa [prefixWord, tailWord_2012476, baseEnd_2012476] using wordTrace_append hprefix tailTrace_2012476
  have hstable : (prefixWord ++ tailWord_2012476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012476).length < 2 ^ (prefixWord ++ tailWord_2012476).sum := by decide
  have hdescent : baseEnd_2012476 < baseStart_2012476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012489 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 5]
def baseStart_2012489 : Nat := 118140960795 + 2012489 * 2 ^ 59
def prefixEnd_2012489 : Nat := 4983230072969 + 3 ^ 40 * 2012489 * 2
def baseEnd_2012489 : Nat := 229638704196951524718275

theorem tailTrace_2012489 : CollatzResearch.WordTrace tailWord_2012489 prefixEnd_2012489 229638704196951524718275 := by
  unfold tailWord_2012489
  simp only [CollatzResearch.WordTrace]
  refine ⟨73401504006103533602496521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48934336004069022401664347 73401504006103533602496521)
  ·
    refine ⟨55051128004577650201872391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73401504006103533602496521 55051128004577650201872391)
    ·
      refine ⟨82576692006866475302808587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55051128004577650201872391 82576692006866475302808587)
      ·
        refine ⟨123865038010299712954212881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82576692006866475302808587 123865038010299712954212881)
        ·
          refine ⟨92898778507724784715659661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123865038010299712954212881 92898778507724784715659661)
          ·
            refine ⟨34837041940396794268372373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92898778507724784715659661 34837041940396794268372373)
            ·
              refine ⟨1632986340956099731329955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34837041940396794268372373 1632986340956099731329955)
              ·
                refine ⟨2449479511434149596994933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632986340956099731329955 2449479511434149596994933)
                ·
                  refine ⟨229638704196951524718275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2449479511434149596994933 229638704196951524718275)
                  ·
                    rfl

theorem cell22_2012489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_2012489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012489 prefixEnd_2012489 := by exact prefixLift 2012489
  have htrace : WordTrace (prefixWord ++ tailWord_2012489) baseStart_2012489 baseEnd_2012489 := by
    simpa [prefixWord, tailWord_2012489, baseEnd_2012489] using wordTrace_append hprefix tailTrace_2012489
  have hstable : (prefixWord ++ tailWord_2012489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012489).length < 2 ^ (prefixWord ++ tailWord_2012489).sum := by decide
  have hdescent : baseEnd_2012489 < baseStart_2012489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012568 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_2012568 : Nat := 118140960795 + 2012568 * 2 ^ 59
def prefixEnd_2012568 : Nat := 4983230072969 + 3 ^ 40 * 2012568 * 2
def baseEnd_2012568 : Nat := 229647718635108233809861

theorem tailTrace_2012568 : CollatzResearch.WordTrace tailWord_2012568 prefixEnd_2012568 229647718635108233809861 := by
  unfold tailWord_2012568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702192686408665047311179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48936256915211553396414905 36702192686408665047311179)
  ·
    refine ⟨55053289029612997570966769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702192686408665047311179 55053289029612997570966769)
    ·
      refine ⟨41289966772209748178225077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55053289029612997570966769 41289966772209748178225077)
      ·
        refine ⟨3870934384894663891708601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41289966772209748178225077 3870934384894663891708601)
        ·
          refine ⟨2903200788670997918781451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870934384894663891708601 2903200788670997918781451)
          ·
            refine ⟨4354801183006496878172177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903200788670997918781451 4354801183006496878172177)
            ·
              refine ⟨3266100887254872658629133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354801183006496878172177 3266100887254872658629133)
              ·
                refine ⟨1224787832720577246985925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3266100887254872658629133 1224787832720577246985925)
                ·
                  refine ⟨229647718635108233809861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224787832720577246985925 229647718635108233809861)
                  ·
                    rfl

theorem cell22_2012568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_2012568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012568 prefixEnd_2012568 := by exact prefixLift 2012568
  have htrace : WordTrace (prefixWord ++ tailWord_2012568) baseStart_2012568 baseEnd_2012568 := by
    simpa [prefixWord, tailWord_2012568, baseEnd_2012568] using wordTrace_append hprefix tailTrace_2012568
  have hstable : (prefixWord ++ tailWord_2012568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012568).length < 2 ^ (prefixWord ++ tailWord_2012568).sum := by decide
  have hdescent : baseEnd_2012568 < baseStart_2012568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012592 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_2012592 : Nat := 118140960795 + 2012592 * 2 ^ 59
def prefixEnd_2012592 : Nat := 4983230072969 + 3 ^ 40 * 2012592 * 2
def baseEnd_2012592 : Nat := 688951371595796638829509

theorem tailTrace_2012592 : CollatzResearch.WordTrace tailWord_2012592 prefixEnd_2012592 688951371595796638829509 := by
  unfold tailWord_2012592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702630362365191096748015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48936840483153588128997353 36702630362365191096748015)
  ·
    refine ⟨55053945543547786645122023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702630362365191096748015 55053945543547786645122023)
    ·
      refine ⟨82580918315321679967683035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55053945543547786645122023 82580918315321679967683035)
      ·
        refine ⟨123871377472982519951524553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82580918315321679967683035 123871377472982519951524553)
        ·
          refine ⟨92903533104736889963643415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123871377472982519951524553 92903533104736889963643415)
          ·
            refine ⟨139355299657105334945465123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92903533104736889963643415 139355299657105334945465123)
            ·
              refine ⟨209032949485658002418197685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139355299657105334945465123 209032949485658002418197685)
              ·
                refine ⟨19596839014280437726706033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209032949485658002418197685 19596839014280437726706033)
                ·
                  refine ⟨14697629260710328295029525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19596839014280437726706033 14697629260710328295029525)
                  ·
                    refine ⟨688951371595796638829509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14697629260710328295029525 688951371595796638829509)
                    ·
                      rfl

theorem cell22_2012592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_2012592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012592 prefixEnd_2012592 := by exact prefixLift 2012592
  have htrace : WordTrace (prefixWord ++ tailWord_2012592) baseStart_2012592 baseEnd_2012592 := by
    simpa [prefixWord, tailWord_2012592, baseEnd_2012592] using wordTrace_append hprefix tailTrace_2012592
  have hstable : (prefixWord ++ tailWord_2012592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012592).length < 2 ^ (prefixWord ++ tailWord_2012592).sum := by decide
  have hdescent : baseEnd_2012592 < baseStart_2012592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012658 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2012658 : Nat := 118140960795 + 2012658 * 2 ^ 59
def prefixEnd_2012658 : Nat := 4983230072969 + 3 ^ 40 * 2012658 * 2
def baseEnd_2012658 : Nat := 229657988248198155559769

theorem tailTrace_2012658 : CollatzResearch.WordTrace tailWord_2012658 prefixEnd_2012658 229657988248198155559769 := by
  unfold tailWord_2012658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18351916985622818866349657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48938445294994183643599085 18351916985622818866349657)
  ·
    refine ⟨13763937739217114149762243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18351916985622818866349657 13763937739217114149762243)
    ·
      refine ⟨20645906608825671224643365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13763937739217114149762243 20645906608825671224643365)
      ·
        refine ⟨3871107489154813354620631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20645906608825671224643365 3871107489154813354620631)
        ·
          refine ⟨5806661233732220031930947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871107489154813354620631 5806661233732220031930947)
          ·
            refine ⟨8709991850598330047896421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806661233732220031930947 8709991850598330047896421)
            ·
              refine ⟨1633123471987186883980579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8709991850598330047896421 1633123471987186883980579)
              ·
                refine ⟨2449685207980780325970869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633123471987186883980579 2449685207980780325970869)
                ·
                  refine ⟨229657988248198155559769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2449685207980780325970869 229657988248198155559769)
                  ·
                    rfl

theorem cell22_2012658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2012658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012658 prefixEnd_2012658 := by exact prefixLift 2012658
  have htrace : WordTrace (prefixWord ++ tailWord_2012658) baseStart_2012658 baseEnd_2012658 := by
    simpa [prefixWord, tailWord_2012658, baseEnd_2012658] using wordTrace_append hprefix tailTrace_2012658
  have hstable : (prefixWord ++ tailWord_2012658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012658).length < 2 ^ (prefixWord ++ tailWord_2012658).sum := by decide
  have hdescent : baseEnd_2012658 < baseStart_2012658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012703 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 4]
def baseStart_2012703 : Nat := 118140960795 + 2012703 * 2 ^ 59
def prefixEnd_2012703 : Nat := 4983230072969 + 3 ^ 40 * 2012703 * 2
def baseEnd_2012703 : Nat := 229663123054743116434723

theorem tailTrace_2012703 : CollatzResearch.WordTrace tailWord_2012703 prefixEnd_2012703 229663123054743116434723 := by
  unfold tailWord_2012703
  simp only [CollatzResearch.WordTrace]
  refine ⟨73409309227328248150786763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48939539484885498767191175 73409309227328248150786763)
  ·
    refine ⟨110113963840992372226180145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73409309227328248150786763 110113963840992372226180145)
    ·
      refine ⟨82585472880744279169635109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110113963840992372226180145 82585472880744279169635109)
      ·
        refine ⟨15484776165139552344306583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82585472880744279169635109 15484776165139552344306583)
        ·
          refine ⟨23227164247709328516459875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484776165139552344306583 23227164247709328516459875)
          ·
            refine ⟨34840746371563992774689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23227164247709328516459875 34840746371563992774689813)
            ·
              refine ⟨1633159986167062161313585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34840746371563992774689813 1633159986167062161313585)
              ·
                refine ⟨1224869989625296620985189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633159986167062161313585 1224869989625296620985189)
                ·
                  refine ⟨229663123054743116434723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224869989625296620985189 229663123054743116434723)
                  ·
                    rfl

theorem cell22_2012703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 4].length) (baseStart_2012703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012703 prefixEnd_2012703 := by exact prefixLift 2012703
  have htrace : WordTrace (prefixWord ++ tailWord_2012703) baseStart_2012703 baseEnd_2012703 := by
    simpa [prefixWord, tailWord_2012703, baseEnd_2012703] using wordTrace_append hprefix tailTrace_2012703
  have hstable : (prefixWord ++ tailWord_2012703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012703).length < 2 ^ (prefixWord ++ tailWord_2012703).sum := by decide
  have hdescent : baseEnd_2012703 < baseStart_2012703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012718 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2012718 : Nat := 118140960795 + 2012718 * 2 ^ 59
def prefixEnd_2012718 : Nat := 4983230072969 + 3 ^ 40 * 2012718 * 2
def baseEnd_2012718 : Nat := 688994503970774310179123

theorem tailTrace_2012718 : CollatzResearch.WordTrace tailWord_2012718 prefixEnd_2012718 688994503970774310179123 := by
  unfold tailWord_2012718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176232040284238214072851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48939904214849270475055205 9176232040284238214072851)
  ·
    refine ⟨13764348060426357321109277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176232040284238214072851 13764348060426357321109277)
    ·
      refine ⟨5161630522659883995415979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13764348060426357321109277 5161630522659883995415979)
      ·
        refine ⟨7742445783989825993123969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161630522659883995415979 7742445783989825993123969)
        ·
          refine ⟨5806834337992369494842977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742445783989825993123969 5806834337992369494842977)
          ·
            refine ⟨4355125753494277121132233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806834337992369494842977 4355125753494277121132233)
            ·
              refine ⟨3266344315120707840849175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355125753494277121132233 3266344315120707840849175)
              ·
                refine ⟨4899516472681061761273763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266344315120707840849175 4899516472681061761273763)
                ·
                  refine ⟨7349274709021592641910645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899516472681061761273763 7349274709021592641910645)
                  ·
                    refine ⟨688994503970774310179123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7349274709021592641910645 688994503970774310179123)
                    ·
                      rfl

theorem cell22_2012718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2012718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012718 prefixEnd_2012718 := by exact prefixLift 2012718
  have htrace : WordTrace (prefixWord ++ tailWord_2012718) baseStart_2012718 baseEnd_2012718 := by
    simpa [prefixWord, tailWord_2012718, baseEnd_2012718] using wordTrace_append hprefix tailTrace_2012718
  have hstable : (prefixWord ++ tailWord_2012718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012718).length < 2 ^ (prefixWord ++ tailWord_2012718).sum := by decide
  have hdescent : baseEnd_2012718 < baseStart_2012718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012746 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_2012746 : Nat := 118140960795 + 2012746 * 2 ^ 59
def prefixEnd_2012746 : Nat := 4983230072969 + 3 ^ 40 * 2012746 * 2
def baseEnd_2012746 : Nat := 689004088942991570479037

theorem tailTrace_2012746 : CollatzResearch.WordTrace tailWord_2012746 prefixEnd_2012746 689004088942991570479037 := by
  unfold tailWord_2012746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352719391543116623650523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48940585044114977663068061 18352719391543116623650523)
  ·
    refine ⟨27529079087314674935475785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352719391543116623650523 27529079087314674935475785)
    ·
      refine ⟨20646809315486006201606839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27529079087314674935475785 20646809315486006201606839)
      ·
        refine ⟨30970213973229009302410259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20646809315486006201606839 30970213973229009302410259)
        ·
          refine ⟨46455320959843513953615389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30970213973229009302410259 46455320959843513953615389)
          ·
            refine ⟨17420745359941317732605771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46455320959843513953615389 17420745359941317732605771)
            ·
              refine ⟨26131118039911976598908657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17420745359941317732605771 26131118039911976598908657)
              ·
                refine ⟨19598338529933982449181493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26131118039911976598908657 19598338529933982449181493)
                ·
                  refine ⟨1837344237181310854610765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19598338529933982449181493 1837344237181310854610765)
                  ·
                    refine ⟨689004088942991570479037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837344237181310854610765 689004088942991570479037)
                    ·
                      rfl

theorem cell22_2012746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_2012746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012746 prefixEnd_2012746 := by exact prefixLift 2012746
  have htrace : WordTrace (prefixWord ++ tailWord_2012746) baseStart_2012746 baseEnd_2012746 := by
    simpa [prefixWord, tailWord_2012746, baseEnd_2012746] using wordTrace_append hprefix tailTrace_2012746
  have hstable : (prefixWord ++ tailWord_2012746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012746).length < 2 ^ (prefixWord ++ tailWord_2012746).sum := by decide
  have hdescent : baseEnd_2012746 < baseStart_2012746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012797 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_2012797 : Nat := 118140960795 + 2012797 * 2 ^ 59
def prefixEnd_2012797 : Nat := 4983230072969 + 3 ^ 40 * 2012797 * 2
def baseEnd_2012797 : Nat := 689021547285244437453881

theorem tailTrace_2012797 : CollatzResearch.WordTrace tailWord_2012797 prefixEnd_2012797 689021547285244437453881 := by
  unfold tailWord_2012797
  simp only [CollatzResearch.WordTrace]
  refine ⟨73412737688987702204708645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48941825125991801469805763 73412737688987702204708645)
  ·
    refine ⟨13764888316685194163382871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73412737688987702204708645 13764888316685194163382871)
    ·
      refine ⟨20647332475027791245074307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13764888316685194163382871 20647332475027791245074307)
      ·
        refine ⟨30970998712541686867611461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20647332475027791245074307 30970998712541686867611461)
        ·
          refine ⟨5807062258601566287677149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30970998712541686867611461 5807062258601566287677149)
          ·
            refine ⟨2177648346975587357878931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5807062258601566287677149 2177648346975587357878931)
            ·
              refine ⟨3266472520463381036818397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177648346975587357878931 3266472520463381036818397)
              ·
                refine ⟨1224927195173767888806899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3266472520463381036818397 1224927195173767888806899)
                ·
                  refine ⟨1837390792760651833210349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224927195173767888806899 1837390792760651833210349)
                  ·
                    refine ⟨689021547285244437453881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837390792760651833210349 689021547285244437453881)
                    ·
                      rfl

theorem cell22_2012797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_2012797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012797 prefixEnd_2012797 := by exact prefixLift 2012797
  have htrace : WordTrace (prefixWord ++ tailWord_2012797) baseStart_2012797 baseEnd_2012797 := by
    simpa [prefixWord, tailWord_2012797, baseEnd_2012797] using wordTrace_append hprefix tailTrace_2012797
  have hstable : (prefixWord ++ tailWord_2012797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012797).length < 2 ^ (prefixWord ++ tailWord_2012797).sum := by decide
  have hdescent : baseEnd_2012797 < baseStart_2012797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012819 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_2012819 : Nat := 118140960795 + 2012819 * 2 ^ 59
def prefixEnd_2012819 : Nat := 4983230072969 + 3 ^ 40 * 2012819 * 2
def baseEnd_2012819 : Nat := 689029078334843713403813

theorem tailTrace_2012819 : CollatzResearch.WordTrace tailWord_2012819 prefixEnd_2012819 689029078334843713403813 := by
  unfold tailWord_2012819
  simp only [CollatzResearch.WordTrace]
  refine ⟨73413540094907999962009511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48942360063271999974673007 73413540094907999962009511)
  ·
    refine ⟨110120310142361999943014267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73413540094907999962009511 110120310142361999943014267)
    ·
      refine ⟨165180465213542999914521401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110120310142361999943014267 165180465213542999914521401)
      ·
        refine ⟨123885348910157249935891051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165180465213542999914521401 123885348910157249935891051)
        ·
          refine ⟨185828023365235874903836577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123885348910157249935891051 185828023365235874903836577)
          ·
            refine ⟨139371017523926906177877433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185828023365235874903836577 139371017523926906177877433)
            ·
              refine ⟨104528263142945179633408075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139371017523926906177877433 104528263142945179633408075)
              ·
                refine ⟨156792394714417769450112113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104528263142945179633408075 156792394714417769450112113)
                ·
                  refine ⟨117594296035813327087584085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156792394714417769450112113 117594296035813327087584085)
                  ·
                    refine ⟨689029078334843713403813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117594296035813327087584085 689029078334843713403813)
                    ·
                      rfl

theorem cell22_2012819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_2012819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012819 prefixEnd_2012819 := by exact prefixLift 2012819
  have htrace : WordTrace (prefixWord ++ tailWord_2012819) baseStart_2012819 baseEnd_2012819 := by
    simpa [prefixWord, tailWord_2012819, baseEnd_2012819] using wordTrace_append hprefix tailTrace_2012819
  have hstable : (prefixWord ++ tailWord_2012819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012819).length < 2 ^ (prefixWord ++ tailWord_2012819).sum := by decide
  have hdescent : baseEnd_2012819 < baseStart_2012819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012868 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2012868 : Nat := 118140960795 + 2012868 * 2 ^ 59
def prefixEnd_2012868 : Nat := 4983230072969 + 3 ^ 40 * 2012868 * 2
def baseEnd_2012868 : Nat := 689045852036223918928663

theorem tailTrace_2012868 : CollatzResearch.WordTrace tailWord_2012868 prefixEnd_2012868 689045852036223918928663 := by
  unfold tailWord_2012868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36707663635865240665271629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48943551514486987553695505 36707663635865240665271629)
  ·
    refine ⟨13765373863449465249476861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36707663635865240665271629 13765373863449465249476861)
    ·
      refine ⟨5162015198793549468553823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13765373863449465249476861 5162015198793549468553823)
      ·
        refine ⟨7743022798190324202830735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162015198793549468553823 7743022798190324202830735)
        ·
          refine ⟨11614534197285486304246103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743022798190324202830735 11614534197285486304246103)
          ·
            refine ⟨17421801295928229456369155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614534197285486304246103 17421801295928229456369155)
            ·
              refine ⟨26132701943892344184553733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421801295928229456369155 26132701943892344184553733)
              ·
                refine ⟨4899881614479814534603825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26132701943892344184553733 4899881614479814534603825)
                ·
                  refine ⟨3674911210859860900952869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4899881614479814534603825 3674911210859860900952869)
                  ·
                    refine ⟨689045852036223918928663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3674911210859860900952869 689045852036223918928663)
                    ·
                      rfl

theorem cell22_2012868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2012868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012868 prefixEnd_2012868 := by exact prefixLift 2012868
  have htrace : WordTrace (prefixWord ++ tailWord_2012868) baseStart_2012868 baseEnd_2012868 := by
    simpa [prefixWord, tailWord_2012868, baseEnd_2012868] using wordTrace_append hprefix tailTrace_2012868
  have hstable : (prefixWord ++ tailWord_2012868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012868).length < 2 ^ (prefixWord ++ tailWord_2012868).sum := by decide
  have hdescent : baseEnd_2012868 < baseStart_2012868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012911 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 7]
def baseStart_2012911 : Nat := 118140960795 + 2012911 * 2 ^ 59
def prefixEnd_2012911 : Nat := 4983230072969 + 3 ^ 40 * 2012911 * 2
def baseEnd_2012911 : Nat := 229686857271662046701177

theorem tailTrace_2012911 : CollatzResearch.WordTrace tailWord_2012911 prefixEnd_2012911 229686857271662046701177 := by
  unfold tailWord_2012911
  simp only [CollatzResearch.WordTrace]
  refine ⟨73416895610574699674358587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48944597073716466449572391 73416895610574699674358587)
  ·
    refine ⟨110125343415862049511537881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73416895610574699674358587 110125343415862049511537881)
    ·
      refine ⟨82594007561896537133653411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110125343415862049511537881 82594007561896537133653411)
      ·
        refine ⟨123891011342844805700480117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82594007561896537133653411 123891011342844805700480117)
        ·
          refine ⟨11614782313391700534420011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123891011342844805700480117 11614782313391700534420011)
          ·
            refine ⟨17422173470087550801630017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614782313391700534420011 17422173470087550801630017)
            ·
              refine ⟨13066630102565663101222513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17422173470087550801630017 13066630102565663101222513)
              ·
                refine ⟨9799972576924247325916885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13066630102565663101222513 9799972576924247325916885)
                ·
                  refine ⟨229686857271662046701177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9799972576924247325916885 229686857271662046701177)
                  ·
                    rfl

theorem cell22_2012911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_2012911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012911 prefixEnd_2012911 := by exact prefixLift 2012911
  have htrace : WordTrace (prefixWord ++ tailWord_2012911) baseStart_2012911 baseEnd_2012911 := by
    simpa [prefixWord, tailWord_2012911, baseEnd_2012911] using wordTrace_append hprefix tailTrace_2012911
  have hstable : (prefixWord ++ tailWord_2012911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012911).length < 2 ^ (prefixWord ++ tailWord_2012911).sum := by decide
  have hdescent : baseEnd_2012911 < baseStart_2012911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012915 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 1, 3]
def baseStart_2012915 : Nat := 118140960795 + 2012915 * 2 ^ 59
def prefixEnd_2012915 : Nat := 4983230072969 + 3 ^ 40 * 2012915 * 2
def baseEnd_2012915 : Nat := 689061941096731463003519

theorem tailTrace_2012915 : CollatzResearch.WordTrace tailWord_2012915 prefixEnd_2012915 689061941096731463003519 := by
  unfold tailWord_2012915
  simp only [CollatzResearch.WordTrace]
  refine ⟨73417041502560208357504199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48944694335040138905002799 73417041502560208357504199)
  ·
    refine ⟨110125562253840312536256299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73417041502560208357504199 110125562253840312536256299)
    ·
      refine ⟨165188343380760468804384449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110125562253840312536256299 165188343380760468804384449)
      ·
        refine ⟨123891257535570351603288337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165188343380760468804384449 123891257535570351603288337)
        ·
          refine ⟨92918443151677763702466253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123891257535570351603288337 92918443151677763702466253)
          ·
            refine ⟨34844416181879161388424845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92918443151677763702466253 34844416181879161388424845)
            ·
              refine ⟨13066656068204685520659317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34844416181879161388424845 13066656068204685520659317)
              ·
                refine ⟨1224999006394189267561811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13066656068204685520659317 1224999006394189267561811)
                ·
                  refine ⟨1837498509591283901342717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224999006394189267561811 1837498509591283901342717)
                  ·
                    refine ⟨689061941096731463003519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837498509591283901342717 689061941096731463003519)
                    ·
                      rfl

theorem cell22_2012915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 3].length) (baseStart_2012915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012915 prefixEnd_2012915 := by exact prefixLift 2012915
  have htrace : WordTrace (prefixWord ++ tailWord_2012915) baseStart_2012915 baseEnd_2012915 := by
    simpa [prefixWord, tailWord_2012915, baseEnd_2012915] using wordTrace_append hprefix tailTrace_2012915
  have hstable : (prefixWord ++ tailWord_2012915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012915).length < 2 ^ (prefixWord ++ tailWord_2012915).sum := by decide
  have hdescent : baseEnd_2012915 < baseStart_2012915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012932 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2012932 : Nat := 118140960795 + 2012932 * 2 ^ 59
def prefixEnd_2012932 : Nat := 4983230072969 + 3 ^ 40 * 2012932 * 2
def baseEnd_2012932 : Nat := 689067760544149085328467

theorem tailTrace_2012932 : CollatzResearch.WordTrace tailWord_2012932 prefixEnd_2012932 689067760544149085328467 := by
  unfold tailWord_2012932
  simp only [CollatzResearch.WordTrace]
  refine ⟨36708830771749310130436525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48945107695665746840582033 36708830771749310130436525)
  ·
    refine ⟨13765811539405991298913697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36708830771749310130436525 13765811539405991298913697)
    ·
      refine ⟨10324358654554493474185273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13765811539405991298913697 10324358654554493474185273)
      ·
        refine ⟨7743268990915870105638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10324358654554493474185273 7743268990915870105638955)
        ·
          refine ⟨11614903486373805158458433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743268990915870105638955 11614903486373805158458433)
          ·
            refine ⟨8711177614780353868843825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11614903486373805158458433 8711177614780353868843825)
            ·
              refine ⟨6533383211085265401632869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8711177614780353868843825 6533383211085265401632869)
              ·
                refine ⟨1225009352078487262806163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6533383211085265401632869 1225009352078487262806163)
                ·
                  refine ⟨1837514028117730894209245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225009352078487262806163 1837514028117730894209245)
                  ·
                    refine ⟨689067760544149085328467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837514028117730894209245 689067760544149085328467)
                    ·
                      rfl

theorem cell22_2012932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2012932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012932 prefixEnd_2012932 := by exact prefixLift 2012932
  have htrace : WordTrace (prefixWord ++ tailWord_2012932) baseStart_2012932 baseEnd_2012932 := by
    simpa [prefixWord, tailWord_2012932, baseEnd_2012932] using wordTrace_append hprefix tailTrace_2012932
  have hstable : (prefixWord ++ tailWord_2012932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012932).length < 2 ^ (prefixWord ++ tailWord_2012932).sum := by decide
  have hdescent : baseEnd_2012932 < baseStart_2012932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012990 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2012990 : Nat := 118140960795 + 2012990 * 2 ^ 59
def prefixEnd_2012990 : Nat := 4983230072969 + 3 ^ 40 * 2012990 * 2
def baseEnd_2012990 : Nat := 229695871709818755792763

theorem tailTrace_2012990 : CollatzResearch.WordTrace tailWord_2012990 prefixEnd_2012990 229695871709818755792763 := by
  unfold tailWord_2012990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177472122161062020810553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48946517984858997444322949 9177472122161062020810553)
  ·
    refine ⟨6883104091620796515607915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9177472122161062020810553 6883104091620796515607915)
    ·
      refine ⟨10324656137431194773411873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883104091620796515607915 10324656137431194773411873)
      ·
        refine ⟨7743492103073396080058905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10324656137431194773411873 7743492103073396080058905)
        ·
          refine ⟨5807619077305047060044179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743492103073396080058905 5807619077305047060044179)
          ·
            refine ⟨8711428615957570590066269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807619077305047060044179 8711428615957570590066269)
            ·
              refine ⟨3266785730984088971274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8711428615957570590066269 3266785730984088971274851)
              ·
                refine ⟨4900178596476133456912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266785730984088971274851 4900178596476133456912277)
                ·
                  refine ⟨229695871709818755792763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4900178596476133456912277 229695871709818755792763)
                  ·
                    rfl

theorem cell22_2012990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2012990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2012990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2012990 prefixEnd_2012990 := by exact prefixLift 2012990
  have htrace : WordTrace (prefixWord ++ tailWord_2012990) baseStart_2012990 baseEnd_2012990 := by
    simpa [prefixWord, tailWord_2012990, baseEnd_2012990] using wordTrace_append hprefix tailTrace_2012990
  have hstable : (prefixWord ++ tailWord_2012990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012990).length < 2 ^ (prefixWord ++ tailWord_2012990).sum := by decide
  have hdescent : baseEnd_2012990 < baseStart_2012990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013084 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2013084 : Nat := 118140960795 + 2013084 * 2 ^ 59
def prefixEnd_2013084 : Nat := 4983230072969 + 3 ^ 40 * 2013084 * 2
def baseEnd_2013084 : Nat := 689119793250471355528001

theorem tailTrace_2013084 : CollatzResearch.WordTrace tailWord_2013084 prefixEnd_2013084 689119793250471355528001 := by
  unfold tailWord_2013084
  simp only [CollatzResearch.WordTrace]
  refine ⟨36711602719473975110203153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48948803625965300146937537 36711602719473975110203153)
  ·
    refine ⟨27533702039605481332652365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36711602719473975110203153 27533702039605481332652365)
    ·
      refine ⟨10325138264852055499744637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27533702039605481332652365 10325138264852055499744637)
      ·
        refine ⟨3871926849319520812404239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325138264852055499744637 3871926849319520812404239)
        ·
          refine ⟨5807890273979281218606359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871926849319520812404239 5807890273979281218606359)
          ·
            refine ⟨8711835410968921827909539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807890273979281218606359 8711835410968921827909539)
            ·
              refine ⟨13067753116453382741864309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711835410968921827909539 13067753116453382741864309)
              ·
                refine ⟨1225101854667504632049779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13067753116453382741864309 1225101854667504632049779)
                ·
                  refine ⟨1837652782001256948074669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225101854667504632049779 1837652782001256948074669)
                  ·
                    refine ⟨689119793250471355528001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837652782001256948074669 689119793250471355528001)
                    ·
                      rfl

theorem cell22_2013084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2013084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013084 prefixEnd_2013084 := by exact prefixLift 2013084
  have htrace : WordTrace (prefixWord ++ tailWord_2013084) baseStart_2013084 baseEnd_2013084 := by
    simpa [prefixWord, tailWord_2013084, baseEnd_2013084] using wordTrace_append hprefix tailTrace_2013084
  have hstable : (prefixWord ++ tailWord_2013084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013084).length < 2 ^ (prefixWord ++ tailWord_2013084).sum := by decide
  have hdescent : baseEnd_2013084 < baseStart_2013084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013095 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2013095 : Nat := 118140960795 + 2013095 * 2 ^ 59
def prefixEnd_2013095 : Nat := 4983230072969 + 3 ^ 40 * 2013095 * 2
def baseEnd_2013095 : Nat := 689123558775270993502967

theorem tailTrace_2013095 : CollatzResearch.WordTrace tailWord_2013095 prefixEnd_2013095 689123558775270993502967 := by
  unfold tailWord_2013095
  simp only [CollatzResearch.WordTrace]
  refine ⟨73423606641908099099056739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48949071094605399399371159 73423606641908099099056739)
  ·
    refine ⟨110135409962862148648585109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73423606641908099099056739 110135409962862148648585109)
    ·
      refine ⟨5162597342009163217902427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110135409962862148648585109 5162597342009163217902427)
      ·
        refine ⟨7743896013013744826853641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162597342009163217902427 7743896013013744826853641)
        ·
          refine ⟨5807922009760308620140231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743896013013744826853641 5807922009760308620140231)
          ·
            refine ⟨8711883014640462930210347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807922009760308620140231 8711883014640462930210347)
            ·
              refine ⟨13067824521960694395315521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711883014640462930210347 13067824521960694395315521)
              ·
                refine ⟨9800868391470520796486641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13067824521960694395315521 9800868391470520796486641)
                ·
                  refine ⟨7350651293602890597364981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800868391470520796486641 7350651293602890597364981)
                  ·
                    refine ⟨689123558775270993502967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7350651293602890597364981 689123558775270993502967)
                    ·
                      rfl

theorem cell22_2013095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2013095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013095 prefixEnd_2013095 := by exact prefixLift 2013095
  have htrace : WordTrace (prefixWord ++ tailWord_2013095) baseStart_2013095 baseEnd_2013095 := by
    simpa [prefixWord, tailWord_2013095, baseEnd_2013095] using wordTrace_append hprefix tailTrace_2013095
  have hstable : (prefixWord ++ tailWord_2013095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013095).length < 2 ^ (prefixWord ++ tailWord_2013095).sum := by decide
  have hdescent : baseEnd_2013095 < baseStart_2013095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013140 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2013140 : Nat := 118140960795 + 2013140 * 2 ^ 59
def prefixEnd_2013140 : Nat := 4983230072969 + 3 ^ 40 * 2013140 * 2
def baseEnd_2013140 : Nat := 689138963194905876127829

theorem tailTrace_2013140 : CollatzResearch.WordTrace tailWord_2013140 prefixEnd_2013140 689138963194905876127829 := by
  unfold tailWord_2013140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36712623963372535892222437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48950165284496714522963249 36712623963372535892222437)
  ·
    refine ⟨6883616993132350479791707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36712623963372535892222437 6883616993132350479791707)
    ·
      refine ⟨10325425489698525719687561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883616993132350479791707 10325425489698525719687561)
      ·
        refine ⟨7744069117273894289765671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10325425489698525719687561 7744069117273894289765671)
        ·
          refine ⟨11616103675910841434648507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744069117273894289765671 11616103675910841434648507)
          ·
            refine ⟨17424155513866262151972761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616103675910841434648507 17424155513866262151972761)
            ·
              refine ⟨13068116635399696613979571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424155513866262151972761 13068116635399696613979571)
              ·
                refine ⟨19602174953099544920969357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068116635399696613979571 19602174953099544920969357)
                ·
                  refine ⟨7350815607412329345363509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19602174953099544920969357 7350815607412329345363509)
                  ·
                    refine ⟨689138963194905876127829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7350815607412329345363509 689138963194905876127829)
                    ·
                      rfl

theorem cell22_2013140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2013140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013140 prefixEnd_2013140 := by exact prefixLift 2013140
  have htrace : WordTrace (prefixWord ++ tailWord_2013140) baseStart_2013140 baseEnd_2013140 := by
    simpa [prefixWord, tailWord_2013140, baseEnd_2013140] using wordTrace_append hprefix tailTrace_2013140
  have hstable : (prefixWord ++ tailWord_2013140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013140).length < 2 ^ (prefixWord ++ tailWord_2013140).sum := by decide
  have hdescent : baseEnd_2013140 < baseStart_2013140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013153 : List Nat := [1, 2, 3, 1, 2, 1, 12]
def baseStart_2013153 : Nat := 118140960795 + 2013153 * 2 ^ 59
def prefixEnd_2013153 : Nat := 4983230072969 + 3 ^ 40 * 2013153 * 2
def baseEnd_2013153 : Nat := 25523830124465858353807

theorem tailTrace_2013153 : CollatzResearch.WordTrace tailWord_2013153 prefixEnd_2013153 25523830124465858353807 := by
  unfold tailWord_2013153
  simp only [CollatzResearch.WordTrace]
  refine ⟨73425722075697975004668113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48950481383798650003112075 73425722075697975004668113)
  ·
    refine ⟨55069291556773481253501085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73425722075697975004668113 55069291556773481253501085)
    ·
      refine ⟨20650984333790055470062907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55069291556773481253501085 20650984333790055470062907)
      ·
        refine ⟨30976476500685083205094361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650984333790055470062907 30976476500685083205094361)
        ·
          refine ⟨23232357375513812403820771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30976476500685083205094361 23232357375513812403820771)
          ·
            refine ⟨34848536063270718605731157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23232357375513812403820771 34848536063270718605731157)
            ·
              refine ⟨25523830124465858353807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34848536063270718605731157 25523830124465858353807)
              ·
                rfl

theorem cell22_2013153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 12].length) (baseStart_2013153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013153 prefixEnd_2013153 := by exact prefixLift 2013153
  have htrace : WordTrace (prefixWord ++ tailWord_2013153) baseStart_2013153 baseEnd_2013153 := by
    simpa [prefixWord, tailWord_2013153, baseEnd_2013153] using wordTrace_append hprefix tailTrace_2013153
  have hstable : (prefixWord ++ tailWord_2013153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013153).length < 2 ^ (prefixWord ++ tailWord_2013153).sum := by decide
  have hdescent : baseEnd_2013153 < baseStart_2013153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013155 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_2013155 : Nat := 118140960795 + 2013155 * 2 ^ 59
def prefixEnd_2013155 : Nat := 4983230072969 + 3 ^ 40 * 2013155 * 2
def baseEnd_2013155 : Nat := 689144098001450837002783

theorem tailTrace_2013155 : CollatzResearch.WordTrace tailWord_2013155 prefixEnd_2013155 689144098001450837002783 := by
  unfold tailWord_2013155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73425795021690729346240919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48950530014460486230827279 73425795021690729346240919)
  ·
    refine ⟨110138692532536094019361379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73425795021690729346240919 110138692532536094019361379)
    ·
      refine ⟨165208038798804141029042069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110138692532536094019361379 165208038798804141029042069)
      ·
        refine ⟨7744126818693944110736347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165208038798804141029042069 7744126818693944110736347)
        ·
          refine ⟨11616190228040916166104521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744126818693944110736347 11616190228040916166104521)
          ·
            refine ⟨8712142671030687124578391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616190228040916166104521 8712142671030687124578391)
            ·
              refine ⟨13068214006546030686867587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712142671030687124578391 13068214006546030686867587)
              ·
                refine ⟨19602321009819046030301381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068214006546030686867587 19602321009819046030301381)
                ·
                  refine ⟨3675435189341071130681509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19602321009819046030301381 3675435189341071130681509)
                  ·
                    refine ⟨689144098001450837002783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675435189341071130681509 689144098001450837002783)
                    ·
                      rfl

theorem cell22_2013155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_2013155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013155 prefixEnd_2013155 := by exact prefixLift 2013155
  have htrace : WordTrace (prefixWord ++ tailWord_2013155) baseStart_2013155 baseEnd_2013155 := by
    simpa [prefixWord, tailWord_2013155, baseEnd_2013155] using wordTrace_append hprefix tailTrace_2013155
  have hstable : (prefixWord ++ tailWord_2013155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013155).length < 2 ^ (prefixWord ++ tailWord_2013155).sum := by decide
  have hdescent : baseEnd_2013155 < baseStart_2013155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013159 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 6]
def baseStart_2013159 : Nat := 118140960795 + 2013159 * 2 ^ 59
def prefixEnd_2013159 : Nat := 4983230072969 + 3 ^ 40 * 2013159 * 2
def baseEnd_2013159 : Nat := 229715155761065386634257

theorem tailTrace_2013159 : CollatzResearch.WordTrace tailWord_2013159 prefixEnd_2013159 229715155761065386634257 := by
  unfold tailWord_2013159
  simp only [CollatzResearch.WordTrace]
  refine ⟨73425940913676238029386531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48950627275784158686257687 73425940913676238029386531)
  ·
    refine ⟨110138911370514357044079797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73425940913676238029386531 110138911370514357044079797)
    ·
      refine ⟨10325522940985720972882481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110138911370514357044079797 10325522940985720972882481)
      ·
        refine ⟨7744142205739290729661861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10325522940985720972882481 7744142205739290729661861)
        ·
          refine ⟨1452026663576117011811599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7744142205739290729661861 1452026663576117011811599)
          ·
            refine ⟨2178039995364175517717399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452026663576117011811599 2178039995364175517717399)
            ·
              refine ⟨3267059993046263276576099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178039995364175517717399 3267059993046263276576099)
              ·
                refine ⟨4900589989569394914864149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267059993046263276576099 4900589989569394914864149)
                ·
                  refine ⟨229715155761065386634257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4900589989569394914864149 229715155761065386634257)
                  ·
                    rfl

theorem cell22_2013159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 6].length) (baseStart_2013159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013159 prefixEnd_2013159 := by exact prefixLift 2013159
  have htrace : WordTrace (prefixWord ++ tailWord_2013159) baseStart_2013159 baseEnd_2013159 := by
    simpa [prefixWord, tailWord_2013159, baseEnd_2013159] using wordTrace_append hprefix tailTrace_2013159
  have hstable : (prefixWord ++ tailWord_2013159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013159).length < 2 ^ (prefixWord ++ tailWord_2013159).sum := by decide
  have hdescent : baseEnd_2013159 < baseStart_2013159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013204 : List Nat := [2, 4, 3, 2, 2, 9]
def baseStart_2013204 : Nat := 118140960795 + 2013204 * 2 ^ 59
def prefixEnd_2013204 : Nat := 4983230072969 + 3 ^ 40 * 2013204 * 2
def baseEnd_2013204 : Nat := 8508158909911494352193

theorem tailTrace_2013204 : CollatzResearch.WordTrace tailWord_2013204 prefixEnd_2013204 8508158909911494352193 := by
  unfold tailWord_2013204
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713791099256605357387333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48951721465675473809849777 36713791099256605357387333)
  ·
    refine ⟨6883835831110613504510125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36713791099256605357387333 6883835831110613504510125)
    ·
      refine ⟨2581438436666480064191297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6883835831110613504510125 2581438436666480064191297)
      ·
        refine ⟨1936078827499860048143473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581438436666480064191297 1936078827499860048143473)
        ·
          refine ⟨1452059120624895036107605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936078827499860048143473 1452059120624895036107605)
          ·
            refine ⟨8508158909911494352193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1452059120624895036107605 8508158909911494352193)
            ·
              rfl

theorem cell22_2013204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 9].length) (baseStart_2013204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013204 prefixEnd_2013204 := by exact prefixLift 2013204
  have htrace : WordTrace (prefixWord ++ tailWord_2013204) baseStart_2013204 baseEnd_2013204 := by
    simpa [prefixWord, tailWord_2013204, baseEnd_2013204] using wordTrace_append hprefix tailTrace_2013204
  have hstable : (prefixWord ++ tailWord_2013204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013204).length < 2 ^ (prefixWord ++ tailWord_2013204).sum := by decide
  have hdescent : baseEnd_2013204 < baseStart_2013204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013219 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 1, 3]
def baseStart_2013219 : Nat := 118140960795 + 2013219 * 2 ^ 59
def prefixEnd_2013219 : Nat := 4983230072969 + 3 ^ 40 * 2013219 * 2
def baseEnd_2013219 : Nat := 689166006509376003402587

theorem tailTrace_2013219 : CollatzResearch.WordTrace tailWord_2013219 prefixEnd_2013219 689166006509376003402587 := by
  unfold tailWord_2013219
  simp only [CollatzResearch.WordTrace]
  refine ⟨73428129293458868276570711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48952086195639245517713807 73428129293458868276570711)
  ·
    refine ⟨110142193940188302414856067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73428129293458868276570711 110142193940188302414856067)
    ·
      refine ⟨165213290910282453622284101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110142193940188302414856067 165213290910282453622284101)
      ·
        refine ⟨30977492045677960054178269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165213290910282453622284101 30977492045677960054178269)
        ·
          refine ⟨11616559517129235020316851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30977492045677960054178269 11616559517129235020316851)
          ·
            refine ⟨17424839275693852530475277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616559517129235020316851 17424839275693852530475277)
            ·
              refine ⟨6534314728385194698928229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17424839275693852530475277 6534314728385194698928229)
              ·
                refine ⟨1225184011572224006049043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6534314728385194698928229 1225184011572224006049043)
                ·
                  refine ⟨1837776017358336009073565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225184011572224006049043 1837776017358336009073565)
                  ·
                    refine ⟨689166006509376003402587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837776017358336009073565 689166006509376003402587)
                    ·
                      rfl

theorem cell22_2013219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 3].length) (baseStart_2013219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013219 prefixEnd_2013219 := by exact prefixLift 2013219
  have htrace : WordTrace (prefixWord ++ tailWord_2013219) baseStart_2013219 baseEnd_2013219 := by
    simpa [prefixWord, tailWord_2013219, baseEnd_2013219] using wordTrace_append hprefix tailTrace_2013219
  have hstable : (prefixWord ++ tailWord_2013219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013219).length < 2 ^ (prefixWord ++ tailWord_2013219).sum := by decide
  have hdescent : baseEnd_2013219 < baseStart_2013219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013236 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2013236 : Nat := 118140960795 + 2013236 * 2 ^ 59
def prefixEnd_2013236 : Nat := 4983230072969 + 3 ^ 40 * 2013236 * 2
def baseEnd_2013236 : Nat := 689171825956793625727535

theorem tailTrace_2013236 : CollatzResearch.WordTrace tailWord_2013236 prefixEnd_2013236 689171825956793625727535 := by
  unfold tailWord_2013236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36714374667198640089969781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48952499556264853453293041 36714374667198640089969781)
  ·
    refine ⟨3441972625049872508434667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36714374667198640089969781 3441972625049872508434667)
    ·
      refine ⟨5162958937574808762652001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441972625049872508434667 5162958937574808762652001)
      ·
        refine ⟨3872219203181106571989001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162958937574808762652001 3872219203181106571989001)
        ·
          refine ⟨2904164402385829928991751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872219203181106571989001 2904164402385829928991751)
          ·
            refine ⟨4356246603578744893487627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904164402385829928991751 4356246603578744893487627)
            ·
              refine ⟨6534369905368117340231441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356246603578744893487627 6534369905368117340231441)
              ·
                refine ⟨4900777429026088005173581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534369905368117340231441 4900777429026088005173581)
                ·
                  refine ⟨1837791535884783001940093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4900777429026088005173581 1837791535884783001940093)
                  ·
                    refine ⟨689171825956793625727535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837791535884783001940093 689171825956793625727535)
                    ·
                      rfl

theorem cell22_2013236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2013236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013236 prefixEnd_2013236 := by exact prefixLift 2013236
  have htrace : WordTrace (prefixWord ++ tailWord_2013236) baseStart_2013236 baseEnd_2013236 := by
    simpa [prefixWord, tailWord_2013236, baseEnd_2013236] using wordTrace_append hprefix tailTrace_2013236
  have hstable : (prefixWord ++ tailWord_2013236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013236).length < 2 ^ (prefixWord ++ tailWord_2013236).sum := by decide
  have hdescent : baseEnd_2013236 < baseStart_2013236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013266 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_2013266 : Nat := 118140960795 + 2013266 * 2 ^ 59
def prefixEnd_2013266 : Nat := 4983230072969 + 3 ^ 40 * 2013266 * 2
def baseEnd_2013266 : Nat := 229727365189961182492481

theorem tailTrace_2013266 : CollatzResearch.WordTrace tailWord_2013266 prefixEnd_2013266 229727365189961182492481 := by
  unfold tailWord_2013266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357460881072148825882913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48953229016192396869021101 18357460881072148825882913)
  ·
    refine ⟨13768095660804111619412185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18357460881072148825882913 13768095660804111619412185)
    ·
      refine ⟨10326071745603083714559139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13768095660804111619412185 10326071745603083714559139)
      ·
        refine ⟨15489107618404625571838709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326071745603083714559139 15489107618404625571838709)
        ·
          refine ⟨1452103839225433647359879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15489107618404625571838709 1452103839225433647359879)
          ·
            refine ⟨2178155758838150471039819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452103839225433647359879 2178155758838150471039819)
            ·
              refine ⟨3267233638257225706559729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178155758838150471039819 3267233638257225706559729)
              ·
                refine ⟨2450425228692919279919797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267233638257225706559729 2450425228692919279919797)
                ·
                  refine ⟨229727365189961182492481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450425228692919279919797 229727365189961182492481)
                  ·
                    rfl

theorem cell22_2013266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_2013266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013266 prefixEnd_2013266 := by exact prefixLift 2013266
  have htrace : WordTrace (prefixWord ++ tailWord_2013266) baseStart_2013266 baseEnd_2013266 := by
    simpa [prefixWord, tailWord_2013266, baseEnd_2013266] using wordTrace_append hprefix tailTrace_2013266
  have hstable : (prefixWord ++ tailWord_2013266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013266).length < 2 ^ (prefixWord ++ tailWord_2013266).sum := by decide
  have hdescent : baseEnd_2013266 < baseStart_2013266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013292 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_2013292 : Nat := 118140960795 + 2013292 * 2 ^ 59
def prefixEnd_2013292 : Nat := 4983230072969 + 3 ^ 40 * 2013292 * 2
def baseEnd_2013292 : Nat := 689190995901228146327363

theorem tailTrace_2013292 : CollatzResearch.WordTrace tailWord_2013292 prefixEnd_2013292 689190995901228146327363 := by
  unfold tailWord_2013292
  simp only [CollatzResearch.WordTrace]
  refine ⟨36715395911097200871989065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48953861214796267829318753 36715395911097200871989065)
  ·
    refine ⟨27536546933322900653991799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36715395911097200871989065 27536546933322900653991799)
    ·
      refine ⟨41304820399984350980987699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27536546933322900653991799 41304820399984350980987699)
      ·
        refine ⟨61957230599976526471481549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41304820399984350980987699 61957230599976526471481549)
        ·
          refine ⟨23233961474991197426805581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61957230599976526471481549 23233961474991197426805581)
          ·
            refine ⟨8712735553121699035052093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23233961474991197426805581 8712735553121699035052093)
            ·
              refine ⟨3267275832420637138144535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8712735553121699035052093 3267275832420637138144535)
              ·
                refine ⟨4900913748630955707216803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267275832420637138144535 4900913748630955707216803)
                ·
                  refine ⟨7351370622946433560825205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900913748630955707216803 7351370622946433560825205)
                  ·
                    refine ⟨689190995901228146327363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351370622946433560825205 689190995901228146327363)
                    ·
                      rfl

theorem cell22_2013292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_2013292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013292 prefixEnd_2013292 := by exact prefixLift 2013292
  have htrace : WordTrace (prefixWord ++ tailWord_2013292) baseStart_2013292 baseEnd_2013292 := by
    simpa [prefixWord, tailWord_2013292, baseEnd_2013292] using wordTrace_append hprefix tailTrace_2013292
  have hstable : (prefixWord ++ tailWord_2013292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013292).length < 2 ^ (prefixWord ++ tailWord_2013292).sum := by decide
  have hdescent : baseEnd_2013292 < baseStart_2013292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013322 : List Nat := [3, 1, 2, 3, 1, 4, 8]
def baseStart_2013322 : Nat := 118140960795 + 2013322 * 2 ^ 59
def prefixEnd_2013322 : Nat := 4983230072969 + 3 ^ 40 * 2013322 * 2
def baseEnd_2013322 : Nat := 25525972796826595113973

theorem tailTrace_2013322 : CollatzResearch.WordTrace tailWord_2013322 prefixEnd_2013322 25525972796826595113973 := by
  unfold tailWord_2013322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357971503021429216892555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48954590674723811245046813 18357971503021429216892555)
  ·
    refine ⟨27536957254532143825338833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18357971503021429216892555 27536957254532143825338833)
    ·
      refine ⟨20652717940899107869004125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27536957254532143825338833 20652717940899107869004125)
      ·
        refine ⟨7744769227837165450876547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20652717940899107869004125 7744769227837165450876547)
        ·
          refine ⟨11617153841755748176314821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744769227837165450876547 11617153841755748176314821)
          ·
            refine ⟨2178216345329202783059029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11617153841755748176314821 2178216345329202783059029)
            ·
              refine ⟨25525972796826595113973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2178216345329202783059029 25525972796826595113973)
              ·
                rfl

theorem cell22_2013322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 8].length) (baseStart_2013322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013322 prefixEnd_2013322 := by exact prefixLift 2013322
  have htrace : WordTrace (prefixWord ++ tailWord_2013322) baseStart_2013322 baseEnd_2013322 := by
    simpa [prefixWord, tailWord_2013322, baseEnd_2013322] using wordTrace_append hprefix tailTrace_2013322
  have hstable : (prefixWord ++ tailWord_2013322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013322).length < 2 ^ (prefixWord ++ tailWord_2013322).sum := by decide
  have hdescent : baseEnd_2013322 < baseStart_2013322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013334 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2013334 : Nat := 118140960795 + 2013334 * 2 ^ 59
def prefixEnd_2013334 : Nat := 4983230072969 + 3 ^ 40 * 2013334 * 2
def baseEnd_2013334 : Nat := 229735124453184678925745

theorem tailTrace_2013334 : CollatzResearch.WordTrace tailWord_2013334 prefixEnd_2013334 229735124453184678925745 := by
  unfold tailWord_2013334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589520230502640182312941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48954882458694828611338037 4589520230502640182312941)
  ·
    refine ⟨1721070086438490068367353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4589520230502640182312941 1721070086438490068367353)
    ·
      refine ⟨1290802564828867551275515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1721070086438490068367353 1290802564828867551275515)
      ·
        refine ⟨1936203847243301326913273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290802564828867551275515 1936203847243301326913273)
        ·
          refine ⟨1452152885432475995184955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936203847243301326913273 1452152885432475995184955)
          ·
            refine ⟨2178229328148713992777433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452152885432475995184955 2178229328148713992777433)
            ·
              refine ⟨1633671996111535494583075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178229328148713992777433 1633671996111535494583075)
              ·
                refine ⟨2450507994167303241874613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633671996111535494583075 2450507994167303241874613)
                ·
                  refine ⟨229735124453184678925745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450507994167303241874613 229735124453184678925745)
                  ·
                    rfl

theorem cell22_2013334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2013334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013334 prefixEnd_2013334 := by exact prefixLift 2013334
  have htrace : WordTrace (prefixWord ++ tailWord_2013334) baseStart_2013334 baseEnd_2013334 := by
    simpa [prefixWord, tailWord_2013334, baseEnd_2013334] using wordTrace_append hprefix tailTrace_2013334
  have hstable : (prefixWord ++ tailWord_2013334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013334).length < 2 ^ (prefixWord ++ tailWord_2013334).sum := by decide
  have hdescent : baseEnd_2013334 < baseStart_2013334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013343 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 2, 3]
def baseStart_2013343 : Nat := 118140960795 + 2013343 * 2 ^ 59
def prefixEnd_2013343 : Nat := 4983230072969 + 3 ^ 40 * 2013343 * 2
def baseEnd_2013343 : Nat := 689208454243481013302207

theorem tailTrace_2013343 : CollatzResearch.WordTrace tailWord_2013343 prefixEnd_2013343 689208454243481013302207 := by
  unfold tailWord_2013343
  simp only [CollatzResearch.WordTrace]
  refine ⟨73432651945009637454084683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48955101296673091636056455 73432651945009637454084683)
  ·
    refine ⟨110148977917514456181127025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73432651945009637454084683 110148977917514456181127025)
    ·
      refine ⟨82611733438135842135845269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110148977917514456181127025 82611733438135842135845269)
      ·
        refine ⟨3872425004912617600117747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82611733438135842135845269 3872425004912617600117747)
        ·
          refine ⟨5808637507368926400176621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872425004912617600117747 5808637507368926400176621)
          ·
            refine ⟨2178239065263347400066233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5808637507368926400176621 2178239065263347400066233)
            ·
              refine ⟨1633679298947510550049675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178239065263347400066233 1633679298947510550049675)
              ·
                refine ⟨2450518948421265825074513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633679298947510550049675 2450518948421265825074513)
                ·
                  refine ⟨1837889211315949368805885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2450518948421265825074513 1837889211315949368805885)
                  ·
                    refine ⟨689208454243481013302207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837889211315949368805885 689208454243481013302207)
                    ·
                      rfl

theorem cell22_2013343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_2013343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013343 prefixEnd_2013343 := by exact prefixLift 2013343
  have htrace : WordTrace (prefixWord ++ tailWord_2013343) baseStart_2013343 baseEnd_2013343 := by
    simpa [prefixWord, tailWord_2013343, baseEnd_2013343] using wordTrace_append hprefix tailTrace_2013343
  have hstable : (prefixWord ++ tailWord_2013343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013343).length < 2 ^ (prefixWord ++ tailWord_2013343).sum := by decide
  have hdescent : baseEnd_2013343 < baseStart_2013343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013358 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2013358 : Nat := 118140960795 + 2013358 * 2 ^ 59
def prefixEnd_2013358 : Nat := 4983230072969 + 3 ^ 40 * 2013358 * 2
def baseEnd_2013358 : Nat := 689213589050025974177161

theorem tailTrace_2013358 : CollatzResearch.WordTrace tailWord_2013358 prefixEnd_2013358 689213589050025974177161 := by
  unfold tailWord_2013358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179149879994411876985091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48955466026636863343920485 9179149879994411876985091)
  ·
    refine ⟨13768724819991617815477637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179149879994411876985091 13768724819991617815477637)
    ·
      refine ⟨2581635903748428340402057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13768724819991617815477637 2581635903748428340402057)
      ·
        refine ⟨1936226927811321255301543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581635903748428340402057 1936226927811321255301543)
        ·
          refine ⟨2904340391716981882952315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936226927811321255301543 2904340391716981882952315)
          ·
            refine ⟨4356510587575472824428473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904340391716981882952315 4356510587575472824428473)
            ·
              refine ⟨3267382940681604618321355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356510587575472824428473 3267382940681604618321355)
              ·
                refine ⟨4901074411022406927482033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267382940681604618321355 4901074411022406927482033)
                ·
                  refine ⟨3675805808266805195611525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4901074411022406927482033 3675805808266805195611525)
                  ·
                    refine ⟨689213589050025974177161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3675805808266805195611525 689213589050025974177161)
                    ·
                      rfl

theorem cell22_2013358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2013358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013358 prefixEnd_2013358 := by exact prefixLift 2013358
  have htrace : WordTrace (prefixWord ++ tailWord_2013358) baseStart_2013358 baseEnd_2013358 := by
    simpa [prefixWord, tailWord_2013358, baseEnd_2013358] using wordTrace_append hprefix tailTrace_2013358
  have hstable : (prefixWord ++ tailWord_2013358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013358).length < 2 ^ (prefixWord ++ tailWord_2013358).sum := by decide
  have hdescent : baseEnd_2013358 < baseStart_2013358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013427 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_2013427 : Nat := 118140960795 + 2013427 * 2 ^ 59
def prefixEnd_2013427 : Nat := 4983230072969 + 3 ^ 40 * 2013427 * 2
def baseEnd_2013427 : Nat := 689237209160132794201949

theorem tailTrace_2013427 : CollatzResearch.WordTrace tailWord_2013427 prefixEnd_2013427 689237209160132794201949 := by
  unfold tailWord_2013427
  simp only [CollatzResearch.WordTrace]
  refine ⟨73435715676705319800142535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48957143784470213200095023 73435715676705319800142535)
  ·
    refine ⟨110153573515057979700213803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73435715676705319800142535 110153573515057979700213803)
    ·
      refine ⟨165230360272586969550320705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110153573515057979700213803 165230360272586969550320705)
      ·
        refine ⟨123922770204440227162740529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165230360272586969550320705 123922770204440227162740529)
        ·
          refine ⟨92942077653330170372055397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123922770204440227162740529 92942077653330170372055397)
          ·
            refine ⟨17426639559999406944760387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92942077653330170372055397 17426639559999406944760387)
            ·
              refine ⟨26139959339999110417140581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426639559999406944760387 26139959339999110417140581)
              ·
                refine ⟨4901242376249833203213859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26139959339999110417140581 4901242376249833203213859)
                ·
                  refine ⟨7351863564374749804820789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901242376249833203213859 7351863564374749804820789)
                  ·
                    refine ⟨689237209160132794201949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351863564374749804820789 689237209160132794201949)
                    ·
                      rfl

theorem cell22_2013427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_2013427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013427 prefixEnd_2013427 := by exact prefixLift 2013427
  have htrace : WordTrace (prefixWord ++ tailWord_2013427) baseStart_2013427 baseEnd_2013427 := by
    simpa [prefixWord, tailWord_2013427, baseEnd_2013427] using wordTrace_append hprefix tailTrace_2013427
  have hstable : (prefixWord ++ tailWord_2013427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013427).length < 2 ^ (prefixWord ++ tailWord_2013427).sum := by decide
  have hdescent : baseEnd_2013427 < baseStart_2013427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013474 : List Nat := [3, 3, 1, 1, 3, 2, 1, 8]
def baseStart_2013474 : Nat := 118140960795 + 2013474 * 2 ^ 59
def prefixEnd_2013474 : Nat := 4983230072969 + 3 ^ 40 * 2013474 * 2
def baseEnd_2013474 : Nat := 76583699802293370919645

theorem tailTrace_2013474 : CollatzResearch.WordTrace tailWord_2013474 prefixEnd_2013474 76583699802293370919645 := by
  unfold tailWord_2013474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359357476883761706775869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48958286605023364551402317 18359357476883761706775869)
  ·
    refine ⟨6884759053831410640040951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18359357476883761706775869 6884759053831410640040951)
    ·
      refine ⟨10327138580747115960061427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884759053831410640040951 10327138580747115960061427)
      ·
        refine ⟨15490707871120673940092141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327138580747115960061427 15490707871120673940092141)
        ·
          refine ⟨5809015451670252727534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15490707871120673940092141 5809015451670252727534553)
          ·
            refine ⟨4356761588752689545650915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5809015451670252727534553 4356761588752689545650915)
            ·
              refine ⟨6535142383129034318476373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356761588752689545650915 6535142383129034318476373)
              ·
                refine ⟨76583699802293370919645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6535142383129034318476373 76583699802293370919645)
                ·
                  rfl

theorem cell22_2013474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_2013474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013474 prefixEnd_2013474 := by exact prefixLift 2013474
  have htrace : WordTrace (prefixWord ++ tailWord_2013474) baseStart_2013474 baseEnd_2013474 := by
    simpa [prefixWord, tailWord_2013474, baseEnd_2013474] using wordTrace_append hprefix tailTrace_2013474
  have hstable : (prefixWord ++ tailWord_2013474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013474).length < 2 ^ (prefixWord ++ tailWord_2013474).sum := by decide
  have hdescent : baseEnd_2013474 < baseStart_2013474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013480 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_2013480 : Nat := 118140960795 + 2013480 * 2 ^ 59
def prefixEnd_2013480 : Nat := 4983230072969 + 3 ^ 40 * 2013480 * 2
def baseEnd_2013480 : Nat := 229751784047752774208929

theorem tailTrace_2013480 : CollatzResearch.WordTrace tailWord_2013480 prefixEnd_2013480 229751784047752774208929 := by
  unfold tailWord_2013480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718824372756654925910947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48958432497008873234547929 36718824372756654925910947)
  ·
    refine ⟨55078236559134982388866421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36718824372756654925910947 55078236559134982388866421)
    ·
      refine ⟨5163584677418904598956227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55078236559134982388866421 5163584677418904598956227)
      ·
        refine ⟨7745377016128356898434341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163584677418904598956227 7745377016128356898434341)
        ·
          refine ⟨1452258190524066918456439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7745377016128356898434341 1452258190524066918456439)
          ·
            refine ⟨2178387285786100377684659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452258190524066918456439 2178387285786100377684659)
            ·
              refine ⟨3267580928679150566526989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178387285786100377684659 3267580928679150566526989)
              ·
                refine ⟨1225342848254681462447621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267580928679150566526989 1225342848254681462447621)
                ·
                  refine ⟨229751784047752774208929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225342848254681462447621 229751784047752774208929)
                  ·
                    rfl

theorem cell22_2013480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_2013480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013480 prefixEnd_2013480 := by exact prefixLift 2013480
  have htrace : WordTrace (prefixWord ++ tailWord_2013480) baseStart_2013480 baseEnd_2013480 := by
    simpa [prefixWord, tailWord_2013480, baseEnd_2013480] using wordTrace_append hprefix tailTrace_2013480
  have hstable : (prefixWord ++ tailWord_2013480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013480).length < 2 ^ (prefixWord ++ tailWord_2013480).sum := by decide
  have hdescent : baseEnd_2013480 < baseStart_2013480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013547 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 8]
def baseStart_2013547 : Nat := 118140960795 + 2013547 * 2 ^ 59
def prefixEnd_2013547 : Nat := 4983230072969 + 3 ^ 40 * 2013547 * 2
def baseEnd_2013547 : Nat := 229759429204164160400527

theorem tailTrace_2013547 : CollatzResearch.WordTrace tailWord_2013547 prefixEnd_2013547 229759429204164160400527 := by
  unfold tailWord_2013547
  simp only [CollatzResearch.WordTrace]
  refine ⟨73440092436270580294510895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48960061624180386863007263 73440092436270580294510895)
  ·
    refine ⟨110160138654405870441766343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73440092436270580294510895 110160138654405870441766343)
    ·
      refine ⟨165240207981608805662649515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110160138654405870441766343 165240207981608805662649515)
      ·
        refine ⟨247860311972413208493974273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165240207981608805662649515 247860311972413208493974273)
        ·
          refine ⟨185895233979309906370480705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247860311972413208493974273 185895233979309906370480705)
          ·
            refine ⟨139421425484482429777860529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185895233979309906370480705 139421425484482429777860529)
            ·
              refine ⟨104566069113361822333395397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139421425484482429777860529 104566069113361822333395397)
              ·
                refine ⟨19606137958755341687511637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104566069113361822333395397 19606137958755341687511637)
                ·
                  refine ⟨229759429204164160400527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19606137958755341687511637 229759429204164160400527)
                  ·
                    rfl

theorem cell22_2013547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_2013547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013547 prefixEnd_2013547 := by exact prefixLift 2013547
  have htrace : WordTrace (prefixWord ++ tailWord_2013547) baseStart_2013547 baseEnd_2013547 := by
    simpa [prefixWord, tailWord_2013547, baseEnd_2013547] using wordTrace_append hprefix tailTrace_2013547
  have hstable : (prefixWord ++ tailWord_2013547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013547).length < 2 ^ (prefixWord ++ tailWord_2013547).sum := by decide
  have hdescent : baseEnd_2013547 < baseStart_2013547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013557 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2013557 : Nat := 118140960795 + 2013557 * 2 ^ 59
def prefixEnd_2013557 : Nat := 4983230072969 + 3 ^ 40 * 2013557 * 2
def baseEnd_2013557 : Nat := 689281710816855788451551

theorem tailTrace_2013557 : CollatzResearch.WordTrace tailWord_2013557 prefixEnd_2013557 689281710816855788451551 := by
  unfold tailWord_2013557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73440457166234352002374925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48960304777489568001583283 73440457166234352002374925)
  ·
    refine ⟨27540171437337882000890597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73440457166234352002374925 27540171437337882000890597)
    ·
      refine ⟨5163782144500852875166987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27540171437337882000890597 5163782144500852875166987)
      ·
        refine ⟨7745673216751279312750481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163782144500852875166987 7745673216751279312750481)
        ·
          refine ⟨5809254912563459484562861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7745673216751279312750481 5809254912563459484562861)
          ·
            refine ⟨2178470592211297306711073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5809254912563459484562861 2178470592211297306711073)
            ·
              refine ⟨1633852944158472980033305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178470592211297306711073 1633852944158472980033305)
              ·
                refine ⟨1225389708118854735024979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633852944158472980033305 1225389708118854735024979)
                ·
                  refine ⟨1838084562178282102537469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225389708118854735024979 1838084562178282102537469)
                  ·
                    refine ⟨689281710816855788451551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838084562178282102537469 689281710816855788451551)
                    ·
                      rfl

theorem cell22_2013557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2013557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013557 prefixEnd_2013557 := by exact prefixLift 2013557
  have htrace : WordTrace (prefixWord ++ tailWord_2013557) baseStart_2013557 baseEnd_2013557 := by
    simpa [prefixWord, tailWord_2013557, baseEnd_2013557] using wordTrace_append hprefix tailTrace_2013557
  have hstable : (prefixWord ++ tailWord_2013557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013557).length < 2 ^ (prefixWord ++ tailWord_2013557).sum := by decide
  have hdescent : baseEnd_2013557 < baseStart_2013557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013579 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_2013579 : Nat := 118140960795 + 2013579 * 2 ^ 59
def prefixEnd_2013579 : Nat := 4983230072969 + 3 ^ 40 * 2013579 * 2
def baseEnd_2013579 : Nat := 689289241866455064401483

theorem tailTrace_2013579 : CollatzResearch.WordTrace tailWord_2013579 prefixEnd_2013579 689289241866455064401483 := by
  unfold tailWord_2013579
  simp only [CollatzResearch.WordTrace]
  refine ⟨73441259572154649759675791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48960839714769766506450527 73441259572154649759675791)
  ·
    refine ⟨110161889358231974639513687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73441259572154649759675791 110161889358231974639513687)
    ·
      refine ⟨165242834037347961959270531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110161889358231974639513687 165242834037347961959270531)
      ·
        refine ⟨247864251056021942938905797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165242834037347961959270531 247864251056021942938905797)
        ·
          refine ⟨46474547073004114301044837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247864251056021942938905797 46474547073004114301044837)
          ·
            refine ⟨8713977576188271431445907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46474547073004114301044837 8713977576188271431445907)
            ·
              refine ⟨13070966364282407147168861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713977576188271431445907 13070966364282407147168861)
              ·
                refine ⟨4901612386605902680188323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13070966364282407147168861 4901612386605902680188323)
                ·
                  refine ⟨7352418579908854020282485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901612386605902680188323 7352418579908854020282485)
                  ·
                    refine ⟨689289241866455064401483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7352418579908854020282485 689289241866455064401483)
                    ·
                      rfl

theorem cell22_2013579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_2013579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013579 prefixEnd_2013579 := by exact prefixLift 2013579
  have htrace : WordTrace (prefixWord ++ tailWord_2013579) baseStart_2013579 baseEnd_2013579 := by
    simpa [prefixWord, tailWord_2013579, baseEnd_2013579] using wordTrace_append hprefix tailTrace_2013579
  have hstable : (prefixWord ++ tailWord_2013579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013579).length < 2 ^ (prefixWord ++ tailWord_2013579).sum := by decide
  have hdescent : baseEnd_2013579 < baseStart_2013579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013641 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_2013641 : Nat := 118140960795 + 2013641 * 2 ^ 59
def prefixEnd_2013641 : Nat := 4983230072969 + 3 ^ 40 * 2013641 * 2
def baseEnd_2013641 : Nat := 689310465733507569351293

theorem tailTrace_2013641 : CollatzResearch.WordTrace tailWord_2013641 prefixEnd_2013641 689310465733507569351293 := by
  unfold tailWord_2013641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73443520897930034348432777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48962347265286689565621851 73443520897930034348432777)
  ·
    refine ⟨55082640673447525761324583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73443520897930034348432777 55082640673447525761324583)
    ·
      refine ⟨82623961010171288641986875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55082640673447525761324583 82623961010171288641986875)
      ·
        refine ⟨123935941515256932962980313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82623961010171288641986875 123935941515256932962980313)
        ·
          refine ⟨92951956136442699722235235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123935941515256932962980313 92951956136442699722235235)
          ·
            refine ⟨139427934204664049583352853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92951956136442699722235235 139427934204664049583352853)
            ·
              refine ⟨6535684415843627324219665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139427934204664049583352853 6535684415843627324219665)
              ·
                refine ⟨4901763311882720493164749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535684415843627324219665 4901763311882720493164749)
                ·
                  refine ⟨1838161241956020184936781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4901763311882720493164749 1838161241956020184936781)
                  ·
                    refine ⟨689310465733507569351293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838161241956020184936781 689310465733507569351293)
                    ·
                      rfl

theorem cell22_2013641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_2013641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013641 prefixEnd_2013641 := by exact prefixLift 2013641
  have htrace : WordTrace (prefixWord ++ tailWord_2013641) baseStart_2013641 baseEnd_2013641 := by
    simpa [prefixWord, tailWord_2013641, baseEnd_2013641] using wordTrace_append hprefix tailTrace_2013641
  have hstable : (prefixWord ++ tailWord_2013641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013641).length < 2 ^ (prefixWord ++ tailWord_2013641).sum := by decide
  have hdescent : baseEnd_2013641 < baseStart_2013641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013671 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 5]
def baseStart_2013671 : Nat := 118140960795 + 2013671 * 2 ^ 59
def prefixEnd_2013671 : Nat := 4983230072969 + 3 ^ 40 * 2013671 * 2
def baseEnd_2013671 : Nat := 229773578448865830367067

theorem tailTrace_2013671 : CollatzResearch.WordTrace tailWord_2013671 prefixEnd_2013671 229773578448865830367067 := by
  unfold tailWord_2013671
  simp only [CollatzResearch.WordTrace]
  refine ⟨73444615087821349472024867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48963076725214232981349911 73444615087821349472024867)
  ·
    refine ⟨110166922631732024208037301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73444615087821349472024867 110166922631732024208037301)
    ·
      refine ⟨10328148996724877269503497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110166922631732024208037301 10328148996724877269503497)
      ·
        refine ⟨7746111747543657952127623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10328148996724877269503497 7746111747543657952127623)
        ·
          refine ⟨11619167621315486928191435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746111747543657952127623 11619167621315486928191435)
          ·
            refine ⟨17428751431973230392287153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619167621315486928191435 17428751431973230392287153)
            ·
              refine ⟨13071563573979922794215365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17428751431973230392287153 13071563573979922794215365)
              ·
                refine ⟨2450918170121235523915381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13071563573979922794215365 2450918170121235523915381)
                ·
                  refine ⟨229773578448865830367067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450918170121235523915381 229773578448865830367067)
                  ·
                    rfl

theorem cell22_2013671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 5].length) (baseStart_2013671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013671 prefixEnd_2013671 := by exact prefixLift 2013671
  have htrace : WordTrace (prefixWord ++ tailWord_2013671) baseStart_2013671 baseEnd_2013671 := by
    simpa [prefixWord, tailWord_2013671, baseEnd_2013671] using wordTrace_append hprefix tailTrace_2013671
  have hstable : (prefixWord ++ tailWord_2013671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013671).length < 2 ^ (prefixWord ++ tailWord_2013671).sum := by decide
  have hdescent : baseEnd_2013671 < baseStart_2013671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013675 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 1, 3]
def baseStart_2013675 : Nat := 118140960795 + 2013675 * 2 ^ 59
def prefixEnd_2013675 : Nat := 4983230072969 + 3 ^ 40 * 2013675 * 2
def baseEnd_2013675 : Nat := 689322104628342814001189

theorem tailTrace_2013675 : CollatzResearch.WordTrace tailWord_2013675 prefixEnd_2013675 689322104628342814001189 := by
  unfold tailWord_2013675
  simp only [CollatzResearch.WordTrace]
  refine ⟨73444760979806858155170479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48963173986537905436780319 73444760979806858155170479)
  ·
    refine ⟨110167141469710287232755719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73444760979806858155170479 110167141469710287232755719)
    ·
      refine ⟨165250712204565430849133579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110167141469710287232755719 165250712204565430849133579)
      ·
        refine ⟨247876068306848146273700369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165250712204565430849133579 247876068306848146273700369)
        ·
          refine ⟨185907051230136109705275277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247876068306848146273700369 185907051230136109705275277)
          ·
            refine ⟨69715144211301041139478229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185907051230136109705275277 69715144211301041139478229)
            ·
              refine ⟨1633948692452368151706521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69715144211301041139478229 1633948692452368151706521)
              ·
                refine ⟨1225461519339276113779891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633948692452368151706521 1225461519339276113779891)
                ·
                  refine ⟨1838192279008914170669837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225461519339276113779891 1838192279008914170669837)
                  ·
                    refine ⟨689322104628342814001189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838192279008914170669837 689322104628342814001189)
                    ·
                      rfl

theorem cell22_2013675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 3].length) (baseStart_2013675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013675 prefixEnd_2013675 := by exact prefixLift 2013675
  have htrace : WordTrace (prefixWord ++ tailWord_2013675) baseStart_2013675 baseEnd_2013675 := by
    simpa [prefixWord, tailWord_2013675, baseEnd_2013675] using wordTrace_append hprefix tailTrace_2013675
  have hstable : (prefixWord ++ tailWord_2013675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013675).length < 2 ^ (prefixWord ++ tailWord_2013675).sum := by decide
  have hdescent : baseEnd_2013675 < baseStart_2013675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013686 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2013686 : Nat := 118140960795 + 2013686 * 2 ^ 59
def prefixEnd_2013686 : Nat := 4983230072969 + 3 ^ 40 * 2013686 * 2
def baseEnd_2013686 : Nat := 689325870153142451976155

theorem tailTrace_2013686 : CollatzResearch.WordTrace tailWord_2013686 prefixEnd_2013686 689325870153142451976155 := by
  unfold tailWord_2013686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590322636422937939613807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48963441455178004689213941 4590322636422937939613807)
  ·
    refine ⟨6885483954634406909420711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590322636422937939613807 6885483954634406909420711)
    ·
      refine ⟨10328225931951610364131067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885483954634406909420711 10328225931951610364131067)
      ·
        refine ⟨15492338897927415546196601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328225931951610364131067 15492338897927415546196601)
        ·
          refine ⟨11619254173445561659647451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15492338897927415546196601 11619254173445561659647451)
          ·
            refine ⟨17428881260168342489471177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619254173445561659647451 17428881260168342489471177)
            ·
              refine ⟨13071660945126256867103383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17428881260168342489471177 13071660945126256867103383)
              ·
                refine ⟨19607491417689385300655075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071660945126256867103383 19607491417689385300655075)
                ·
                  refine ⟨29411237126534077950982613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19607491417689385300655075 29411237126534077950982613)
                  ·
                    refine ⟨689325870153142451976155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29411237126534077950982613 689325870153142451976155)
                    ·
                      rfl

theorem cell22_2013686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2013686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013686 prefixEnd_2013686 := by exact prefixLift 2013686
  have htrace : WordTrace (prefixWord ++ tailWord_2013686) baseStart_2013686 baseEnd_2013686 := by
    simpa [prefixWord, tailWord_2013686, baseEnd_2013686] using wordTrace_append hprefix tailTrace_2013686
  have hstable : (prefixWord ++ tailWord_2013686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013686).length < 2 ^ (prefixWord ++ tailWord_2013686).sum := by decide
  have hdescent : baseEnd_2013686 < baseStart_2013686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013699 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 8]
def baseStart_2013699 : Nat := 118140960795 + 2013699 * 2 ^ 59
def prefixEnd_2013699 : Nat := 4983230072969 + 3 ^ 40 * 2013699 * 2
def baseEnd_2013699 : Nat := 229776773439604917133705

theorem tailTrace_2013699 : CollatzResearch.WordTrace tailWord_2013699 prefixEnd_2013699 229776773439604917133705 := by
  unfold tailWord_2013699
  simp only [CollatzResearch.WordTrace]
  refine ⟨73445636331719910254044151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48963757554479940169362767 73445636331719910254044151)
  ·
    refine ⟨110168454497579865381066227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73445636331719910254044151 110168454497579865381066227)
    ·
      refine ⟨165252681746369798071599341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110168454497579865381066227 165252681746369798071599341)
      ·
        refine ⟨61969755654888674276849753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165252681746369798071599341 61969755654888674276849753)
        ·
          refine ⟨46477316741166505707637315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61969755654888674276849753 46477316741166505707637315)
          ·
            refine ⟨69715975111749758561455973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46477316741166505707637315 69715975111749758561455973)
            ·
              refine ⟨13071745333453079730272995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69715975111749758561455973 13071745333453079730272995)
              ·
                refine ⟨19607618000179619595409493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071745333453079730272995 19607618000179619595409493)
                ·
                  refine ⟨229776773439604917133705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19607618000179619595409493 229776773439604917133705)
                  ·
                    rfl

theorem cell22_2013699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_2013699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013699 prefixEnd_2013699 := by exact prefixLift 2013699
  have htrace : WordTrace (prefixWord ++ tailWord_2013699) baseStart_2013699 baseEnd_2013699 := by
    simpa [prefixWord, tailWord_2013699, baseEnd_2013699] using wordTrace_append hprefix tailTrace_2013699
  have hstable : (prefixWord ++ tailWord_2013699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013699).length < 2 ^ (prefixWord ++ tailWord_2013699).sum := by decide
  have hdescent : baseEnd_2013699 < baseStart_2013699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013746 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2013746 : Nat := 118140960795 + 2013746 * 2 ^ 59
def prefixEnd_2013746 : Nat := 4983230072969 + 3 ^ 40 * 2013746 * 2
def baseEnd_2013746 : Nat := 689346409379322295475971

theorem tailTrace_2013746 : CollatzResearch.WordTrace tailWord_2013746 prefixEnd_2013746 689346409379322295475971 := by
  unfold tailWord_2013746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361837640637409320251273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48964900375033091520670061 18361837640637409320251273)
  ·
    refine ⟨13771378230478056990188455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18361837640637409320251273 13771378230478056990188455)
    ·
      refine ⟨20657067345717085485282683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13771378230478056990188455 20657067345717085485282683)
      ·
        refine ⟨30985601018575628227924025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657067345717085485282683 30985601018575628227924025)
        ·
          refine ⟨23239200763931721170943019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30985601018575628227924025 23239200763931721170943019)
          ·
            refine ⟨34858801145897581756414529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23239200763931721170943019 34858801145897581756414529)
            ·
              refine ⟨26144100859423186317310897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34858801145897581756414529 26144100859423186317310897)
              ·
                refine ⟨19608075644567389737983173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26144100859423186317310897 19608075644567389737983173)
                ·
                  refine ⟨3676514183356385575871845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19608075644567389737983173 3676514183356385575871845)
                  ·
                    refine ⟨689346409379322295475971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676514183356385575871845 689346409379322295475971)
                    ·
                      rfl

theorem cell22_2013746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2013746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013746 prefixEnd_2013746 := by exact prefixLift 2013746
  have htrace : WordTrace (prefixWord ++ tailWord_2013746) baseStart_2013746 baseEnd_2013746 := by
    simpa [prefixWord, tailWord_2013746, baseEnd_2013746] using wordTrace_append hprefix tailTrace_2013746
  have hstable : (prefixWord ++ tailWord_2013746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013746).length < 2 ^ (prefixWord ++ tailWord_2013746).sum := by decide
  have hdescent : baseEnd_2013746 < baseStart_2013746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013793 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2013793 : Nat := 118140960795 + 2013793 * 2 ^ 59
def prefixEnd_2013793 : Nat := 4983230072969 + 3 ^ 40 * 2013793 * 2
def baseEnd_2013793 : Nat := 689362498439829839550827

theorem tailTrace_2013793 : CollatzResearch.WordTrace tailWord_2013793 prefixEnd_2013793 689362498439829839550827 := by
  unfold tailWord_2013793
  simp only [CollatzResearch.WordTrace]
  refine ⟨73449064793379364307966033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48966043195586242871977355 73449064793379364307966033)
  ·
    refine ⟨55086798595034523230974525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73449064793379364307966033 55086798595034523230974525)
    ·
      refine ⟨20657549473137946211615447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55086798595034523230974525 20657549473137946211615447)
      ·
        refine ⟨30986324209706919317423171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657549473137946211615447 30986324209706919317423171)
        ·
          refine ⟨46479486314560378976134757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30986324209706919317423171 46479486314560378976134757)
          ·
            refine ⟨8714903683980071058025267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46479486314560378976134757 8714903683980071058025267)
            ·
              refine ⟨13072355525970106587037901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714903683980071058025267 13072355525970106587037901)
              ·
                refine ⟨4902133322238789970139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13072355525970106587037901 4902133322238789970139213)
                ·
                  refine ⟨1838299995839546238802205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4902133322238789970139213 1838299995839546238802205)
                  ·
                    refine ⟨689362498439829839550827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838299995839546238802205 689362498439829839550827)
                    ·
                      rfl

theorem cell22_2013793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2013793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013793 prefixEnd_2013793 := by exact prefixLift 2013793
  have htrace : WordTrace (prefixWord ++ tailWord_2013793) baseStart_2013793 baseEnd_2013793 := by
    simpa [prefixWord, tailWord_2013793, baseEnd_2013793] using wordTrace_append hprefix tailTrace_2013793
  have hstable : (prefixWord ++ tailWord_2013793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013793).length < 2 ^ (prefixWord ++ tailWord_2013793).sum := by decide
  have hdescent : baseEnd_2013793 < baseStart_2013793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013857 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 5]
def baseStart_2013857 : Nat := 118140960795 + 2013857 * 2 ^ 59
def prefixEnd_2013857 : Nat := 4983230072969 + 3 ^ 40 * 2013857 * 2
def baseEnd_2013857 : Nat := 229794802315918335316877

theorem tailTrace_2013857 : CollatzResearch.WordTrace tailWord_2013857 prefixEnd_2013857 229794802315918335316877 := by
  unfold tailWord_2013857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73451399065147503238295825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48967599376765002158863883 73451399065147503238295825)
  ·
    refine ⟨55088549298860627428721869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73451399065147503238295825 55088549298860627428721869)
    ·
      refine ⟨20658205987072735285770701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55088549298860627428721869 20658205987072735285770701)
      ·
        refine ⟨7746827245152275732164013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20658205987072735285770701 7746827245152275732164013)
        ·
          refine ⟨2905060216932103399561505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7746827245152275732164013 2905060216932103399561505)
          ·
            refine ⟨2178795162699077549671129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905060216932103399561505 2178795162699077549671129)
            ·
              refine ⟨1634096372024308162253347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178795162699077549671129 1634096372024308162253347)
              ·
                refine ⟨2451144558036462243380021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634096372024308162253347 2451144558036462243380021)
                ·
                  refine ⟨229794802315918335316877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2451144558036462243380021 229794802315918335316877)
                  ·
                    rfl

theorem cell22_2013857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_2013857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013857 prefixEnd_2013857 := by exact prefixLift 2013857
  have htrace : WordTrace (prefixWord ++ tailWord_2013857) baseStart_2013857 baseEnd_2013857 := by
    simpa [prefixWord, tailWord_2013857, baseEnd_2013857] using wordTrace_append hprefix tailTrace_2013857
  have hstable : (prefixWord ++ tailWord_2013857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013857).length < 2 ^ (prefixWord ++ tailWord_2013857).sum := by decide
  have hdescent : baseEnd_2013857 < baseStart_2013857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013896 : List Nat := [2, 1, 3, 1, 2, 13]
def baseStart_2013896 : Nat := 118140960795 + 2013896 * 2 ^ 59
def prefixEnd_2013896 : Nat := 4983230072969 + 3 ^ 40 * 2013896 * 2
def baseEnd_2013896 : Nat := 8511083425244097583031

theorem tailTrace_2013896 : CollatzResearch.WordTrace tailWord_2013896 prefixEnd_2013896 8511083425244097583031 := by
  unfold tailWord_2013896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36726410756003106449482771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48968547674670808599310361 36726410756003106449482771)
  ·
    refine ⟨55089616134004659674224157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36726410756003106449482771 55089616134004659674224157)
    ·
      refine ⟨20658606050251747377834059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55089616134004659674224157 20658606050251747377834059)
      ·
        refine ⟨30987909075377621066751089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20658606050251747377834059 30987909075377621066751089)
        ·
          refine ⟨23240931806533215800063317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30987909075377621066751089 23240931806533215800063317)
          ·
            refine ⟨8511083425244097583031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23240931806533215800063317 8511083425244097583031)
            ·
              rfl

theorem cell22_2013896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 13].length) (baseStart_2013896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013896 prefixEnd_2013896 := by exact prefixLift 2013896
  have htrace : WordTrace (prefixWord ++ tailWord_2013896) baseStart_2013896 baseEnd_2013896 := by
    simpa [prefixWord, tailWord_2013896, baseEnd_2013896] using wordTrace_append hprefix tailTrace_2013896
  have hstable : (prefixWord ++ tailWord_2013896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013896).length < 2 ^ (prefixWord ++ tailWord_2013896).sum := by decide
  have hdescent : baseEnd_2013896 < baseStart_2013896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013902 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2013902 : Nat := 118140960795 + 2013902 * 2 ^ 59
def prefixEnd_2013902 : Nat := 4983230072969 + 3 ^ 40 * 2013902 * 2
def baseEnd_2013902 : Nat := 229799937122463296191831

theorem tailTrace_2013902 : CollatzResearch.WordTrace tailWord_2013902 prefixEnd_2013902 229799937122463296191831 := by
  unfold tailWord_2013902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181630043748059490460495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48968693566656317282455973 9181630043748059490460495)
  ·
    refine ⟨13772445065622089235690743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9181630043748059490460495 13772445065622089235690743)
    ·
      refine ⟨20658667598433133853536115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13772445065622089235690743 20658667598433133853536115)
      ·
        refine ⟨30988001397649700780304173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20658667598433133853536115 30988001397649700780304173)
        ·
          refine ⟨11620500524118637792614065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30988001397649700780304173 11620500524118637792614065)
          ·
            refine ⟨8715375393088978344460549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620500524118637792614065 8715375393088978344460549)
            ·
              refine ⟨1634132886204183439586353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8715375393088978344460549 1634132886204183439586353)
              ·
                refine ⟨1225599664653137579689765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634132886204183439586353 1225599664653137579689765)
                ·
                  refine ⟨229799937122463296191831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225599664653137579689765 229799937122463296191831)
                  ·
                    rfl

theorem cell22_2013902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2013902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013902 prefixEnd_2013902 := by exact prefixLift 2013902
  have htrace : WordTrace (prefixWord ++ tailWord_2013902) baseStart_2013902 baseEnd_2013902 := by
    simpa [prefixWord, tailWord_2013902, baseEnd_2013902] using wordTrace_append hprefix tailTrace_2013902
  have hstable : (prefixWord ++ tailWord_2013902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013902).length < 2 ^ (prefixWord ++ tailWord_2013902).sum := by decide
  have hdescent : baseEnd_2013902 < baseStart_2013902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013962 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2013962 : Nat := 118140960795 + 2013962 * 2 ^ 59
def prefixEnd_2013962 : Nat := 4983230072969 + 3 ^ 40 * 2013962 * 2
def baseEnd_2013962 : Nat := 689420350593569732075309

theorem tailTrace_2013962 : CollatzResearch.WordTrace tailWord_2013962 prefixEnd_2013962 689420350593569732075309 := by
  unfold tailWord_2013962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363807182441776542717035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48970152486511404113912093 18363807182441776542717035)
  ·
    refine ⟨27545710773662664814075553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363807182441776542717035 27545710773662664814075553)
    ·
      refine ⟨20659283080246998610556665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27545710773662664814075553 20659283080246998610556665)
      ·
        refine ⟨15494462310185248957917499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20659283080246998610556665 15494462310185248957917499)
        ·
          refine ⟨23241693465277873436876249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494462310185248957917499 23241693465277873436876249)
          ·
            refine ⟨17431270098958405077657187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23241693465277873436876249 17431270098958405077657187)
            ·
              refine ⟨26146905148437607616485781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17431270098958405077657187 26146905148437607616485781)
              ·
                refine ⟨1225636178833012857022771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26146905148437607616485781 1225636178833012857022771)
                ·
                  refine ⟨1838454268249519285534157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225636178833012857022771 1838454268249519285534157)
                  ·
                    refine ⟨689420350593569732075309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838454268249519285534157 689420350593569732075309)
                    ·
                      rfl

theorem cell22_2013962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2013962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013962 prefixEnd_2013962 := by exact prefixLift 2013962
  have htrace : WordTrace (prefixWord ++ tailWord_2013962) baseStart_2013962 baseEnd_2013962 := by
    simpa [prefixWord, tailWord_2013962, baseEnd_2013962] using wordTrace_append hprefix tailTrace_2013962
  have hstable : (prefixWord ++ tailWord_2013962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013962).length < 2 ^ (prefixWord ++ tailWord_2013962).sum := by decide
  have hdescent : baseEnd_2013962 < baseStart_2013962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013973 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2013973 : Nat := 118140960795 + 2013973 * 2 ^ 59
def prefixEnd_2013973 : Nat := 4983230072969 + 3 ^ 40 * 2013973 * 2
def baseEnd_2013973 : Nat := 689424116118369370050275

theorem tailTrace_2013973 : CollatzResearch.WordTrace tailWord_2013973 prefixEnd_2013973 689424116118369370050275 := by
  unfold tailWord_2013973
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455629932727255049518573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48970419955151503366345715 73455629932727255049518573)
  ·
    refine ⟨27545861224772720643569465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73455629932727255049518573 27545861224772720643569465)
    ·
      refine ⟨20659395918579540482677099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27545861224772720643569465 20659395918579540482677099)
      ·
        refine ⟨30989093877869310724015649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20659395918579540482677099 30989093877869310724015649)
        ·
          refine ⟨23241820408401983043011737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30989093877869310724015649 23241820408401983043011737)
          ·
            refine ⟨17431365306301487282258803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23241820408401983043011737 17431365306301487282258803)
            ·
              refine ⟨26147047959452230923388205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17431365306301487282258803 26147047959452230923388205)
              ·
                refine ⟨9805142984794586596270577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26147047959452230923388205 9805142984794586596270577)
                ·
                  refine ⟨7353857238595939947202933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9805142984794586596270577 7353857238595939947202933)
                  ·
                    refine ⟨689424116118369370050275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7353857238595939947202933 689424116118369370050275)
                    ·
                      rfl

theorem cell22_2013973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2013973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2013973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2013973 prefixEnd_2013973 := by exact prefixLift 2013973
  have htrace : WordTrace (prefixWord ++ tailWord_2013973) baseStart_2013973 baseEnd_2013973 := by
    simpa [prefixWord, tailWord_2013973, baseEnd_2013973] using wordTrace_append hprefix tailTrace_2013973
  have hstable : (prefixWord ++ tailWord_2013973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013973).length < 2 ^ (prefixWord ++ tailWord_2013973).sum := by decide
  have hdescent : baseEnd_2013973 < baseStart_2013973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014048 : List Nat := [2, 1, 1, 3, 3, 1, 1, 10]
def baseStart_2014048 : Nat := 118140960795 + 2014048 * 2 ^ 59
def prefixEnd_2014048 : Nat := 4983230072969 + 3 ^ 40 * 2014048 * 2
def baseEnd_2014048 : Nat := 76605532239010463825005

theorem tailTrace_2014048 : CollatzResearch.WordTrace tailWord_2014048 prefixEnd_2014048 76605532239010463825005 := by
  unfold tailWord_2014048
  simp only [CollatzResearch.WordTrace]
  refine ⟨36729182703727771429249399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48972243604970361905665865 36729182703727771429249399)
  ·
    refine ⟨55093774055591657143874099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36729182703727771429249399 55093774055591657143874099)
    ·
      refine ⟨82640661083387485715811149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55093774055591657143874099 82640661083387485715811149)
      ·
        refine ⟨30990247906270307143429181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82640661083387485715811149 30990247906270307143429181)
        ·
          refine ⟨11621342964851365178785943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30990247906270307143429181 11621342964851365178785943)
          ·
            refine ⟨17432014447277047768178915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621342964851365178785943 17432014447277047768178915)
            ·
              refine ⟨26148021670915571652268373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17432014447277047768178915 26148021670915571652268373)
              ·
                refine ⟨76605532239010463825005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26148021670915571652268373 76605532239010463825005)
                ·
                  rfl

theorem cell22_2014048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_2014048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014048 prefixEnd_2014048 := by exact prefixLift 2014048
  have htrace : WordTrace (prefixWord ++ tailWord_2014048) baseStart_2014048 baseEnd_2014048 := by
    simpa [prefixWord, tailWord_2014048, baseEnd_2014048] using wordTrace_append hprefix tailTrace_2014048
  have hstable : (prefixWord ++ tailWord_2014048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014048).length < 2 ^ (prefixWord ++ tailWord_2014048).sum := by decide
  have hdescent : baseEnd_2014048 < baseStart_2014048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014069 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2014069 : Nat := 118140960795 + 2014069 * 2 ^ 59
def prefixEnd_2014069 : Nat := 4983230072969 + 3 ^ 40 * 2014069 * 2
def baseEnd_2014069 : Nat := 689456978880257119649981

theorem tailTrace_2014069 : CollatzResearch.WordTrace tailWord_2014069 prefixEnd_2014069 689456978880257119649981 := by
  unfold tailWord_2014069
  simp only [CollatzResearch.WordTrace]
  refine ⟨73459131340379463445013261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48972754226919642296675507 73459131340379463445013261)
  ·
    refine ⟨27547174252642298791879973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73459131340379463445013261 27547174252642298791879973)
    ·
      refine ⟨5165095172370431023477495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27547174252642298791879973 5165095172370431023477495)
      ·
        refine ⟨7747642758555646535216243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165095172370431023477495 7747642758555646535216243)
        ·
          refine ⟨11621464137833469802824365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747642758555646535216243 11621464137833469802824365)
          ·
            refine ⟨4358049051687551176059137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11621464137833469802824365 4358049051687551176059137)
            ·
              refine ⟨3268536788765663382044353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358049051687551176059137 3268536788765663382044353)
              ·
                refine ⟨2451402591574247536533265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268536788765663382044353 2451402591574247536533265)
                ·
                  refine ⟨1838551943680685652399949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451402591574247536533265 1838551943680685652399949)
                  ·
                    refine ⟨689456978880257119649981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838551943680685652399949 689456978880257119649981)
                    ·
                      rfl

theorem cell22_2014069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2014069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014069 prefixEnd_2014069 := by exact prefixLift 2014069
  have htrace : WordTrace (prefixWord ++ tailWord_2014069) baseStart_2014069 baseEnd_2014069 := by
    simpa [prefixWord, tailWord_2014069, baseEnd_2014069] using wordTrace_append hprefix tailTrace_2014069
  have hstable : (prefixWord ++ tailWord_2014069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014069).length < 2 ^ (prefixWord ++ tailWord_2014069).sum := by decide
  have hdescent : baseEnd_2014069 < baseStart_2014069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014150 : List Nat := [6, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2014150 : Nat := 118140960795 + 2014150 * 2 ^ 59
def prefixEnd_2014150 : Nat := 4983230072969 + 3 ^ 40 * 2014150 * 2
def baseEnd_2014150 : Nat := 76609411870622212041637

theorem tailTrace_2014150 : CollatzResearch.WordTrace tailWord_2014150 prefixEnd_2014150 76609411870622212041637 := by
  unfold tailWord_2014150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295690176658937946209747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48974723768724009519141269 2295690176658937946209747)
  ·
    refine ⟨3443535264988406919314621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295690176658937946209747 3443535264988406919314621)
    ·
      refine ⟨1291325724370652594742983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3443535264988406919314621 1291325724370652594742983)
      ·
        refine ⟨1936988586555978892114475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291325724370652594742983 1936988586555978892114475)
        ·
          refine ⟨2905482879833968338171713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936988586555978892114475 2905482879833968338171713)
          ·
            refine ⟨2179112159875476253628785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905482879833968338171713 2179112159875476253628785)
            ·
              refine ⟨1634334119906607190221589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179112159875476253628785 1634334119906607190221589)
              ·
                refine ⟨76609411870622212041637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1634334119906607190221589 76609411870622212041637)
                ·
                  rfl

theorem cell22_2014150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2014150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014150 prefixEnd_2014150 := by exact prefixLift 2014150
  have htrace : WordTrace (prefixWord ++ tailWord_2014150) baseStart_2014150 baseEnd_2014150 := by
    simpa [prefixWord, tailWord_2014150, baseEnd_2014150] using wordTrace_append hprefix tailTrace_2014150
  have hstable : (prefixWord ++ tailWord_2014150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014150).length < 2 ^ (prefixWord ++ tailWord_2014150).sum := by decide
  have hdescent : baseEnd_2014150 < baseStart_2014150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014155 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 6]
def baseStart_2014155 : Nat := 118140960795 + 2014155 * 2 ^ 59
def prefixEnd_2014155 : Nat := 4983230072969 + 3 ^ 40 * 2014155 * 2
def baseEnd_2014155 : Nat := 229828806145927187333239

theorem tailTrace_2014155 : CollatzResearch.WordTrace tailWord_2014155 prefixEnd_2014155 229828806145927187333239 := by
  unfold tailWord_2014155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73462268018067900132643919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48974845345378600088429279 73462268018067900132643919)
  ·
    refine ⟨110193402027101850198965879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73462268018067900132643919 110193402027101850198965879)
    ·
      refine ⟨165290103040652775298448819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110193402027101850198965879 165290103040652775298448819)
      ·
        refine ⟨247935154560979162947673229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165290103040652775298448819 247935154560979162947673229)
        ·
          refine ⟨92975682960367186105377461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247935154560979162947673229 92975682960367186105377461)
          ·
            refine ⟨8716470277534423697379137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92975682960367186105377461 8716470277534423697379137)
            ·
              refine ⟨6537352708150817773034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716470277534423697379137 6537352708150817773034353)
              ·
                refine ⟨4903014531113113329775765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6537352708150817773034353 4903014531113113329775765)
                ·
                  refine ⟨229828806145927187333239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4903014531113113329775765 229828806145927187333239)
                  ·
                    rfl

theorem cell22_2014155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_2014155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014155 prefixEnd_2014155 := by exact prefixLift 2014155
  have htrace : WordTrace (prefixWord ++ tailWord_2014155) baseStart_2014155 baseEnd_2014155 := by
    simpa [prefixWord, tailWord_2014155, baseEnd_2014155] using wordTrace_append hprefix tailTrace_2014155
  have hstable : (prefixWord ++ tailWord_2014155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014155).length < 2 ^ (prefixWord ++ tailWord_2014155).sum := by decide
  have hdescent : baseEnd_2014155 < baseStart_2014155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014204 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2014204 : Nat := 118140960795 + 2014204 * 2 ^ 59
def prefixEnd_2014204 : Nat := 4983230072969 + 3 ^ 40 * 2014204 * 2
def baseEnd_2014204 : Nat := 689503192139161767524567

theorem tailTrace_2014204 : CollatzResearch.WordTrace tailWord_2014204 prefixEnd_2014204 689503192139161767524567 := by
  unfold tailWord_2014204
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732027597445190750588833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48976036796593587667451777 36732027597445190750588833)
  ·
    refine ⟨27549020698083893062941625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36732027597445190750588833 27549020698083893062941625)
    ·
      refine ⟨20661765523562919797206219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27549020698083893062941625 20661765523562919797206219)
      ·
        refine ⟨30992648285344379695809329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20661765523562919797206219 30992648285344379695809329)
        ·
          refine ⟨23244486214008284771856997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30992648285344379695809329 23244486214008284771856997)
          ·
            refine ⟨4358341165126553394723187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23244486214008284771856997 4358341165126553394723187)
            ·
              refine ⟨6537511747689830092084781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358341165126553394723187 6537511747689830092084781)
              ·
                refine ⟨2451566905383686284531793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537511747689830092084781 2451566905383686284531793)
                ·
                  refine ⟨1838675179037764713398845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451566905383686284531793 1838675179037764713398845)
                  ·
                    refine ⟨689503192139161767524567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838675179037764713398845 689503192139161767524567)
                    ·
                      rfl

theorem cell22_2014204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2014204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014204 prefixEnd_2014204 := by exact prefixLift 2014204
  have htrace : WordTrace (prefixWord ++ tailWord_2014204) baseStart_2014204 baseEnd_2014204 := by
    simpa [prefixWord, tailWord_2014204, baseEnd_2014204] using wordTrace_append hprefix tailTrace_2014204
  have hstable : (prefixWord ++ tailWord_2014204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014204).length < 2 ^ (prefixWord ++ tailWord_2014204).sum := by decide
  have hdescent : baseEnd_2014204 < baseStart_2014204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014240 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_2014240 : Nat := 118140960795 + 2014240 * 2 ^ 59
def prefixEnd_2014240 : Nat := 4983230072969 + 3 ^ 40 * 2014240 * 2
def baseEnd_2014240 : Nat := 229838505224956557874819

theorem tailTrace_2014240 : CollatzResearch.WordTrace tailWord_2014240 prefixEnd_2014240 229838505224956557874819 := by
  unfold tailWord_2014240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732684111379979824744087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48976912148506639766325449 36732684111379979824744087)
  ·
    refine ⟨55099026167069969737116131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36732684111379979824744087 55099026167069969737116131)
    ·
      refine ⟨82648539250604954605674197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55099026167069969737116131 82648539250604954605674197)
      ·
        refine ⟨1937075138686053623570489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82648539250604954605674197 1937075138686053623570489)
        ·
          refine ⟨1452806354014540217677867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937075138686053623570489 1452806354014540217677867)
          ·
            refine ⟨2179209531021810326516801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452806354014540217677867 2179209531021810326516801)
            ·
              refine ⟨1634407148266357744887601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179209531021810326516801 1634407148266357744887601)
              ·
                refine ⟨1225805361199768308665701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634407148266357744887601 1225805361199768308665701)
                ·
                  refine ⟨229838505224956557874819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225805361199768308665701 229838505224956557874819)
                  ·
                    rfl

theorem cell22_2014240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_2014240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014240 prefixEnd_2014240 := by exact prefixLift 2014240
  have htrace : WordTrace (prefixWord ++ tailWord_2014240) baseStart_2014240 baseEnd_2014240 := by
    simpa [prefixWord, tailWord_2014240, baseEnd_2014240] using wordTrace_append hprefix tailTrace_2014240
  have hstable : (prefixWord ++ tailWord_2014240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014240).length < 2 ^ (prefixWord ++ tailWord_2014240).sum := by decide
  have hdescent : baseEnd_2014240 < baseStart_2014240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014326 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2014326 : Nat := 118140960795 + 2014326 * 2 ^ 59
def prefixEnd_2014326 : Nat := 4983230072969 + 3 ^ 40 * 2014326 * 2
def baseEnd_2014326 : Nat := 689544955232394115974193

theorem tailTrace_2014326 : CollatzResearch.WordTrace tailWord_2014326 prefixEnd_2014326 689544955232394115974193 := by
  unfold tailWord_2014326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591781556278024771069927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48979003266965597558079221 4591781556278024771069927)
  ·
    refine ⟨6887672334417037156604891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591781556278024771069927 6887672334417037156604891)
    ·
      refine ⟨10331508501625555734907337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887672334417037156604891 10331508501625555734907337)
      ·
        refine ⟨7748631376219166801180503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10331508501625555734907337 7748631376219166801180503)
        ·
          refine ⟨11622947064328750201770755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748631376219166801180503 11622947064328750201770755)
          ·
            refine ⟨17434420596493125302656133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11622947064328750201770755 17434420596493125302656133)
            ·
              refine ⟨3268953861842460994248025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17434420596493125302656133 3268953861842460994248025)
              ·
                refine ⟨2451715396381845745686019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268953861842460994248025 2451715396381845745686019)
                ·
                  refine ⟨3677573094572768618529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451715396381845745686019 3677573094572768618529029)
                  ·
                    refine ⟨689544955232394115974193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677573094572768618529029 689544955232394115974193)
                    ·
                      rfl

theorem cell22_2014326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2014326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014326 prefixEnd_2014326 := by exact prefixLift 2014326
  have htrace : WordTrace (prefixWord ++ tailWord_2014326) baseStart_2014326 baseEnd_2014326 := by
    simpa [prefixWord, tailWord_2014326, baseEnd_2014326] using wordTrace_append hprefix tailTrace_2014326
  have hstable : (prefixWord ++ tailWord_2014326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014326).length < 2 ^ (prefixWord ++ tailWord_2014326).sum := by decide
  have hdescent : baseEnd_2014326 < baseStart_2014326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014334 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2014334 : Nat := 118140960795 + 2014334 * 2 ^ 59
def prefixEnd_2014334 : Nat := 4983230072969 + 3 ^ 40 * 2014334 * 2
def baseEnd_2014334 : Nat := 689547693795884761774169

theorem tailTrace_2014334 : CollatzResearch.WordTrace tailWord_2014334 prefixEnd_2014334 689547693795884761774169 := by
  unfold tailWord_2014334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183599585552426712926257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48979197789612942468940037 9183599585552426712926257)
  ·
    refine ⟨6887699689164320034694693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9183599585552426712926257 6887699689164320034694693)
    ·
      refine ⟨1291443691718310006505255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6887699689164320034694693 1291443691718310006505255)
      ·
        refine ⟨1937165537577465009757883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291443691718310006505255 1937165537577465009757883)
        ·
          refine ⟨2905748306366197514636825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937165537577465009757883 2905748306366197514636825)
          ·
            refine ⟨2179311229774648135977619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905748306366197514636825 2179311229774648135977619)
            ·
              refine ⟨3268966844661972203966429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179311229774648135977619 3268966844661972203966429)
              ·
                refine ⟨1225862566748239576487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3268966844661972203966429 1225862566748239576487411)
                ·
                  refine ⟨1838793850122359364731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225862566748239576487411 1838793850122359364731117)
                  ·
                    refine ⟨689547693795884761774169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838793850122359364731117 689547693795884761774169)
                    ·
                      rfl

theorem cell22_2014334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2014334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014334 prefixEnd_2014334 := by exact prefixLift 2014334
  have htrace : WordTrace (prefixWord ++ tailWord_2014334) baseStart_2014334 baseEnd_2014334 := by
    simpa [prefixWord, tailWord_2014334, baseEnd_2014334] using wordTrace_append hprefix tailTrace_2014334
  have hstable : (prefixWord ++ tailWord_2014334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014334).length < 2 ^ (prefixWord ++ tailWord_2014334).sum := by decide
  have hdescent : baseEnd_2014334 < baseStart_2014334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014354 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2014354 : Nat := 118140960795 + 2014354 * 2 ^ 59
def prefixEnd_2014354 : Nat := 4983230072969 + 3 ^ 40 * 2014354 * 2
def baseEnd_2014354 : Nat := 689554540204611376274107

theorem tailTrace_2014354 : CollatzResearch.WordTrace tailWord_2014354 prefixEnd_2014354 689554540204611376274107 := by
  unfold tailWord_2014354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367381536086739279784529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48979684096231304746092077 18367381536086739279784529)
  ·
    refine ⟨13775536152065054459838397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18367381536086739279784529 13775536152065054459838397)
    ·
      refine ⟨5165826057024395422439399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13775536152065054459838397 5165826057024395422439399)
      ·
        refine ⟨7748739085536593133659099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165826057024395422439399 7748739085536593133659099)
        ·
          refine ⟨11623108628304889700488649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748739085536593133659099 11623108628304889700488649)
          ·
            refine ⟨8717331471228667275366487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11623108628304889700488649 8717331471228667275366487)
            ·
              refine ⟨13075997206843000913049731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717331471228667275366487 13075997206843000913049731)
              ·
                refine ⟨19613995810264501369574597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075997206843000913049731 19613995810264501369574597)
                ·
                  refine ⟨3677624214424594006795237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19613995810264501369574597 3677624214424594006795237)
                  ·
                    refine ⟨689554540204611376274107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677624214424594006795237 689554540204611376274107)
                    ·
                      rfl

theorem cell22_2014354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2014354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014354 prefixEnd_2014354 := by exact prefixLift 2014354
  have htrace : WordTrace (prefixWord ++ tailWord_2014354) baseStart_2014354 baseEnd_2014354 := by
    simpa [prefixWord, tailWord_2014354, baseEnd_2014354] using wordTrace_append hprefix tailTrace_2014354
  have hstable : (prefixWord ++ tailWord_2014354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014354).length < 2 ^ (prefixWord ++ tailWord_2014354).sum := by decide
  have hdescent : baseEnd_2014354 < baseStart_2014354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014373 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_2014373 : Nat := 118140960795 + 2014373 * 2 ^ 59
def prefixEnd_2014373 : Nat := 4983230072969 + 3 ^ 40 * 2014373 * 2
def baseEnd_2014373 : Nat := 689561044292901660049049

theorem tailTrace_2014373 : CollatzResearch.WordTrace tailWord_2014373 prefixEnd_2014373 689561044292901660049049 := by
  unfold tailWord_2014373
  simp only [CollatzResearch.WordTrace]
  refine ⟨73470219131278123364079773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48980146087518748909386515 73470219131278123364079773)
  ·
    refine ⟨27551332174229296261529915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73470219131278123364079773 27551332174229296261529915)
    ·
      refine ⟨41326998261343944392294873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27551332174229296261529915 41326998261343944392294873)
      ·
        refine ⟨30995248696007958294221155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41326998261343944392294873 30995248696007958294221155)
        ·
          refine ⟨46492873044011937441331733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30995248696007958294221155 46492873044011937441331733)
          ·
            refine ⟨2179353423938059567562425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46492873044011937441331733 2179353423938059567562425)
            ·
              refine ⟨1634515067953544675671819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179353423938059567562425 1634515067953544675671819)
              ·
                refine ⟨2451772601930317013507729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634515067953544675671819 2451772601930317013507729)
                ·
                  refine ⟨1838829451447737760130797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451772601930317013507729 1838829451447737760130797)
                  ·
                    refine ⟨689561044292901660049049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838829451447737760130797 689561044292901660049049)
                    ·
                      rfl

theorem cell22_2014373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_2014373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014373 prefixEnd_2014373 := by exact prefixLift 2014373
  have htrace : WordTrace (prefixWord ++ tailWord_2014373) baseStart_2014373 baseEnd_2014373 := by
    simpa [prefixWord, tailWord_2014373, baseEnd_2014373] using wordTrace_append hprefix tailTrace_2014373
  have hstable : (prefixWord ++ tailWord_2014373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014373).length < 2 ^ (prefixWord ++ tailWord_2014373).sum := by decide
  have hdescent : baseEnd_2014373 < baseStart_2014373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014397 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2014397 : Nat := 118140960795 + 2014397 * 2 ^ 59
def prefixEnd_2014397 : Nat := 4983230072969 + 3 ^ 40 * 2014397 * 2
def baseEnd_2014397 : Nat := 229856419994457865816325

theorem tailTrace_2014397 : CollatzResearch.WordTrace tailWord_2014397 prefixEnd_2014397 229856419994457865816325 := by
  unfold tailWord_2014397
  simp only [CollatzResearch.WordTrace]
  refine ⟨73471094483191175462953445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48980729655460783641968963 73471094483191175462953445)
  ·
    refine ⟨13775830215598345399303771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73471094483191175462953445 13775830215598345399303771)
    ·
      refine ⟨20663745323397518098955657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13775830215598345399303771 20663745323397518098955657)
      ·
        refine ⟨15497808992548138574216743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20663745323397518098955657 15497808992548138574216743)
        ·
          refine ⟨23246713488822207861325115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15497808992548138574216743 23246713488822207861325115)
          ·
            refine ⟨34870070233233311791987673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23246713488822207861325115 34870070233233311791987673)
            ·
              refine ⟨26152552674924983843990755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34870070233233311791987673 26152552674924983843990755)
              ·
                refine ⟨39228829012387475765986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26152552674924983843990755 39228829012387475765986133)
                ·
                  refine ⟨229856419994457865816325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39228829012387475765986133 229856419994457865816325)
                  ·
                    rfl

theorem cell22_2014397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2014397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014397 prefixEnd_2014397 := by exact prefixLift 2014397
  have htrace : WordTrace (prefixWord ++ tailWord_2014397) baseStart_2014397 baseEnd_2014397 := by
    simpa [prefixWord, tailWord_2014397, baseEnd_2014397] using wordTrace_append hprefix tailTrace_2014397
  have hstable : (prefixWord ++ tailWord_2014397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014397).length < 2 ^ (prefixWord ++ tailWord_2014397).sum := by decide
  have hdescent : baseEnd_2014397 < baseStart_2014397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014418 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2014418 : Nat := 118140960795 + 2014418 * 2 ^ 59
def prefixEnd_2014418 : Nat := 4983230072969 + 3 ^ 40 * 2014418 * 2
def baseEnd_2014418 : Nat := 689576448712536542673911

theorem tailTrace_2014418 : CollatzResearch.WordTrace tailWord_2014418 prefixEnd_2014418 689576448712536542673911 := by
  unfold tailWord_2014418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367965104028774012366977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48981240277410064032978605 18367965104028774012366977)
  ·
    refine ⟨13775973828021580509275233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18367965104028774012366977 13775973828021580509275233)
    ·
      refine ⟨10331980371016185381956425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13775973828021580509275233 10331980371016185381956425)
      ·
        refine ⟨7748985278262139036467319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10331980371016185381956425 7748985278262139036467319)
        ·
          refine ⟨11623477917393208554700979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748985278262139036467319 11623477917393208554700979)
          ·
            refine ⟨17435216876089812832051469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623477917393208554700979 17435216876089812832051469)
            ·
              refine ⟨6538206328533679812019301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17435216876089812832051469 6538206328533679812019301)
              ·
                refine ⟨1225913686600064964753619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6538206328533679812019301 1225913686600064964753619)
                ·
                  refine ⟨1838870529900097447130429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225913686600064964753619 1838870529900097447130429)
                  ·
                    refine ⟨689576448712536542673911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838870529900097447130429 689576448712536542673911)
                    ·
                      rfl

theorem cell22_2014418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2014418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014418 prefixEnd_2014418 := by exact prefixLift 2014418
  have htrace : WordTrace (prefixWord ++ tailWord_2014418) baseStart_2014418 baseEnd_2014418 := by
    simpa [prefixWord, tailWord_2014418, baseEnd_2014418] using wordTrace_append hprefix tailTrace_2014418
  have hstable : (prefixWord ++ tailWord_2014418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014418).length < 2 ^ (prefixWord ++ tailWord_2014418).sum := by decide
  have hdescent : baseEnd_2014418 < baseStart_2014418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014444 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_2014444 : Nat := 118140960795 + 2014444 * 2 ^ 59
def prefixEnd_2014444 : Nat := 4983230072969 + 3 ^ 40 * 2014444 * 2
def baseEnd_2014444 : Nat := 689585349043881141523831

theorem tailTrace_2014444 : CollatzResearch.WordTrace tailWord_2014444 prefixEnd_2014444 689585349043881141523831 := by
  unfold tailWord_2014444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36736404357010451244957193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48981872476013934993276257 36736404357010451244957193)
  ·
    refine ⟨27552303267757838433717895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36736404357010451244957193 27552303267757838433717895)
    ·
      refine ⟨41328454901636757650576843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552303267757838433717895 41328454901636757650576843)
      ·
        refine ⟨61992682352455136475865265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41328454901636757650576843 61992682352455136475865265)
        ·
          refine ⟨46494511764341352356898949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61992682352455136475865265 46494511764341352356898949)
          ·
            refine ⟨8717720955814003566918553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46494511764341352356898949 8717720955814003566918553)
            ·
              refine ⟨6538290716860502675188915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717720955814003566918553 6538290716860502675188915)
              ·
                refine ⟨9807436075290754012783373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538290716860502675188915 9807436075290754012783373)
                ·
                  refine ⟨3677788528234032754793765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9807436075290754012783373 3677788528234032754793765)
                  ·
                    refine ⟨689585349043881141523831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677788528234032754793765 689585349043881141523831)
                    ·
                      rfl

theorem cell22_2014444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_2014444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014444 prefixEnd_2014444 := by exact prefixLift 2014444
  have htrace : WordTrace (prefixWord ++ tailWord_2014444) baseStart_2014444 baseEnd_2014444 := by
    simpa [prefixWord, tailWord_2014444, baseEnd_2014444] using wordTrace_append hprefix tailTrace_2014444
  have hstable : (prefixWord ++ tailWord_2014444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014444).length < 2 ^ (prefixWord ++ tailWord_2014444).sum := by decide
  have hdescent : baseEnd_2014444 < baseStart_2014444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014476 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_2014476 : Nat := 118140960795 + 2014476 * 2 ^ 59
def prefixEnd_2014476 : Nat := 4983230072969 + 3 ^ 40 * 2014476 * 2
def baseEnd_2014476 : Nat := 229865434432614574907911

theorem tailTrace_2014476 : CollatzResearch.WordTrace tailWord_2014476 prefixEnd_2014476 229865434432614574907911 := by
  unfold tailWord_2014476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36736987924952485977539641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48982650566603314636719521 36736987924952485977539641)
  ·
    refine ⟨27552740943714364483154731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36736987924952485977539641 27552740943714364483154731)
    ·
      refine ⟨41329111415571546724732097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552740943714364483154731 41329111415571546724732097)
      ·
        refine ⟨30996833561678660043549073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41329111415571546724732097 30996833561678660043549073)
        ·
          refine ⟨23247625171258995032661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30996833561678660043549073 23247625171258995032661805)
          ·
            refine ⟨8717859439222123137248177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23247625171258995032661805 8717859439222123137248177)
            ·
              refine ⟨6538394579416592352936133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717859439222123137248177 6538394579416592352936133)
              ·
                refine ⟨1225948983640611066175525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6538394579416592352936133 1225948983640611066175525)
                ·
                  refine ⟨229865434432614574907911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225948983640611066175525 229865434432614574907911)
                  ·
                    rfl

theorem cell22_2014476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_2014476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014476 prefixEnd_2014476 := by exact prefixLift 2014476
  have htrace : WordTrace (prefixWord ++ tailWord_2014476) baseStart_2014476 baseEnd_2014476 := by
    simpa [prefixWord, tailWord_2014476, baseEnd_2014476] using wordTrace_append hprefix tailTrace_2014476
  have hstable : (prefixWord ++ tailWord_2014476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014476).length < 2 ^ (prefixWord ++ tailWord_2014476).sum := by decide
  have hdescent : baseEnd_2014476 < baseStart_2014476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014506 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2014506 : Nat := 118140960795 + 2014506 * 2 ^ 59
def prefixEnd_2014506 : Nat := 4983230072969 + 3 ^ 40 * 2014506 * 2
def baseEnd_2014506 : Nat := 689606572910933646473641

theorem tailTrace_2014506 : CollatzResearch.WordTrace tailWord_2014506 prefixEnd_2014506 689606572910933646473641 := by
  unfold tailWord_2014506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368767509949071769667843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48983380026530858052447581 18368767509949071769667843)
  ·
    refine ⟨27553151264923607654501765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368767509949071769667843 27553151264923607654501765)
    ·
      refine ⟨5166215862173176435219081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27553151264923607654501765 5166215862173176435219081)
      ·
        refine ⟨3874661896629882326414311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5166215862173176435219081 3874661896629882326414311)
        ·
          refine ⟨5811992844944823489621467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874661896629882326414311 5811992844944823489621467)
          ·
            refine ⟨8717989267417235234432201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811992844944823489621467 8717989267417235234432201)
            ·
              refine ⟨6538491950562926425824151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717989267417235234432201 6538491950562926425824151)
              ·
                refine ⟨9807737925844389638736227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538491950562926425824151 9807737925844389638736227)
                ·
                  refine ⟨14711606888766584458104341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807737925844389638736227 14711606888766584458104341)
                  ·
                    refine ⟨689606572910933646473641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14711606888766584458104341 689606572910933646473641)
                    ·
                      rfl

theorem cell22_2014506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2014506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014506 prefixEnd_2014506 := by exact prefixLift 2014506
  have htrace : WordTrace (prefixWord ++ tailWord_2014506) baseStart_2014506 baseEnd_2014506 := by
    simpa [prefixWord, tailWord_2014506, baseEnd_2014506] using wordTrace_append hprefix tailTrace_2014506
  have hstable : (prefixWord ++ tailWord_2014506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014506).length < 2 ^ (prefixWord ++ tailWord_2014506).sum := by decide
  have hdescent : baseEnd_2014506 < baseStart_2014506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014521 : List Nat := [1, 2, 1, 6, 2, 2, 8]
def baseStart_2014521 : Nat := 118140960795 + 2014521 * 2 ^ 59
def prefixEnd_2014521 : Nat := 4983230072969 + 3 ^ 40 * 2014521 * 2
def baseEnd_2014521 : Nat := 25541174359906615086985

theorem tailTrace_2014521 : CollatzResearch.WordTrace tailWord_2014521 prefixEnd_2014521 25541174359906615086985 := by
  unfold tailWord_2014521
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475617134741944640467417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48983744756494629760311611 73475617134741944640467417)
  ·
    refine ⟨55106712851056458480350563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73475617134741944640467417 55106712851056458480350563)
    ·
      refine ⟨82660069276584687720525845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55106712851056458480350563 82660069276584687720525845)
      ·
        refine ⟨3874690747339907236899649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82660069276584687720525845 3874690747339907236899649)
        ·
          refine ⟨2906018060504930427674737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3874690747339907236899649 2906018060504930427674737)
          ·
            refine ⟨2179513545378697820756053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906018060504930427674737 2179513545378697820756053)
            ·
              refine ⟨25541174359906615086985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2179513545378697820756053 25541174359906615086985)
              ·
                rfl

theorem cell22_2014521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 8].length) (baseStart_2014521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014521 prefixEnd_2014521 := by exact prefixLift 2014521
  have htrace : WordTrace (prefixWord ++ tailWord_2014521) baseStart_2014521 baseEnd_2014521 := by
    simpa [prefixWord, tailWord_2014521, baseEnd_2014521] using wordTrace_append hprefix tailTrace_2014521
  have hstable : (prefixWord ++ tailWord_2014521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014521).length < 2 ^ (prefixWord ++ tailWord_2014521).sum := by decide
  have hdescent : baseEnd_2014521 < baseStart_2014521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014557 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2014557 : Nat := 118140960795 + 2014557 * 2 ^ 59
def prefixEnd_2014557 : Nat := 4983230072969 + 3 ^ 40 * 2014557 * 2
def baseEnd_2014557 : Nat := 689624031253186513448485

theorem tailTrace_2014557 : CollatzResearch.WordTrace tailWord_2014557 prefixEnd_2014557 689624031253186513448485 := by
  unfold tailWord_2014557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73476930162611522788777925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48984620108407681859185283 73476930162611522788777925)
  ·
    refine ⟨13776924405489660522895861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73476930162611522788777925 13776924405489660522895861)
    ·
      refine ⟨1291586663014655674021487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13776924405489660522895861 1291586663014655674021487)
      ·
        refine ⟨1937379994521983511032231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291586663014655674021487 1937379994521983511032231)
        ·
          refine ⟨2906069991782975266548347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937379994521983511032231 2906069991782975266548347)
          ·
            refine ⟨4359104987674462899822521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906069991782975266548347 4359104987674462899822521)
            ·
              refine ⟨3269328740755847174866891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359104987674462899822521 3269328740755847174866891)
              ·
                refine ⟨4903993111133770762300337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269328740755847174866891 4903993111133770762300337)
                ·
                  refine ⟨3677994833350328071725253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903993111133770762300337 3677994833350328071725253)
                  ·
                    refine ⟨689624031253186513448485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677994833350328071725253 689624031253186513448485)
                    ·
                      rfl

theorem cell22_2014557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2014557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014557 prefixEnd_2014557 := by exact prefixLift 2014557
  have htrace : WordTrace (prefixWord ++ tailWord_2014557) baseStart_2014557 baseEnd_2014557 := by
    simpa [prefixWord, tailWord_2014557, baseEnd_2014557] using wordTrace_append hprefix tailTrace_2014557
  have hstable : (prefixWord ++ tailWord_2014557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014557).length < 2 ^ (prefixWord ++ tailWord_2014557).sum := by decide
  have hdescent : baseEnd_2014557 < baseStart_2014557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_2014579 : Nat := 118140960795 + 2014579 * 2 ^ 59
def prefixEnd_2014579 : Nat := 4983230072969 + 3 ^ 40 * 2014579 * 2
def baseEnd_2014579 : Nat := 689631562302785789398417

theorem tailTrace_2014579 : CollatzResearch.WordTrace tailWord_2014579 prefixEnd_2014579 689631562302785789398417 := by
  unfold tailWord_2014579
  simp only [CollatzResearch.WordTrace]
  refine ⟨73477732568531820546078791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48985155045687880364052527 73477732568531820546078791)
  ·
    refine ⟨110216598852797730819118187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73477732568531820546078791 110216598852797730819118187)
    ·
      refine ⟨165324898279196596228677281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110216598852797730819118187 165324898279196596228677281)
      ·
        refine ⟨123993673709397447171507961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165324898279196596228677281 123993673709397447171507961)
        ·
          refine ⟨92995255282048085378630971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123993673709397447171507961 92995255282048085378630971)
          ·
            refine ⟨139492882923072128067946457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92995255282048085378630971 139492882923072128067946457)
            ·
              refine ⟨104619662192304096050959843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139492882923072128067946457 104619662192304096050959843)
              ·
                refine ⟨156929493288456144076439765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104619662192304096050959843 156929493288456144076439765)
                ·
                  refine ⟨3678034998948190876791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 156929493288456144076439765 3678034998948190876791557)
                  ·
                    refine ⟨689631562302785789398417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678034998948190876791557 689631562302785789398417)
                    ·
                      rfl

theorem cell22_2014579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_2014579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014579 prefixEnd_2014579 := by exact prefixLift 2014579
  have htrace : WordTrace (prefixWord ++ tailWord_2014579) baseStart_2014579 baseEnd_2014579 := by
    simpa [prefixWord, tailWord_2014579, baseEnd_2014579] using wordTrace_append hprefix tailTrace_2014579
  have hstable : (prefixWord ++ tailWord_2014579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014579).length < 2 ^ (prefixWord ++ tailWord_2014579).sum := by decide
  have hdescent : baseEnd_2014579 < baseStart_2014579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014596 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2014596 : Nat := 118140960795 + 2014596 * 2 ^ 59
def prefixEnd_2014596 : Nat := 4983230072969 + 3 ^ 40 * 2014596 * 2
def baseEnd_2014596 : Nat := 689637381750203411723365

theorem tailTrace_2014596 : CollatzResearch.WordTrace tailWord_2014596 prefixEnd_2014596 689637381750203411723365 := by
  unfold tailWord_2014596
  simp only [CollatzResearch.WordTrace]
  refine ⟨36739176304735116224723821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48985568406313488299631761 36739176304735116224723821)
  ·
    refine ⟨13777191114275668584271433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36739176304735116224723821 13777191114275668584271433)
    ·
      refine ⟨10332893335706751438203575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13777191114275668584271433 10332893335706751438203575)
      ·
        refine ⟨15499340003560127157305363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332893335706751438203575 15499340003560127157305363)
        ·
          refine ⟨23249010005340190735958045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15499340003560127157305363 23249010005340190735958045)
          ·
            refine ⟨8718378752002571525984267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23249010005340190735958045 8718378752002571525984267)
            ·
              refine ⟨13077568128003857288976401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718378752002571525984267 13077568128003857288976401)
              ·
                refine ⟨9808176096002892966732301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13077568128003857288976401 9808176096002892966732301)
                ·
                  refine ⟨3678066036001084862524613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9808176096002892966732301 3678066036001084862524613)
                  ·
                    refine ⟨689637381750203411723365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678066036001084862524613 689637381750203411723365)
                    ·
                      rfl

theorem cell22_2014596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2014596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014596 prefixEnd_2014596 := by exact prefixLift 2014596
  have htrace : WordTrace (prefixWord ++ tailWord_2014596) baseStart_2014596 baseEnd_2014596 := by
    simpa [prefixWord, tailWord_2014596, baseEnd_2014596] using wordTrace_append hprefix tailTrace_2014596
  have hstable : (prefixWord ++ tailWord_2014596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014596).length < 2 ^ (prefixWord ++ tailWord_2014596).sum := by decide
  have hdescent : baseEnd_2014596 < baseStart_2014596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014609 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_2014609 : Nat := 118140960795 + 2014609 * 2 ^ 59
def prefixEnd_2014609 : Nat := 4983230072969 + 3 ^ 40 * 2014609 * 2
def baseEnd_2014609 : Nat := 689641831915875711148325

theorem tailTrace_2014609 : CollatzResearch.WordTrace tailWord_2014609 prefixEnd_2014609 689641831915875711148325 := by
  unfold tailWord_2014609
  simp only [CollatzResearch.WordTrace]
  refine ⟨73478826758423135669670881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48985884505615423779780587 73478826758423135669670881)
  ·
    refine ⟨55109120068817351752253161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73478826758423135669670881 55109120068817351752253161)
    ·
      refine ⟨41331840051613013814189871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55109120068817351752253161 41331840051613013814189871)
      ·
        refine ⟨61997760077419520721284807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41331840051613013814189871 61997760077419520721284807)
        ·
          refine ⟨92996640116129281081927211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61997760077419520721284807 92996640116129281081927211)
          ·
            refine ⟨139494960174193921622890817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92996640116129281081927211 139494960174193921622890817)
            ·
              refine ⟨104621220130645441217168113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139494960174193921622890817 104621220130645441217168113)
              ·
                refine ⟨78465915097984080912876085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104621220130645441217168113 78465915097984080912876085)
                ·
                  refine ⟨7356179540436007585582133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78465915097984080912876085 7356179540436007585582133)
                  ·
                    refine ⟨689641831915875711148325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356179540436007585582133 689641831915875711148325)
                    ·
                      rfl

theorem cell22_2014609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_2014609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014609 prefixEnd_2014609 := by exact prefixLift 2014609
  have htrace : WordTrace (prefixWord ++ tailWord_2014609) baseStart_2014609 baseEnd_2014609 := by
    simpa [prefixWord, tailWord_2014609, baseEnd_2014609] using wordTrace_append hprefix tailTrace_2014609
  have hstable : (prefixWord ++ tailWord_2014609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014609).length < 2 ^ (prefixWord ++ tailWord_2014609).sum := by decide
  have hdescent : baseEnd_2014609 < baseStart_2014609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014641 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2014641 : Nat := 118140960795 + 2014641 * 2 ^ 59
def prefixEnd_2014641 : Nat := 4983230072969 + 3 ^ 40 * 2014641 * 2
def baseEnd_2014641 : Nat := 689652786169838294348227

theorem tailTrace_2014641 : CollatzResearch.WordTrace tailWord_2014641 prefixEnd_2014641 689652786169838294348227 := by
  unfold tailWord_2014641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73479993894307205134835777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48986662596204803423223851 73479993894307205134835777)
  ·
    refine ⟨55109995420730403851126833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73479993894307205134835777 55109995420730403851126833)
    ·
      refine ⟨41332496565547802888345125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55109995420730403851126833 41332496565547802888345125)
      ·
        refine ⟨7749843106040213041564711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41332496565547802888345125 7749843106040213041564711)
        ·
          refine ⟨11624764659060319562347067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749843106040213041564711 11624764659060319562347067)
          ·
            refine ⟨17437146988590479343520601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624764659060319562347067 17437146988590479343520601)
            ·
              refine ⟨13077860241442859507640451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17437146988590479343520601 13077860241442859507640451)
              ·
                refine ⟨19616790362164289261460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13077860241442859507640451 19616790362164289261460677)
                ·
                  refine ⟨3678148192905804236523877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19616790362164289261460677 3678148192905804236523877)
                  ·
                    refine ⟨689652786169838294348227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678148192905804236523877 689652786169838294348227)
                    ·
                      rfl

theorem cell22_2014641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2014641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014641 prefixEnd_2014641 := by exact prefixLift 2014641
  have htrace : WordTrace (prefixWord ++ tailWord_2014641) baseStart_2014641 baseEnd_2014641 := by
    simpa [prefixWord, tailWord_2014641, baseEnd_2014641] using wordTrace_append hprefix tailTrace_2014641
  have hstable : (prefixWord ++ tailWord_2014641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014641).length < 2 ^ (prefixWord ++ tailWord_2014641).sum := by decide
  have hdescent : baseEnd_2014641 < baseStart_2014641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014660 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2014660 : Nat := 118140960795 + 2014660 * 2 ^ 59
def prefixEnd_2014660 : Nat := 4983230072969 + 3 ^ 40 * 2014660 * 2
def baseEnd_2014660 : Nat := 689659290258128578123169

theorem tailTrace_2014660 : CollatzResearch.WordTrace tailWord_2014660 prefixEnd_2014660 689659290258128578123169 := by
  unfold tailWord_2014660
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740343440619185689888717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48987124587492247586518289 36740343440619185689888717)
  ·
    refine ⟨13777628790232194633708269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36740343440619185689888717 13777628790232194633708269)
    ·
      refine ⟨5166610796337072987640601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13777628790232194633708269 5166610796337072987640601)
      ·
        refine ⟨3874958097252804740730451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5166610796337072987640601 3874958097252804740730451)
        ·
          refine ⟨5812437145879207111095677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874958097252804740730451 5812437145879207111095677)
          ·
            refine ⟨2179663929704702666660879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5812437145879207111095677 2179663929704702666660879)
            ·
              refine ⟨3269495894557053999991319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179663929704702666660879 3269495894557053999991319)
              ·
                refine ⟨4904243841835580999986979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269495894557053999991319 4904243841835580999986979)
                ·
                  refine ⟨7356365762753371499980469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904243841835580999986979 7356365762753371499980469)
                  ·
                    refine ⟨689659290258128578123169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356365762753371499980469 689659290258128578123169)
                    ·
                      rfl

theorem cell22_2014660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2014660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014660 prefixEnd_2014660 := by exact prefixLift 2014660
  have htrace : WordTrace (prefixWord ++ tailWord_2014660) baseStart_2014660 baseEnd_2014660 := by
    simpa [prefixWord, tailWord_2014660, baseEnd_2014660] using wordTrace_append hprefix tailTrace_2014660
  have hstable : (prefixWord ++ tailWord_2014660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014660).length < 2 ^ (prefixWord ++ tailWord_2014660).sum := by decide
  have hdescent : baseEnd_2014660 < baseStart_2014660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014705 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_2014705 : Nat := 118140960795 + 2014705 * 2 ^ 59
def prefixEnd_2014705 : Nat := 4983230072969 + 3 ^ 40 * 2014705 * 2
def baseEnd_2014705 : Nat := 689674694677763460748031

theorem tailTrace_2014705 : CollatzResearch.WordTrace tailWord_2014705 prefixEnd_2014705 689674694677763460748031 := by
  unfold tailWord_2014705
  simp only [CollatzResearch.WordTrace]
  refine ⟨73482328166075344065165569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48988218777383562710110379 73482328166075344065165569)
  ·
    refine ⟨55111746124556508048874177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73482328166075344065165569 55111746124556508048874177)
    ·
      refine ⟨41333809593417381036655633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55111746124556508048874177 41333809593417381036655633)
      ·
        refine ⟨31000357195063035777491725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41333809593417381036655633 31000357195063035777491725)
        ·
          refine ⟨11625133948148638416559397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31000357195063035777491725 11625133948148638416559397)
          ·
            refine ⟨2179712615277869703104887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11625133948148638416559397 2179712615277869703104887)
            ·
              refine ⟨3269568922916804554657331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179712615277869703104887 3269568922916804554657331)
              ·
                refine ⟨4904353384375206831985997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269568922916804554657331 4904353384375206831985997)
                ·
                  refine ⟨1839132519140702561994749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4904353384375206831985997 1839132519140702561994749)
                  ·
                    refine ⟨689674694677763460748031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839132519140702561994749 689674694677763460748031)
                    ·
                      rfl

theorem cell22_2014705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_2014705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014705 prefixEnd_2014705 := by exact prefixLift 2014705
  have htrace : WordTrace (prefixWord ++ tailWord_2014705) baseStart_2014705 baseEnd_2014705 := by
    simpa [prefixWord, tailWord_2014705, baseEnd_2014705] using wordTrace_append hprefix tailTrace_2014705
  have hstable : (prefixWord ++ tailWord_2014705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014705).length < 2 ^ (prefixWord ++ tailWord_2014705).sum := by decide
  have hdescent : baseEnd_2014705 < baseStart_2014705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014716 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2014716 : Nat := 118140960795 + 2014716 * 2 ^ 59
def prefixEnd_2014716 : Nat := 4983230072969 + 3 ^ 40 * 2014716 * 2
def baseEnd_2014716 : Nat := 689678460202563098722997

theorem tailTrace_2014716 : CollatzResearch.WordTrace tailWord_2014716 prefixEnd_2014716 689678460202563098722997 := by
  unfold tailWord_2014716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36741364684517746471908001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48988486246023661962544001 36741364684517746471908001)
  ·
    refine ⟨27556023513388309853931001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36741364684517746471908001 27556023513388309853931001)
    ·
      refine ⟨20667017635041232390448251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27556023513388309853931001 20667017635041232390448251)
      ·
        refine ⟨31000526452561848585672377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20667017635041232390448251 31000526452561848585672377)
        ·
          refine ⟨23250394839421386439254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31000526452561848585672377 23250394839421386439254283)
          ·
            refine ⟨34875592259132079658881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250394839421386439254283 34875592259132079658881425)
            ·
              refine ⟨26156694194349059744161069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34875592259132079658881425 26156694194349059744161069)
              ·
                refine ⟨9808760322880897404060401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26156694194349059744161069 9808760322880897404060401)
                ·
                  refine ⟨7356570242160673053045301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808760322880897404060401 7356570242160673053045301)
                  ·
                    refine ⟨689678460202563098722997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356570242160673053045301 689678460202563098722997)
                    ·
                      rfl

theorem cell22_2014716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2014716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014716 prefixEnd_2014716 := by exact prefixLift 2014716
  have htrace : WordTrace (prefixWord ++ tailWord_2014716) baseStart_2014716 baseEnd_2014716 := by
    simpa [prefixWord, tailWord_2014716, baseEnd_2014716] using wordTrace_append hprefix tailTrace_2014716
  have hstable : (prefixWord ++ tailWord_2014716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014716).length < 2 ^ (prefixWord ++ tailWord_2014716).sum := by decide
  have hdescent : baseEnd_2014716 < baseStart_2014716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014778 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_2014778 : Nat := 118140960795 + 2014778 * 2 ^ 59
def prefixEnd_2014778 : Nat := 4983230072969 + 3 ^ 40 * 2014778 * 2
def baseEnd_2014778 : Nat := 689699684069615603672807

theorem tailTrace_2014778 : CollatzResearch.WordTrace tailWord_2014778 prefixEnd_2014778 689699684069615603672807 := by
  unfold tailWord_2014778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371247673702719383143247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48989993796540585021715325 18371247673702719383143247)
  ·
    refine ⟨27556871510554079074714871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371247673702719383143247 27556871510554079074714871)
    ·
      refine ⟨41335307265831118612072307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27556871510554079074714871 41335307265831118612072307)
      ·
        refine ⟨62002960898746677918108461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41335307265831118612072307 62002960898746677918108461)
        ·
          refine ⟨23251110337030004219290673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62002960898746677918108461 23251110337030004219290673)
          ·
            refine ⟨17438332752772503164468005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23251110337030004219290673 17438332752772503164468005)
            ·
              refine ⟨3269687391144844343337751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17438332752772503164468005 3269687391144844343337751)
              ·
                refine ⟨4904531086717266515006627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269687391144844343337751 4904531086717266515006627)
                ·
                  refine ⟨7356796630075899772509941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904531086717266515006627 7356796630075899772509941)
                  ·
                    refine ⟨689699684069615603672807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356796630075899772509941 689699684069615603672807)
                    ·
                      rfl

theorem cell22_2014778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_2014778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014778 prefixEnd_2014778 := by exact prefixLift 2014778
  have htrace : WordTrace (prefixWord ++ tailWord_2014778) baseStart_2014778 baseEnd_2014778 := by
    simpa [prefixWord, tailWord_2014778, baseEnd_2014778] using wordTrace_append hprefix tailTrace_2014778
  have hstable : (prefixWord ++ tailWord_2014778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014778).length < 2 ^ (prefixWord ++ tailWord_2014778).sum := by decide
  have hdescent : baseEnd_2014778 < baseStart_2014778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014812 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2014812 : Nat := 118140960795 + 2014812 * 2 ^ 59
def prefixEnd_2014812 : Nat := 4983230072969 + 3 ^ 40 * 2014812 * 2
def baseEnd_2014812 : Nat := 689711322964450848322703

theorem tailTrace_2014812 : CollatzResearch.WordTrace tailWord_2014812 prefixEnd_2014812 689711322964450848322703 := by
  unfold tailWord_2014812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36743115388343850669655345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48990820517791800892873793 36743115388343850669655345)
  ·
    refine ⟨27557336541257888002241509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36743115388343850669655345 27557336541257888002241509)
    ·
      refine ⟨5167000601485854000420283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27557336541257888002241509 5167000601485854000420283)
      ·
        refine ⟨7750500902228781000630425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167000601485854000420283 7750500902228781000630425)
        ·
          refine ⟨5812875676671585750472819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750500902228781000630425 5812875676671585750472819)
          ·
            refine ⟨8719313515007378625709229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812875676671585750472819 8719313515007378625709229)
            ·
              refine ⟨3269742568127766984640961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8719313515007378625709229 3269742568127766984640961)
              ·
                refine ⟨2452306926095825238480721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269742568127766984640961 2452306926095825238480721)
                ·
                  refine ⟨1839230194571868928860541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452306926095825238480721 1839230194571868928860541)
                  ·
                    refine ⟨689711322964450848322703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839230194571868928860541 689711322964450848322703)
                    ·
                      rfl

theorem cell22_2014812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2014812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014812 prefixEnd_2014812 := by exact prefixLift 2014812
  have htrace : WordTrace (prefixWord ++ tailWord_2014812) baseStart_2014812 baseEnd_2014812 := by
    simpa [prefixWord, tailWord_2014812, baseEnd_2014812] using wordTrace_append hprefix tailTrace_2014812
  have hstable : (prefixWord ++ tailWord_2014812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014812).length < 2 ^ (prefixWord ++ tailWord_2014812).sum := by decide
  have hdescent : baseEnd_2014812 < baseStart_2014812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014829 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2014829 : Nat := 118140960795 + 2014829 * 2 ^ 59
def prefixEnd_2014829 : Nat := 4983230072969 + 3 ^ 40 * 2014829 * 2
def baseEnd_2014829 : Nat := 689717142411868470647651

theorem tailTrace_2014829 : CollatzResearch.WordTrace tailWord_2014829 prefixEnd_2014829 689717142411868470647651 := by
  unfold tailWord_2014829
  simp only [CollatzResearch.WordTrace]
  refine ⟨73486850817626113242679541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48991233878417408828453027 73486850817626113242679541)
  ·
    refine ⟨6889392264152448116501207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73486850817626113242679541 6889392264152448116501207)
    ·
      refine ⟨10334088396228672174751811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889392264152448116501207 10334088396228672174751811)
      ·
        refine ⟨15501132594343008262127717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334088396228672174751811 15501132594343008262127717)
        ·
          refine ⟨2906462361439314049148947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15501132594343008262127717 2906462361439314049148947)
          ·
            refine ⟨4359693542158971073723421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906462361439314049148947 4359693542158971073723421)
            ·
              refine ⟨1634885078309614152646283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4359693542158971073723421 1634885078309614152646283)
              ·
                refine ⟨2452327617464421228969425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634885078309614152646283 2452327617464421228969425)
                ·
                  refine ⟨1839245713098315921727069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452327617464421228969425 1839245713098315921727069)
                  ·
                    refine ⟨689717142411868470647651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839245713098315921727069 689717142411868470647651)
                    ·
                      rfl

theorem cell22_2014829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2014829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014829 prefixEnd_2014829 := by exact prefixLift 2014829
  have htrace : WordTrace (prefixWord ++ tailWord_2014829) baseStart_2014829 baseEnd_2014829 := by
    simpa [prefixWord, tailWord_2014829, baseEnd_2014829] using wordTrace_append hprefix tailTrace_2014829
  have hstable : (prefixWord ++ tailWord_2014829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014829).length < 2 ^ (prefixWord ++ tailWord_2014829).sum := by decide
  have hdescent : baseEnd_2014829 < baseStart_2014829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014857 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_2014857 : Nat := 118140960795 + 2014857 * 2 ^ 59
def prefixEnd_2014857 : Nat := 4983230072969 + 3 ^ 40 * 2014857 * 2
def baseEnd_2014857 : Nat := 689726727384085730947565

theorem tailTrace_2014857 : CollatzResearch.WordTrace tailWord_2014857 prefixEnd_2014857 689726727384085730947565 := by
  unfold tailWord_2014857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73487872061524674024698825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48991914707683116016465883 73487872061524674024698825)
  ·
    refine ⟨55115904046143505518524119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73487872061524674024698825 55115904046143505518524119)
    ·
      refine ⟨82673856069215258277786179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55115904046143505518524119 82673856069215258277786179)
      ·
        refine ⟨124010784103822887416679269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82673856069215258277786179 124010784103822887416679269)
        ·
          refine ⟨23252022019466791390627363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124010784103822887416679269 23252022019466791390627363)
          ·
            refine ⟨34878033029200187085941045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23252022019466791390627363 34878033029200187085941045)
            ·
              refine ⟨3269815596487517539306973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34878033029200187085941045 3269815596487517539306973)
              ·
                refine ⟨1226180848682819077240115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269815596487517539306973 1226180848682819077240115)
                ·
                  refine ⟨1839271273024228615860173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226180848682819077240115 1839271273024228615860173)
                  ·
                    refine ⟨689726727384085730947565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839271273024228615860173 689726727384085730947565)
                    ·
                      rfl

theorem cell22_2014857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_2014857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014857 prefixEnd_2014857 := by exact prefixLift 2014857
  have htrace : WordTrace (prefixWord ++ tailWord_2014857) baseStart_2014857 baseEnd_2014857 := by
    simpa [prefixWord, tailWord_2014857, baseEnd_2014857] using wordTrace_append hprefix tailTrace_2014857
  have hstable : (prefixWord ++ tailWord_2014857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014857).length < 2 ^ (prefixWord ++ tailWord_2014857).sum := by decide
  have hdescent : baseEnd_2014857 < baseStart_2014857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014883 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_2014883 : Nat := 118140960795 + 2014883 * 2 ^ 59
def prefixEnd_2014883 : Nat := 4983230072969 + 3 ^ 40 * 2014883 * 2
def baseEnd_2014883 : Nat := 689735627715430329797485

theorem tailTrace_2014883 : CollatzResearch.WordTrace tailWord_2014883 prefixEnd_2014883 689735627715430329797485 := by
  unfold tailWord_2014883
  simp only [CollatzResearch.WordTrace]
  refine ⟨73488820359430480465145303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48992546906286986976763535 73488820359430480465145303)
  ·
    refine ⟨110233230539145720697717955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73488820359430480465145303 110233230539145720697717955)
    ·
      refine ⟨165349845808718581046576933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110233230539145720697717955 165349845808718581046576933)
      ·
        refine ⟨31003096089134733946233175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165349845808718581046576933 31003096089134733946233175)
        ·
          refine ⟨46504644133702100919349763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31003096089134733946233175 46504644133702100919349763)
          ·
            refine ⟨69756966200553151379024645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46504644133702100919349763 69756966200553151379024645)
            ·
              refine ⟨13079431162603715883567121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69756966200553151379024645 13079431162603715883567121)
              ·
                refine ⟨9809573371952786912675341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079431162603715883567121 9809573371952786912675341)
                ·
                  refine ⟨3678590014482295092253253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9809573371952786912675341 3678590014482295092253253)
                  ·
                    refine ⟨689735627715430329797485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678590014482295092253253 689735627715430329797485)
                    ·
                      rfl

theorem cell22_2014883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_2014883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014883 prefixEnd_2014883 := by exact prefixLift 2014883
  have htrace : WordTrace (prefixWord ++ tailWord_2014883) baseStart_2014883 baseEnd_2014883 := by
    simpa [prefixWord, tailWord_2014883, baseEnd_2014883] using wordTrace_append hprefix tailTrace_2014883
  have hstable : (prefixWord ++ tailWord_2014883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014883).length < 2 ^ (prefixWord ++ tailWord_2014883).sum := by decide
  have hdescent : baseEnd_2014883 < baseStart_2014883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014898 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2014898 : Nat := 118140960795 + 2014898 * 2 ^ 59
def prefixEnd_2014898 : Nat := 4983230072969 + 3 ^ 40 * 2014898 * 2
def baseEnd_2014898 : Nat := 229913587507325096890813

theorem tailTrace_2014898 : CollatzResearch.WordTrace tailWord_2014898 prefixEnd_2014898 229913587507325096890813 := by
  unfold tailWord_2014898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372341863594034506735337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48992911636250758684627565 18372341863594034506735337)
  ·
    refine ⟨13779256397695525880051503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18372341863594034506735337 13779256397695525880051503)
    ·
      refine ⟨20668884596543288820077255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779256397695525880051503 20668884596543288820077255)
      ·
        refine ⟨31003326894814933230115883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668884596543288820077255 31003326894814933230115883)
        ·
          refine ⟨46504990342222399845173825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31003326894814933230115883 46504990342222399845173825)
          ·
            refine ⟨34878742756666799883880369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46504990342222399845173825 34878742756666799883880369)
            ·
              refine ⟨26159057067500099912910277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34878742756666799883880369 26159057067500099912910277)
              ·
                refine ⟨4904823200156268733670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26159057067500099912910277 4904823200156268733670677)
                ·
                  refine ⟨229913587507325096890813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4904823200156268733670677 229913587507325096890813)
                  ·
                    rfl

theorem cell22_2014898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2014898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014898 prefixEnd_2014898 := by exact prefixLift 2014898
  have htrace : WordTrace (prefixWord ++ tailWord_2014898) baseStart_2014898 baseEnd_2014898 := by
    simpa [prefixWord, tailWord_2014898, baseEnd_2014898] using wordTrace_append hprefix tailTrace_2014898
  have hstable : (prefixWord ++ tailWord_2014898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014898).length < 2 ^ (prefixWord ++ tailWord_2014898).sum := by decide
  have hdescent : baseEnd_2014898 < baseStart_2014898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014928 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_2014928 : Nat := 118140960795 + 2014928 * 2 ^ 59
def prefixEnd_2014928 : Nat := 4983230072969 + 3 ^ 40 * 2014928 * 2
def baseEnd_2014928 : Nat := 689751032135065212422347

theorem tailTrace_2014928 : CollatzResearch.WordTrace tailWord_2014928 prefixEnd_2014928 689751032135065212422347 := by
  unfold tailWord_2014928
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745230822133726575266719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48993641096178302100355625 36745230822133726575266719)
  ·
    refine ⟨55117846233200589862900079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36745230822133726575266719 55117846233200589862900079)
    ·
      refine ⟨82676769349800884794350119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55117846233200589862900079 82676769349800884794350119)
      ·
        refine ⟨124015154024701327191525179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82676769349800884794350119 124015154024701327191525179)
        ·
          refine ⟨186022731037051990787287769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124015154024701327191525179 186022731037051990787287769)
          ·
            refine ⟨139517048277788993090465827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186022731037051990787287769 139517048277788993090465827)
            ·
              refine ⟨209275572416683489635698741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139517048277788993090465827 209275572416683489635698741)
              ·
                refine ⟨19619584914064077153346757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209275572416683489635698741 19619584914064077153346757)
                ·
                  refine ⟨3678672171387014466252517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19619584914064077153346757 3678672171387014466252517)
                  ·
                    refine ⟨689751032135065212422347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678672171387014466252517 689751032135065212422347)
                    ·
                      rfl

theorem cell22_2014928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_2014928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014928 prefixEnd_2014928 := by exact prefixLift 2014928
  have htrace : WordTrace (prefixWord ++ tailWord_2014928) baseStart_2014928 baseEnd_2014928 := by
    simpa [prefixWord, tailWord_2014928, baseEnd_2014928] using wordTrace_append hprefix tailTrace_2014928
  have hstable : (prefixWord ++ tailWord_2014928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014928).length < 2 ^ (prefixWord ++ tailWord_2014928).sum := by decide
  have hdescent : baseEnd_2014928 < baseStart_2014928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014947 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_2014947 : Nat := 118140960795 + 2014947 * 2 ^ 59
def prefixEnd_2014947 : Nat := 4983230072969 + 3 ^ 40 * 2014947 * 2
def baseEnd_2014947 : Nat := 689757536223355496197289

theorem tailTrace_2014947 : CollatzResearch.WordTrace tailWord_2014947 prefixEnd_2014947 689757536223355496197289 := by
  unfold tailWord_2014947
  simp only [CollatzResearch.WordTrace]
  refine ⟨73491154631198619395475095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48994103087465746263650063 73491154631198619395475095)
  ·
    refine ⟨110236731946797929093212643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73491154631198619395475095 110236731946797929093212643)
    ·
      refine ⟨165355097920196893639818965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110236731946797929093212643 165355097920196893639818965)
      ·
        refine ⟨3875510107504614694683257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 165355097920196893639818965 3875510107504614694683257)
        ·
          refine ⟨2906632580628461021012443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875510107504614694683257 2906632580628461021012443)
          ·
            refine ⟨4359948870942691531518665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906632580628461021012443 4359948870942691531518665)
            ·
              refine ⟨3269961653207018648638999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359948870942691531518665 3269961653207018648638999)
              ·
                refine ⟨4904942479810527972958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269961653207018648638999 4904942479810527972958499)
                ·
                  refine ⟨7357413719715791959437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904942479810527972958499 7357413719715791959437749)
                  ·
                    refine ⟨689757536223355496197289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7357413719715791959437749 689757536223355496197289)
                    ·
                      rfl

theorem cell22_2014947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_2014947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014947 prefixEnd_2014947 := by exact prefixLift 2014947
  have htrace : WordTrace (prefixWord ++ tailWord_2014947) baseStart_2014947 baseEnd_2014947 := by
    simpa [prefixWord, tailWord_2014947, baseEnd_2014947] using wordTrace_append hprefix tailTrace_2014947
  have hstable : (prefixWord ++ tailWord_2014947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014947).length < 2 ^ (prefixWord ++ tailWord_2014947).sum := by decide
  have hdescent : baseEnd_2014947 < baseStart_2014947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014964 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2014964 : Nat := 118140960795 + 2014964 * 2 ^ 59
def prefixEnd_2014964 : Nat := 4983230072969 + 3 ^ 40 * 2014964 * 2
def baseEnd_2014964 : Nat := 689763355670773118522237

theorem tailTrace_2014964 : CollatzResearch.WordTrace tailWord_2014964 prefixEnd_2014964 689763355670773118522237 := by
  unfold tailWord_2014964
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745887336068515649421973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48994516448091354199229297 36745887336068515649421973)
  ·
    refine ⟨1722463468878211671066655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36745887336068515649421973 1722463468878211671066655)
    ·
      refine ⟨2583695203317317506599983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722463468878211671066655 2583695203317317506599983)
      ·
        refine ⟨3875542804975976259899975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583695203317317506599983 3875542804975976259899975)
        ·
          refine ⟨5813314207463964389849963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875542804975976259899975 5813314207463964389849963)
          ·
            refine ⟨8719971311195946584774945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813314207463964389849963 8719971311195946584774945)
            ·
              refine ⟨6539978483396959938581209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8719971311195946584774945 6539978483396959938581209)
              ·
                refine ⟨4904983862547719953935907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539978483396959938581209 4904983862547719953935907)
                ·
                  refine ⟨7357475793821579930903861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904983862547719953935907 7357475793821579930903861)
                  ·
                    refine ⟨689763355670773118522237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7357475793821579930903861 689763355670773118522237)
                    ·
                      rfl

theorem cell22_2014964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2014964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014964 prefixEnd_2014964 := by exact prefixLift 2014964
  have htrace : WordTrace (prefixWord ++ tailWord_2014964) baseStart_2014964 baseEnd_2014964 := by
    simpa [prefixWord, tailWord_2014964, baseEnd_2014964] using wordTrace_append hprefix tailTrace_2014964
  have hstable : (prefixWord ++ tailWord_2014964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014964).length < 2 ^ (prefixWord ++ tailWord_2014964).sum := by decide
  have hdescent : baseEnd_2014964 < baseStart_2014964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014973 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2014973 : Nat := 118140960795 + 2014973 * 2 ^ 59
def prefixEnd_2014973 : Nat := 4983230072969 + 3 ^ 40 * 2014973 * 2
def baseEnd_2014973 : Nat := 689766436554700095047209

theorem tailTrace_2014973 : CollatzResearch.WordTrace tailWord_2014973 prefixEnd_2014973 689766436554700095047209 := by
  unfold tailWord_2014973
  simp only [CollatzResearch.WordTrace]
  refine ⟨73492102929104425835921573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48994735286069617223947715 73492102929104425835921573)
  ·
    refine ⟨13779769299207079844235295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73492102929104425835921573 13779769299207079844235295)
    ·
      refine ⟨20669653948810619766352943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779769299207079844235295 20669653948810619766352943)
      ·
        refine ⟨31004480923215929649529415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20669653948810619766352943 31004480923215929649529415)
        ·
          refine ⟨46506721384823894474294123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31004480923215929649529415 46506721384823894474294123)
          ·
            refine ⟨69760082077235841711441185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46506721384823894474294123 69760082077235841711441185)
            ·
              refine ⟨52320061557926881283580889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69760082077235841711441185 52320061557926881283580889)
              ·
                refine ⟨39240046168445160962685667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52320061557926881283580889 39240046168445160962685667)
                ·
                  refine ⟨58860069252667741444028501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39240046168445160962685667 58860069252667741444028501)
                  ·
                    refine ⟨689766436554700095047209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58860069252667741444028501 689766436554700095047209)
                    ·
                      rfl

theorem cell22_2014973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2014973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2014973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2014973 prefixEnd_2014973 := by exact prefixLift 2014973
  have htrace : WordTrace (prefixWord ++ tailWord_2014973) baseStart_2014973 baseEnd_2014973 := by
    simpa [prefixWord, tailWord_2014973, baseEnd_2014973] using wordTrace_append hprefix tailTrace_2014973
  have hstable : (prefixWord ++ tailWord_2014973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014973).length < 2 ^ (prefixWord ++ tailWord_2014973).sum := by decide
  have hdescent : baseEnd_2014973 < baseStart_2014973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015026 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2015026 : Nat := 118140960795 + 2015026 * 2 ^ 59
def prefixEnd_2015026 : Nat := 4983230072969 + 3 ^ 40 * 2015026 * 2
def baseEnd_2015026 : Nat := 689784579537825623472047

theorem tailTrace_2015026 : CollatzResearch.WordTrace tailWord_2015026 prefixEnd_2015026 689784579537825623472047 := by
  unfold tailWord_2015026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373508999478103971900233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48996023998608277258400621 18373508999478103971900233)
  ·
    refine ⟨13780131749608577978925175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18373508999478103971900233 13780131749608577978925175)
    ·
      refine ⟨20670197624412866968387763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13780131749608577978925175 20670197624412866968387763)
      ·
        refine ⟨31005296436619300452581645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20670197624412866968387763 31005296436619300452581645)
        ·
          refine ⟨11626986163732237669718117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31005296436619300452581645 11626986163732237669718117)
          ·
            refine ⟨2180059905699794563072147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11626986163732237669718117 2180059905699794563072147)
            ·
              refine ⟨3270089858549691844608221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180059905699794563072147 3270089858549691844608221)
              ·
                refine ⟨1226283696956134441728083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3270089858549691844608221 1226283696956134441728083)
                ·
                  refine ⟨1839425545434201662592125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226283696956134441728083 1839425545434201662592125)
                  ·
                    refine ⟨689784579537825623472047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839425545434201662592125 689784579537825623472047)
                    ·
                      rfl

theorem cell22_2015026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2015026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015026 prefixEnd_2015026 := by exact prefixLift 2015026
  have htrace : WordTrace (prefixWord ++ tailWord_2015026) baseStart_2015026 baseEnd_2015026 := by
    simpa [prefixWord, tailWord_2015026, baseEnd_2015026] using wordTrace_append hprefix tailTrace_2015026
  have hstable : (prefixWord ++ tailWord_2015026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015026).length < 2 ^ (prefixWord ++ tailWord_2015026).sum := by decide
  have hdescent : baseEnd_2015026 < baseStart_2015026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015065 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_2015065 : Nat := 118140960795 + 2015065 * 2 ^ 59
def prefixEnd_2015065 : Nat := 4983230072969 + 3 ^ 40 * 2015065 * 2
def baseEnd_2015065 : Nat := 689797930034842521746927

theorem tailTrace_2015065 : CollatzResearch.WordTrace tailWord_2015065 prefixEnd_2015065 689797930034842521746927 := by
  unfold tailWord_2015065
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495458444771125548270649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48996972296514083698847099 73495458444771125548270649)
  ·
    refine ⟨55121593833578344161202987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73495458444771125548270649 55121593833578344161202987)
    ·
      refine ⟨82682390750367516241804481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55121593833578344161202987 82682390750367516241804481)
      ·
        refine ⟨62011793062775637181353361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82682390750367516241804481 62011793062775637181353361)
        ·
          refine ⟨46508844797081727886015021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62011793062775637181353361 46508844797081727886015021)
          ·
            refine ⟨17440816798905647957255633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46508844797081727886015021 17440816798905647957255633)
            ·
              refine ⟨13080612599179235967941725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17440816798905647957255633 13080612599179235967941725)
              ·
                refine ⟨4905229724692213487978147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13080612599179235967941725 4905229724692213487978147)
                ·
                  refine ⟨7357844587038320231967221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905229724692213487978147 7357844587038320231967221)
                  ·
                    refine ⟨689797930034842521746927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7357844587038320231967221 689797930034842521746927)
                    ·
                      rfl

theorem cell22_2015065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_2015065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015065 prefixEnd_2015065 := by exact prefixLift 2015065
  have htrace : WordTrace (prefixWord ++ tailWord_2015065) baseStart_2015065 baseEnd_2015065 := by
    simpa [prefixWord, tailWord_2015065, baseEnd_2015065] using wordTrace_append hprefix tailTrace_2015065
  have hstable : (prefixWord ++ tailWord_2015065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015065).length < 2 ^ (prefixWord ++ tailWord_2015065).sum := by decide
  have hdescent : baseEnd_2015065 < baseStart_2015065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015086 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2015086 : Nat := 118140960795 + 2015086 * 2 ^ 59
def prefixEnd_2015086 : Nat := 4983230072969 + 3 ^ 40 * 2015086 * 2
def baseEnd_2015086 : Nat := 689805118764005466971863

theorem tailTrace_2015086 : CollatzResearch.WordTrace tailWord_2015086 prefixEnd_2015086 689805118764005466971863 := by
  unfold tailWord_2015086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187028047211880766848139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48997482918463364089856741 9187028047211880766848139)
  ·
    refine ⟨13780542070817821150272209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187028047211880766848139 13780542070817821150272209)
    ·
      refine ⟨10335406553113365862704157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13780542070817821150272209 10335406553113365862704157)
      ·
        refine ⟨3875777457417512198514059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10335406553113365862704157 3875777457417512198514059)
        ·
          refine ⟨5813666186126268297771089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875777457417512198514059 5813666186126268297771089)
          ·
            refine ⟨4360249639594701223328317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813666186126268297771089 4360249639594701223328317)
            ·
              refine ⟨1635093614848012958748119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360249639594701223328317 1635093614848012958748119)
              ·
                refine ⟨2452640422272019438122179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635093614848012958748119 2452640422272019438122179)
                ·
                  refine ⟨3678960633408029157183269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452640422272019438122179 3678960633408029157183269)
                  ·
                    refine ⟨689805118764005466971863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678960633408029157183269 689805118764005466971863)
                    ·
                      rfl

theorem cell22_2015086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2015086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015086 prefixEnd_2015086 := by exact prefixLift 2015086
  have htrace : WordTrace (prefixWord ++ tailWord_2015086) baseStart_2015086 baseEnd_2015086 := by
    simpa [prefixWord, tailWord_2015086, baseEnd_2015086] using wordTrace_append hprefix tailTrace_2015086
  have hstable : (prefixWord ++ tailWord_2015086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015086).length < 2 ^ (prefixWord ++ tailWord_2015086).sum := by decide
  have hdescent : baseEnd_2015086 < baseStart_2015086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015125 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2015125 : Nat := 118140960795 + 2015125 * 2 ^ 59
def prefixEnd_2015125 : Nat := 4983230072969 + 3 ^ 40 * 2015125 * 2
def baseEnd_2015125 : Nat := 689818469261022365246743

theorem tailTrace_2015125 : CollatzResearch.WordTrace tailWord_2015125 prefixEnd_2015125 689818469261022365246743 := by
  unfold tailWord_2015125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73497646824553755795454829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48998431216369170530303219 73497646824553755795454829)
  ·
    refine ⟨27561617559207658423295561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73497646824553755795454829 27561617559207658423295561)
    ·
      refine ⟨20671213169405743817471671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27561617559207658423295561 20671213169405743817471671)
      ·
        refine ⟨31006819754108615726207507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671213169405743817471671 31006819754108615726207507)
        ·
          refine ⟨46510229631162923589311261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31006819754108615726207507 46510229631162923589311261)
          ·
            refine ⟨17441336111686096345991723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46510229631162923589311261 17441336111686096345991723)
            ·
              refine ⟨26162004167529144518987585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441336111686096345991723 26162004167529144518987585)
              ·
                refine ⟨19621503125646858389240689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26162004167529144518987585 19621503125646858389240689)
                ·
                  refine ⟨14716127344235143791930517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19621503125646858389240689 14716127344235143791930517)
                  ·
                    refine ⟨689818469261022365246743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14716127344235143791930517 689818469261022365246743)
                    ·
                      rfl

theorem cell22_2015125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2015125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015125 prefixEnd_2015125 := by exact prefixLift 2015125
  have htrace : WordTrace (prefixWord ++ tailWord_2015125) baseStart_2015125 baseEnd_2015125 := by
    simpa [prefixWord, tailWord_2015125, baseEnd_2015125] using wordTrace_append hprefix tailTrace_2015125
  have hstable : (prefixWord ++ tailWord_2015125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015125).length < 2 ^ (prefixWord ++ tailWord_2015125).sum := by decide
  have hdescent : baseEnd_2015125 < baseStart_2015125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015127 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2015127 : Nat := 118140960795 + 2015127 * 2 ^ 59
def prefixEnd_2015127 : Nat := 4983230072969 + 3 ^ 40 * 2015127 * 2
def baseEnd_2015127 : Nat := 689819153901895026696737

theorem tailTrace_2015127 : CollatzResearch.WordTrace tailWord_2015127 prefixEnd_2015127 689819153901895026696737 := by
  unfold tailWord_2015127
  simp only [CollatzResearch.WordTrace]
  refine ⟨73497719770546510137027635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48998479847031006758018423 73497719770546510137027635)
  ·
    refine ⟨110246579655819765205541453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73497719770546510137027635 110246579655819765205541453)
    ·
      refine ⟨41342467370932411952078045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110246579655819765205541453 41342467370932411952078045)
      ·
        refine ⟨15503425264099654482029267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41342467370932411952078045 15503425264099654482029267)
        ·
          refine ⟨23255137896149481723043901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503425264099654482029267 23255137896149481723043901)
          ·
            refine ⟨8720676711056055646141463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23255137896149481723043901 8720676711056055646141463)
            ·
              refine ⟨13081015066584083469212195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720676711056055646141463 13081015066584083469212195)
              ·
                refine ⟨19621522599876125203818293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13081015066584083469212195 19621522599876125203818293)
                ·
                  refine ⟨1839517743738386737857965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19621522599876125203818293 1839517743738386737857965)
                  ·
                    refine ⟨689819153901895026696737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839517743738386737857965 689819153901895026696737)
                    ·
                      rfl

theorem cell22_2015127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2015127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015127 prefixEnd_2015127 := by exact prefixLift 2015127
  have htrace : WordTrace (prefixWord ++ tailWord_2015127) baseStart_2015127 baseEnd_2015127 := by
    simpa [prefixWord, tailWord_2015127, baseEnd_2015127] using wordTrace_append hprefix tailTrace_2015127
  have hstable : (prefixWord ++ tailWord_2015127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015127).length < 2 ^ (prefixWord ++ tailWord_2015127).sum := by decide
  have hdescent : baseEnd_2015127 < baseStart_2015127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015155 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_2015155 : Nat := 118140960795 + 2015155 * 2 ^ 59
def prefixEnd_2015155 : Nat := 4983230072969 + 3 ^ 40 * 2015155 * 2
def baseEnd_2015155 : Nat := 689828738874112286996651

theorem tailTrace_2015155 : CollatzResearch.WordTrace tailWord_2015155 prefixEnd_2015155 689828738874112286996651 := by
  unfold tailWord_2015155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498741014445070919046919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48999160676296713946031279 73498741014445070919046919)
  ·
    refine ⟨110248111521667606378570379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73498741014445070919046919 110248111521667606378570379)
    ·
      refine ⟨165372167282501409567855569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110248111521667606378570379 165372167282501409567855569)
      ·
        refine ⟨124029125461876057175891677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165372167282501409567855569 124029125461876057175891677)
        ·
          refine ⟨46510922048203521440959379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124029125461876057175891677 46510922048203521440959379)
          ·
            refine ⟨69766383072305282161439069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46510922048203521440959379 69766383072305282161439069)
            ·
              refine ⟨26162393652114480810539651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69766383072305282161439069 26162393652114480810539651)
              ·
                refine ⟨39243590478171721215809477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26162393652114480810539651 39243590478171721215809477)
                ·
                  refine ⟨7358173214657197727964277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39243590478171721215809477 7358173214657197727964277)
                  ·
                    refine ⟨689828738874112286996651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7358173214657197727964277 689828738874112286996651)
                    ·
                      rfl

theorem cell22_2015155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_2015155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015155 prefixEnd_2015155 := by exact prefixLift 2015155
  have htrace : WordTrace (prefixWord ++ tailWord_2015155) baseStart_2015155 baseEnd_2015155 := by
    simpa [prefixWord, tailWord_2015155, baseEnd_2015155] using wordTrace_append hprefix tailTrace_2015155
  have hstable : (prefixWord ++ tailWord_2015155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015155).length < 2 ^ (prefixWord ++ tailWord_2015155).sum := by decide
  have hdescent : baseEnd_2015155 < baseStart_2015155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015157 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2015157 : Nat := 118140960795 + 2015157 * 2 ^ 59
def prefixEnd_2015157 : Nat := 4983230072969 + 3 ^ 40 * 2015157 * 2
def baseEnd_2015157 : Nat := 229943141171661649482215

theorem tailTrace_2015157 : CollatzResearch.WordTrace tailWord_2015157 prefixEnd_2015157 229943141171661649482215 := by
  unfold tailWord_2015157
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498813960437825260619725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48999209306958550173746483 73498813960437825260619725)
  ·
    refine ⟨27562055235164184472732397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73498813960437825260619725 27562055235164184472732397)
    ·
      refine ⟨10335770713186569177274649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27562055235164184472732397 10335770713186569177274649)
      ·
        refine ⟨7751828034889926882955987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10335770713186569177274649 7751828034889926882955987)
        ·
          refine ⟨11627742052334890324433981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751828034889926882955987 11627742052334890324433981)
          ·
            refine ⟨4360403269625583871662743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11627742052334890324433981 4360403269625583871662743)
            ·
              refine ⟨6540604904438375807494115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360403269625583871662743 6540604904438375807494115)
              ·
                refine ⟨9810907356657563711241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540604904438375807494115 9810907356657563711241173)
                ·
                  refine ⟨229943141171661649482215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9810907356657563711241173 229943141171661649482215)
                  ·
                    rfl

theorem cell22_2015157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2015157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015157 prefixEnd_2015157 := by exact prefixLift 2015157
  have htrace : WordTrace (prefixWord ++ tailWord_2015157) baseStart_2015157 baseEnd_2015157 := by
    simpa [prefixWord, tailWord_2015157, baseEnd_2015157] using wordTrace_append hprefix tailTrace_2015157
  have hstable : (prefixWord ++ tailWord_2015157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015157).length < 2 ^ (prefixWord ++ tailWord_2015157).sum := by decide
  have hdescent : baseEnd_2015157 < baseStart_2015157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015185 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 8]
def baseStart_2015185 : Nat := 118140960795 + 2015185 * 2 ^ 59
def prefixEnd_2015185 : Nat := 4983230072969 + 3 ^ 40 * 2015185 * 2
def baseEnd_2015185 : Nat := 229946336162400736248853

theorem tailTrace_2015185 : CollatzResearch.WordTrace tailWord_2015185 prefixEnd_2015185 229946336162400736248853 := by
  unfold tailWord_2015185
  simp only [CollatzResearch.WordTrace]
  refine ⟨73499835204336386042639009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48999890136224257361759339 73499835204336386042639009)
  ·
    refine ⟨55124876403252289531979257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73499835204336386042639009 55124876403252289531979257)
    ·
      refine ⟨41343657302439217148984443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55124876403252289531979257 41343657302439217148984443)
      ·
        refine ⟨62015485953658825723476665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41343657302439217148984443 62015485953658825723476665)
        ·
          refine ⟨46511614465244119292607499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62015485953658825723476665 46511614465244119292607499)
          ·
            refine ⟨69767421697866178938911249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46511614465244119292607499 69767421697866178938911249)
            ·
              refine ⟨52325566273399634204183437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69767421697866178938911249 52325566273399634204183437)
              ·
                refine ⟨19622087352524862826568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52325566273399634204183437 19622087352524862826568789)
                ·
                  refine ⟨229946336162400736248853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19622087352524862826568789 229946336162400736248853)
                  ·
                    rfl

theorem cell22_2015185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_2015185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015185 prefixEnd_2015185 := by exact prefixLift 2015185
  have htrace : WordTrace (prefixWord ++ tailWord_2015185) baseStart_2015185 baseEnd_2015185 := by
    simpa [prefixWord, tailWord_2015185, baseEnd_2015185] using wordTrace_append hprefix tailTrace_2015185
  have hstable : (prefixWord ++ tailWord_2015185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015185).length < 2 ^ (prefixWord ++ tailWord_2015185).sum := by decide
  have hdescent : baseEnd_2015185 < baseStart_2015185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
